# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The generic host: one engine process per proof revision, each stream judged by the engine of the revision it named.

The host knows no layer's commands. For each revision in its map (a commit and a package: `revisions.py`) it starts the
engine only when a request needs it, reads the engine's description (`{"query":"describe"}`) and builds its request
handling from it: which commands the stream's proof has, the fresh ids each takes, and which field names the stream.
Every request carries the caller's `actor_id`: the token's principal, which the caller may also name, and which is
refused (`actor_id_must_match_the_token`) when it names another. An engine idle for `idle_timeout` seconds is stopped
(no process for an idle revision); its streams reload lazily.

Writes: every write for a stream goes to that stream's in-process `Owner`, which decides what its queue holds as one
batch against the stream's revision's engine and appends it with one compare-and-set (`Owner._process`): the protocol
of `attemptBatch` (gap_read_decide_append). Writers on different streams never wait for each other's appends.

A `stream.open` whose URL is not a revision URL is refused with the core's own rule, `revision_url_must_name_a_commit`,
read exactly as the core reads it (`revisions.parse_url`, Lean's `validRevisionUrl`): such a URL names no engine to
ask. What the host decides itself, outside the proofs, each named for the rule broken and documented where it happens: an
`actor_id` other than the caller's (`actor_id_must_match_the_token`), a command on a stream with no rows
(`stream_must_exist`: there is no proof to ask), a `stream.open` naming a revision with no engine here
(`revision_must_be_installed`), or naming another repository than that engine was built from
(`repository_must_match_the_engine`), or whose engine does not implement the stream interface
(`engine_must_implement_the_interface`, `interface.py`), a retry whose idempotency key was used for another request
(`idempotency_key_must_match_its_request`), and refusals of a request that cannot be built (`Malformed`).
"""
from __future__ import annotations
import collections, logging, random, threading, time
from concurrent.futures import Future, ThreadPoolExecutor, TimeoutError as FutureTimeout
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Set, Tuple, Union

from . import chain, ids, interface, wire
from .engine import Engine, EngineFailure, EngineRefusedLog
from .revisions import parse_url, revision_key, revision_of_url, same_repository, stamped_repo
from .schema import CommandSpec, SchemaError, commands_of
from .store import StreamStore, ask_until_answered, rows_hash

log = logging.getLogger("provenstream.service")

MAX_BATCH = 512
STREAM_FIELD = "stream_id"         # the param naming the stream of every command but stream.open (routed by it)


@dataclass
class Principal:
    """The caller: the principal its bearer token names, or the one an operator acts as in process (`host.Operator`)."""
    principal: str


@dataclass
class Accepted:
    event: Dict[str, Any]
    seq: int
    chain: Optional[str] = None      # the stream's head after this row, hex (chain.py)


@dataclass
class Rejected:
    reason: str


@dataclass
class Malformed:
    detail: str


@dataclass
class Undescribed(Malformed):
    """A well-formed command name the stream's revision does not describe: no such method there (`method_not_found`),
    rather than a malformed call of one that exists."""
    revision: str = ""


class Unavailable(Exception):
    """Nothing was stored for this request: the engine failed, the store failed before committing, or the stream was
    contended too long. Safe to retry with the same idempotency key."""


class OtherRevision(Unavailable):
    """The stream names a revision this host has no engine for: it is not judged here, by any engine."""

    def __init__(self, stream: str, revision: Optional[str]):
        self.stream, self.revision = stream, revision
        super().__init__("stream %s is judged by revision %s, which this host has no engine for" % (stream, revision))


class RevisionMismatch(Exception):
    """An engine reports another revision than the one it is listed under, or another description than before."""


class Judge:
    """One revision: the command that starts its engine, the process when one runs, its description, the streams the
    process holds (`synced`), the snapshots it re-folded and found right (`verified`), and its usage."""

    def __init__(self, key: str, command: List[str]):
        self.key, self.command = key, command
        self.engine = Engine(command=command)
        self.describe: Optional[dict] = None
        self.commands: Dict[str, CommandSpec] = {}
        self.synced: "collections.OrderedDict[str, int]" = collections.OrderedDict()
        self.verified: Set[Tuple[str, int]] = set()
        self.last_used = time.time()
        self.cpu_flushed = 0.0
        self.interface: Optional[str] = None       # unchecked; "" implemented; else why it is not the interface
        self.interface_lock = threading.Lock()


class Usage:
    """Counters per stream and per revision, kept in memory and added to the store's `usage` table after each batch
    (`flush`). `engine_ms` is an estimate (the wall time of engine calls for that stream or revision); `cpu_ms` is
    measured from the engine process (exact for reaped processes, sampled for running ones), per revision only."""

    def __init__(self) -> None:
        self.lock = threading.Lock()
        self.pending: Dict[Tuple[str, str], Dict[str, float]] = {}

    def add(self, scope: str, key: str, **deltas: float) -> None:
        with self.lock:
            d = self.pending.setdefault((scope, key), {})
            for k, v in deltas.items():
                d[k] = d.get(k, 0) + v

    def take(self) -> List[Tuple[str, str, dict]]:
        with self.lock:
            rows = [(s, k, d) for (s, k), d in self.pending.items()]
            self.pending = {}
        return rows


def same_request(a: dict, b: dict) -> bool:
    """Two requests are the same intent: the same actor and the same command (fresh ids are the host's)."""
    norm = lambda c: {k: v for k, v in c.items() if not (k == "meta" and v is None)}
    return a.get("actor_id") == b.get("actor_id") and norm(a.get("command", {})) == norm(b.get("command", {}))


def scoped_key(caller: Principal, key: str) -> str:
    """The stored form of a caller's idempotency key: scoped to the caller, so that one caller's key never answers, or
    conflicts with, another's (the same key from two callers is two writes). A key the host makes is `host:` and a fresh
    id instead. Rows stored before keys were scoped keep the key as it was sent; a retry of one now is a new write."""
    return "p:%s:%s" % (caller.principal, key)


@dataclass
class Item:
    caller: Principal
    request: dict
    key: str
    revision: str
    spec: CommandSpec
    future: Future = field(default_factory=Future)


class Owner:
    """The single in-process owner of one stream's writes: a queue, drained batch by batch on the worker pool (no
    thread of its own, so an idle stream costs nothing). It exists while it has work."""

    def __init__(self, service: "Service", stream: str):
        self.service, self.stream = service, stream
        self.queue: List[Item] = []
        self.cond = threading.Lock()
        self.scheduled = False
        self.alive = True

    def put(self, item: Item) -> bool:
        with self.cond:
            if not self.alive:
                return False
            self.queue.append(item)
            if not self.scheduled:
                self.scheduled = True
                self.service.pool.submit(self._drain)
            return True

    def withdraw(self, item: Item) -> bool:
        with self.cond:
            if item in self.queue:
                self.queue.remove(item)
                return True
            return False

    def requeue(self, items: List[Item]) -> None:
        if items:
            with self.cond:
                self.queue[:0] = items

    def _drain(self) -> None:
        while True:
            with self.service.owners_lock, self.cond:
                if not self.queue:
                    self.scheduled = False
                    self.alive = False
                    if self.service.owners.get(self.stream) is self:
                        del self.service.owners[self.stream]
                    return
                m = self.service.max_batch
                batch, self.queue = self.queue[:m], self.queue[m:]
            try:
                self._process(batch)
            except BaseException as x:                   # never leave a caller waiting
                log.exception("owner %s: batch failed", self.stream)
                for it in batch:
                    if not it.future.done():
                        it.future.set_exception(Unavailable("batch failed: %s" % x))

    def _answer_idempotent(self, items: List[Item]) -> List[Item]:
        """A key already stored: the same request gets the stored answer, a different one
        `idempotency_key_must_match_its_request`."""
        rest = []
        for it in items:
            stored = self.service.store.find_idem(it.key)
            if stored is None:
                rest.append(it)
                continue
            stream, seq, req, ev = stored
            if same_request(wire.loads(req), it.request):
                it.future.set_result(Accepted(wire.loads(ev), seq, self.service.chain_at(stream, seq).hex()))
            else:
                it.future.set_result(Rejected("idempotency_key_must_match_its_request"))
        return rest

    def _stored_at(self, key: str) -> Optional[Tuple[str, int]]:
        found = ask_until_answered(lambda: self.service.store.find_idem(key), BaseException)
        return (found[0], found[1]) if found else None

    def _process(self, batch: List[Item]) -> None:
        svc, s = self.service, self.stream
        pending = list(batch)
        for attempt in range(svc.retries):
            pending = self._answer_idempotent(pending)
            if not pending:
                return
            leaders: List[Item] = []
            followers: Dict[int, List[Item]] = {}
            for it in pending:                           # the same key twice in one batch: the later waits
                first = next((l for l in leaders if l.key == it.key), None)
                if first is None:
                    leaders.append(it)
                else:
                    followers.setdefault(id(first), []).append(it)
            judge = svc.judges[leaders[0].revision]
            t0 = time.time()
            try:
                with svc.engine_lock:
                    svc._ensure_engine(judge)
                    n = svc._sync(judge, s)
                    answers = [judge.engine.decide(it.request) for it in leaders]
                    svc.inflight.add(s)
            except (EngineFailure, Unavailable) as x:
                svc._forget(s)
                for it in pending:
                    it.future.set_exception(x if isinstance(x, Unavailable) else Unavailable(str(x)))
                return
            engine_ms = (time.time() - t0) * 1000
            try:
                head = svc._head(s, n)
                rows, results, pos, nbytes = [], [], n, 0
                for it, a in zip(leaders, answers):
                    if "error" in a:
                        results.append(Malformed(a["detail"]))
                        continue
                    if a["stream_id"] != s or a["at"] != pos:                                      # tripwire
                        svc._kill_engine(judge, "engine decided on %r at %r, host expected %r at %r"
                                         % (a["stream_id"], a["at"], s, pos))
                        for p in pending:
                            p.future.set_exception(Unavailable(judge.engine.failed or "engine killed"))
                        return
                    if a["accept"]:
                        svc._tripwire(judge, it, a["event"])
                        salt = chain.new_salt()
                        r, e, _ = chain.redact(it.request, a["event"], salt)
                        head = chain.link(head, pos, r, e)
                        rows.append((it.request, a["event"], it.key, salt, head))
                        nbytes += len(wire.dumps(it.request).encode()) + len(wire.dumps(a["event"]).encode())
                        results.append(Accepted(a["event"], pos, head.hex()))
                        pos += 1
                    else:
                        results.append(Rejected(a["reason"]))
                try:
                    committed = svc.store.append_batch(s, n, rows)                              # one CAS per batch
                except BaseException as x:
                    if rows and all(self._stored_at(key) == (s, n + i) for i, (_, _, key) in enumerate(rows)):
                        committed = True
                        log.warning("owner %s: append reported %r but our batch is stored", s, x)
                    else:
                        svc._forget(s)
                        for it in pending:
                            it.future.set_exception(Unavailable("store: %s" % x))
                        return
                if committed:
                    svc._committed(judge, s, n + len(rows))
                    with svc.heads_lock:
                        svc.heads[s] = (n + len(rows), head)
                    acc = sum(1 for r in results if isinstance(r, Accepted))
                    for scope, key in (("stream", s), ("revision", judge.key)):
                        svc.usage.add(scope, key, received=len(leaders), accepted=acc, events=len(rows),
                                      bytes=nbytes, engine_ms=engine_ms)
                    again = []
                    for it, res in zip(leaders, results):
                        it.future.set_result(res)
                        for f in followers.get(id(it), []):
                            if not isinstance(res, Accepted):
                                again.append(f)
                            else:
                                f.future.set_result(res if same_request(it.request, f.request)
                                                    else Rejected("idempotency_key_must_match_its_request"))
                    self.requeue(again)
                    svc._flush_usage()
                    if rows:
                        svc._maybe_snapshot(judge, s, n + len(rows))
                    return
                svc._forget(s)                                       # another writer appended first: decide again
                time.sleep(random.uniform(0, min(0.05, 0.0005 * (2 ** attempt))))
            finally:
                svc._settle(s)
        for it in pending:
            it.future.set_exception(Unavailable("stream %s: %d compare-and-set conflicts in a row" % (s, svc.retries)))


class Service:
    """The host's service over a store and a revision map `{revision key: engine command}`."""

    def __init__(self, store: StreamStore, engines: Dict[str, List[str]], max_streams: int = 10000,
                 snapshot_every: int = 1000, workers: int = 32, idle_timeout: float = 300.0):
        self.store = store
        self.judges: Dict[str, Judge] = {r: Judge(r, list(c)) for r, c in engines.items()}
        self.stream_rev: Dict[str, str] = {}
        self.engine_lock = threading.Condition(threading.RLock())
        self.inflight: Set[str] = set()
        self.owners: Dict[str, Owner] = {}
        self.owners_lock = threading.Lock()
        self.pool = ThreadPoolExecutor(max_workers=workers, thread_name_prefix="owner")
        self.usage = Usage()
        self.heads: Dict[str, Tuple[int, bytes]] = {}     # stream -> (length, head after its last row)
        self.heads_lock = threading.Lock()
        self.mint = ids.uuid7
        self.retries = 16
        self.max_batch = MAX_BATCH
        self.snapshot_every = snapshot_every
        self.max_streams = max_streams
        self.idle_timeout = idle_timeout
        self._stop = threading.Event()
        self._reaper = threading.Thread(target=self._reap_loop, daemon=True, name="engine-reaper")
        self._reaper.start()

    def close(self) -> None:
        self._stop.set()
        self.pool.shutdown(wait=True)
        with self.engine_lock:
            for j in self.judges.values():
                j.engine.stop()
        self._flush_usage(cpu=True)

    # -- engines: started lazily, described, stopped when idle ---------------------------------------------------------

    def _ensure_engine(self, judge: Judge) -> None:
        """Start `judge`'s engine if it is not running, and check what it says of itself: the revision it is listed
        under (its commit and its package), and the same description as before (an engine's description never
        changes)."""
        judge.last_used = time.time()
        if judge.engine.alive():
            return
        judge.synced.clear()
        try:
            judge.engine.start()
            d = judge.engine.describe()
        except EngineFailure as x:
            raise Unavailable(str(x)) from x
        reported = revision_key(d.get("revision") or "", d.get("package") or "") \
            if isinstance(d.get("revision"), str) and isinstance(d.get("package", ""), str) else None
        if reported != judge.key:
            judge.engine._kill("the engine listed under %s reports revision %r, package %r"
                               % (judge.key, d.get("revision"), d.get("package")))
            raise Unavailable("revision mismatch: %s" % judge.engine.failed)
        if judge.describe is not None and d["schema"] != judge.describe["schema"]:
            judge.engine._kill("the engine of %s describes other commands than before" % judge.key)
            raise Unavailable(judge.engine.failed or "description changed")
        try:
            judge.commands = commands_of(d)
        except SchemaError as x:
            judge.engine._kill("the engine of %s does not describe itself: %s" % (judge.key, x))
            raise Unavailable(str(x)) from x
        judge.describe = d

    def commands(self, revision: str) -> Dict[str, CommandSpec]:
        """The command table of a revision, from its engine's description (starting the engine if never described)."""
        judge = self.judges[revision]
        if judge.describe is None:
            with self.engine_lock:
                self._ensure_engine(judge)
        return judge.commands

    def describe(self, revision: str) -> dict:
        self.commands(revision)
        return self.judges[revision].describe

    def implements_interface(self, revision: str) -> bool:
        """The engine of `revision` implements the stream interface (`interface.py`): checked once per host process, in
        engine processes of its own (the serving engine never holds the recorded streams). No stream opens on one that
        does not, whatever its proof proves. An engine that does not start is `Unavailable`, checked again next time."""
        judge = self.judges[revision]
        with judge.interface_lock:
            if judge.interface is None:
                try:
                    interface.check(judge.command)
                    judge.interface = ""
                except interface.InterfaceMismatch as x:
                    judge.interface = str(x) or "mismatch"
                    log.warning("revision %s: not the stream interface: %s", revision, judge.interface)
                except EngineFailure as x:
                    raise Unavailable(str(x)) from x
        return judge.interface == ""

    def running(self) -> Dict[str, bool]:
        return {r: j.engine.alive() for r, j in self.judges.items()}

    def _reap_loop(self) -> None:
        while not self._stop.wait(min(1.0, max(0.05, self.idle_timeout / 4))):
            self.reap_idle()

    def reap_idle(self) -> List[str]:
        """Stop every engine idle for `idle_timeout` seconds with nothing in flight; answer their revisions."""
        stopped = []
        with self.engine_lock:
            if self.inflight:
                return stopped
            now = time.time()
            for j in self.judges.values():
                if j.engine.proc is not None and now - j.last_used >= self.idle_timeout:
                    j.engine.stop()
                    j.synced.clear()
                    stopped.append(j.key)
        if stopped:
            self._flush_usage(cpu=True)
        return stopped

    def _kill_engine(self, judge: Judge, why: str) -> None:
        with self.engine_lock:
            judge.engine._kill(why)
            judge.synced.clear()

    def _flush_usage(self, cpu: bool = False) -> None:
        if cpu:
            for j in self.judges.values():
                c = j.engine.cpu_seconds()
                if c > j.cpu_flushed:
                    self.usage.add("revision", j.key, cpu_ms=(c - j.cpu_flushed) * 1000)
                    j.cpu_flushed = c
        try:
            self.store.bump_usage(self.usage.take())
        except Exception:
            log.exception("usage: could not be stored (counters are best effort)")

    # -- which engine judges a stream ---------------------------------------------------------------------------------

    def revision_of_stream(self, stream: str) -> Optional[str]:
        """The revision stream `stream`'s opening names (None if it has no rows); raises `OtherRevision` when no engine
        here was built from it."""
        key = self.stream_rev.get(stream)
        if key is None:
            row = self.store.first(stream)
            if row is None:
                return None
            key = revision_of_url(wire.loads(row[2]).get("proof_revision_url"))
            if key not in self.judges:
                raise OtherRevision(stream, key)
            if len(self.stream_rev) >= 8 * self.max_streams:
                self.stream_rev.clear()
            self.stream_rev[stream] = key
        return key

    # -- the engine's view of a stream (all under engine_lock) ----------------------------------------------------------

    def _head(self, stream: str, length: int) -> bytes:
        """The stream's head after its first `length` rows: kept in memory, else read from the store (the last row's
        stored head; legacy rows' contributions computed, chain.py)."""
        with self.heads_lock:
            got = self.heads.get(stream)
        if got is not None and got[0] == length:
            return got[1]
        if length == 0:
            return chain.genesis(stream)
        return self.chain_at(stream, length - 1)

    def chain_at(self, stream: str, seq: int) -> bytes:
        """The head after row `seq`: its stored head, or for a legacy row the head computed from the rows before."""
        last = self.store.read_chained(stream, seq)[:1]
        if last and last[0][0] == seq and last[0][4] is not None:
            return last[0][4]
        return self.walk(stream, self.store.read_chained(stream)[:seq + 1])[-1]

    @staticmethod
    def walk(stream: str, rows, start: Optional[bytes] = None) -> List[bytes]:
        """The head after each stored row: a stored head where there is one, computed (empty salt) for legacy rows.
        `rows` start at row 0, or `start` is the head before their first row (a page read from a cursor)."""
        h, out = chain.genesis(stream) if start is None else start, []
        for seq, req, ev, salt, ch in rows:
            if ch is not None:
                h = ch
            else:
                r, e, _ = chain.redact(wire.loads(req), wire.loads(ev), salt)
                h = chain.link(h, seq, r, e)
            out.append(h)
        return out

    def head(self, stream: str) -> Tuple[int, Optional[bytes]]:
        """`(length, head)` of a stream as stored (head None for a stream with no rows)."""
        last = self.store.last_chained(stream)
        if last is None:
            return 0, None
        if last[4] is not None:
            return last[0] + 1, last[4]
        return last[0] + 1, self.walk(stream, self.store.read_chained(stream))[-1]

    def _forget(self, stream: str) -> None:
        with self.heads_lock:
            self.heads.pop(stream, None)
        with self.engine_lock:
            for j in self.judges.values():
                if j.synced.pop(stream, None) is not None and j.engine.alive():
                    try:
                        j.engine.drop(stream)
                    except EngineFailure:
                        pass

    def _settle(self, stream: str) -> None:
        with self.engine_lock:
            self.inflight.discard(stream)
            self.engine_lock.notify_all()

    def _committed(self, judge: Judge, stream: str, length: int) -> None:
        with self.engine_lock:
            if stream in judge.synced:
                judge.synced[stream] = length

    def _evict(self, judge: Judge) -> None:
        """Keep at most `max_streams` streams in an engine: the least recently used are dropped (they reload)."""
        while len(judge.synced) > self.max_streams:
            old, _ = judge.synced.popitem(last=False)
            judge.engine.drop(old)

    def _engine_sync(self, judge: Judge, stream: str, have: int, rows) -> int:
        try:
            return judge.engine.sync(stream, have, rows)
        except EngineRefusedLog as x:
            raise Unavailable("stream %s does not replay: %s" % (stream, x)) from x

    def _sync(self, judge: Judge, stream: str) -> int:
        """Bring `judge`'s engine's state of `stream` up to the store's; answer the length it holds."""
        if stream in judge.synced:
            judge.synced.move_to_end(stream)
            have = judge.synced[stream]
            rows = self.store.read(stream, have)
            if rows:
                have = self._engine_sync(judge, stream, have, rows)
                judge.synced[stream] = have
            return have
        have = self._first_load(judge, stream)
        judge.synced[stream] = have
        self._evict(judge)
        return have

    def _first_load(self, judge: Judge, stream: str) -> int:
        """Load `stream`: from a snapshot this process re-folded and found right and the rows after it, else by folding
        every row, comparing each stored snapshot of this revision on the way (a wrong one is deleted)."""
        snap = self.store.latest_snapshot(stream, judge.key)
        rows = self.store.read(stream)
        judge.engine.drop(stream)
        if snap is not None and (stream, snap[0]) in judge.verified:
            k, state, prefix_hash = snap
            if rows and rows_hash(rows[:k]) == prefix_hash:
                judge.engine.load(stream, k, state)
                return self._engine_sync(judge, stream, k, rows[k:]) if rows[k:] else k
        if not rows:
            return 0
        have = 0
        for k, state, prefix_hash in self.store.snapshots(stream, judge.key):
            if k > len(rows):
                continue
            if k > have:
                have = self._engine_sync(judge, stream, have, rows[have:k])
            got = judge.engine.snapshot(stream)
            if got["k"] == k and got["state"] == state and rows_hash(rows[:k]) == prefix_hash:
                judge.verified.add((stream, k))
            else:
                log.error("stream %s: the snapshot at %d is not the fold of its rows: deleted", stream, k)
                self.store.delete_snapshot(stream, k)
        if have < len(rows):
            have = self._engine_sync(judge, stream, have, rows[have:])
        return have

    def _maybe_snapshot(self, judge: Judge, stream: str, length: int) -> None:
        if not self.snapshot_every or length % self.snapshot_every:
            return
        try:
            with self.engine_lock:
                snap = judge.engine.snapshot(stream)
            if snap["k"] == length:
                self.store.put_snapshot(stream, length, snap["state"], judge.key)
                judge.verified.add((stream, length))
        except Exception:
            log.exception("stream %s: snapshot at %d failed (the batch is stored and was answered)", stream, length)

    def _tripwire(self, judge: Judge, it: Item, event: Dict[str, Any]) -> None:
        """The engine's event agrees with two proved facts (`toEvent_actor`, `toEvent_minted`) and with the command it
        was asked, or the engine is killed and nothing is stored."""
        minted = [event.get(m) for m in it.spec.minted]
        ok = (event.get("event") == it.spec.event and event.get("actor_id") == it.caller.principal
              and minted == it.request["fresh"])
        if not ok:
            self._kill_engine(judge, "tripwire: the engine's event contradicts toEvent_actor/toEvent_minted: %r" % (event,))
            raise Unavailable(judge.engine.failed or "engine killed")

    # -- writes ---------------------------------------------------------------------------------------------------------

    def _owner(self, stream: str) -> Owner:
        with self.owners_lock:
            o = self.owners.get(stream)
            if o is None or not o.alive:
                o = self.owners[stream] = Owner(self, stream)
            return o

    def prepare(self, caller: Principal, command: str, params: Dict[str, Any]
                ) -> Union[Tuple[str, str, CommandSpec, dict, Optional[str]], Rejected, Malformed]:
        """Build the request for one write from the stream's revision's description: the actor, the route, the minted
        ids. Answers `(stream, revision, spec, request, idempotency key)` or why it cannot be built."""
        if not isinstance(params, dict):
            return Malformed("params: expected an object")
        params = dict(params)
        key = params.pop("idempotency_key", None)
        if key is not None and not (isinstance(key, str) and 1 <= len(key) <= 200):
            return Malformed("idempotency_key: expected a string of 1 to 200 characters")
        if "command" in params:
            return Malformed("params: unknown key command")
        if not self.store.known(caller.principal):
            return Malformed("caller: no principal %s was issued by this host" % caller.principal)
        if "actor_id" in params:                                # the caller may name itself, and only itself
            actor = params.pop("actor_id")
            if not (isinstance(actor, str) and ids.CANONICAL_ID.fullmatch(actor)):
                return Malformed("actor_id: expected a canonical lowercase UUID (the caller's principal_id)")
            if actor != caller.principal:
                return Rejected("actor_id_must_match_the_token")    # the host's: the token names the actor
        if command == "stream.open":
            url = params.get("proof_revision_url")
            if not isinstance(url, str) or "\x00" in url:
                return Malformed("proof_revision_url: expected a string without U+0000 (a revision URL)")
            named = parse_url(url)
            if named is None:                                           # the core's rule, applied before routing:
                return Rejected("revision_url_must_name_a_commit")      # a URL naming no revision names no engine
            revision = named.key
            if revision not in self.judges:
                return Rejected("revision_must_be_installed")          # the host's: no engine here was built from it
            if not self.implements_interface(revision):
                return Rejected("engine_must_implement_the_interface")  # the host's: its engine is not the interface
            built_from = stamped_repo(self.describe(revision), self.judges[revision].command)
            if built_from is None or not same_repository(named.repo, built_from):
                return Rejected("repository_must_match_the_engine")     # the host's: that engine was built from another
        else:
            stream = params.get(STREAM_FIELD)
            if not (isinstance(stream, str) and ids.CANONICAL_ID.fullmatch(stream)):
                return Malformed("%s: expected a canonical lowercase UUID" % STREAM_FIELD)
            revision = self.revision_of_stream(stream)
            if revision is None:
                return Rejected("stream_must_exist")                   # the host's: no stream, so no proof to ask
        spec = self.commands(revision).get(command)
        if spec is None:
            return Undescribed("the proof of revision %s has no command %s" % (revision, command), revision)
        fresh = [self.mint() for _ in range(spec.fresh)]
        stream = fresh[spec.minted.index(spec.stream)] if spec.stream in spec.minted else params.get(spec.stream)
        request = {"actor_id": caller.principal, "command": dict(params, command=command), "fresh": fresh}
        return stream, revision, spec, request, key

    def submit(self, caller: Principal, command: str, params: Dict[str, Any],
               timeout: float = 120.0) -> Union[Accepted, Rejected, Malformed]:
        """One write. Without an `idempotency_key` in `params`, the host makes one for this call."""
        prepared = self.prepare(caller, command, params)
        if not isinstance(prepared, tuple):
            return prepared
        stream, revision, spec, request, key = prepared
        item = Item(caller, request, scoped_key(caller, key) if key else "host:" + ids.uuid7(), revision, spec)
        while True:
            owner = self._owner(stream)
            if owner.put(item):
                break
        try:
            return item.future.result(timeout)
        except FutureTimeout:
            if owner.withdraw(item):
                raise Unavailable("timed out in the queue of stream %s: nothing stored" % stream)
            return item.future.result()

    # -- reads ----------------------------------------------------------------------------------------------------------

    def read_stream(self, stream: str) -> Any:
        """A read of one stream, answered by the engine of its revision. It waits for an in-flight batch, so it never
        shows an event that is not stored."""
        revision = self.revision_of_stream(stream)
        if revision is None:
            return {"error": "stream_must_exist"}
        judge = self.judges[revision]
        with self.engine_lock:
            while stream in self.inflight:
                self.engine_lock.wait()
            try:
                self._ensure_engine(judge)
                self._sync(judge, stream)
                return judge.engine.query({"query": "stream", "stream_id": stream})
            except EngineFailure as x:
                raise Unavailable(str(x)) from x

    def usage_report(self, scope: Optional[str] = None, key: Optional[str] = None) -> List[dict]:
        """The stored counters (after adding what is pending, and the engines' CPU so far)."""
        self._flush_usage(cpu=True)
        out = self.store.usage(scope, key)
        for row in out:
            if row["scope"] == "stream":
                row["bytes_stored"] = self.store.stored_bytes(row["key"])
        return out

    # -- replay: every stream through its revision's engine, from its first row -----------------------------------------

    def check_all(self, held: Optional[Dict[str, Dict[int, str]]] = None) -> Dict[str, Any]:
        """For every stream: recompute its meta commitments and hash chain from its rows (refusing at the first
        mismatch, and against the heads in `held`, {stream: {seq: hex}}); replay its rows through a fresh engine of its
        revision (`check`: `replayRows`, then `check`, the audit path); and compare every stored snapshot of that
        revision with the fold of its rows."""
        bad, other, n, snaps, bad_chains = [], [], 0, 0, []
        for s in self.store.streams():
            rows = [chain.Row(seq, wire.loads(req), wire.loads(ev), salt, ch)
                    for seq, req, ev, salt, ch in self.store.read_chained(s)]
            rep = chain.verify(s, rows, (held or {}).get(s))
            if not rep.ok:
                bad_chains.append({"stream": s, "detail": rep.detail})
                log.error("check: stream %s: chain: %s", s, rep.detail)
        for s in (held or {}):
            if not self.store.length(s):
                bad_chains.append({"stream": s, "detail": "heads are held for a stream with no rows"})
        checkers: Dict[str, Engine] = {}
        try:
            for s in self.store.streams():
                try:
                    key = self.revision_of_stream(s)
                except OtherRevision:
                    other.append(s)
                    continue
                checker = checkers.get(key)
                if checker is None:
                    checker = checkers[key] = Engine(command=self.judges[key].command)
                    checker.start()
                    if checker.revision_key() != key:
                        raise RevisionMismatch("the check's engine for %s reports another revision" % key)
                rows = self.store.read(s)
                n += len(rows)
                try:
                    checker.check(s, rows)
                    for k, state, prefix_hash in self.store.snapshots(s, key):
                        if rows_hash(rows[:k]) != prefix_hash or checker.check(s, rows[:k])["state"] != state:
                            raise EngineRefusedLog("snapshot at %d is not the fold of its rows" % k)
                        snaps += 1
                except EngineRefusedLog as x:
                    bad.append(s)
                    log.error("check: stream %s does not replay: %s", s, x)
        finally:
            for c in checkers.values():
                c.stop()
        return {"streams": len(self.store.streams()), "events": n, "snapshots": snaps, "bad_streams": bad,
                "other_revision": other, "bad_chains": bad_chains}
