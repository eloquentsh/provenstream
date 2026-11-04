# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The stored streams, their snapshots, the tokens and the usage counters beside them, in SQLite or Postgres.

`StreamStore` is the interface, with the SQL both stores share, and `host/tests/test_store.py` is the suite each must
pass. A store keys events by `(stream_id, seq)`; `append_batch` is `attemptBatch`'s compare-and-set (Service.lean;
`cas_refines_run`): an append at length `n` commits exactly when the stream has `n` rows (gap_store_compare_and_set).
Events are append-only (a trigger refuses UPDATE and DELETE). A principal is an id and its tokens, nothing more: no
kind, no role, no account.

`SqliteStore` (store_sqlite.py, the standard library only) is the default: one file, one host. `PostgresStore` is for a
database shared by several hosts, and needs the `postgres` extra (`pip install provenstream[postgres]`). `open_store`
picks one by the target's form. `export` and `import_export` move every stream from one store to another, chains
checked.

The event index (`event_index`) is what `revision.events` reads: every stored event has one row, at a position `pos`
in the host's append order, with its stream's revision (the key its row 0's `proof_revision_url` names; "" when it
names none) and its event name. The index is written in the same transaction as the events it indexes
(`append_batch`, `import_export`), so it is exactly as complete as the events table, and a database from before the
index is backfilled once at open (`_backfill_index`, idempotent: it indexes what the index lacks). Positions are
assigned under the writers' serialisation (SQLite's `BEGIN IMMEDIATE`; on Postgres an advisory transaction lock,
`_lock_index`), so an event committed later always has a higher position: a reader that polls from the last position
it saw never misses one. The index is derived data, never read to verify anything: `provenstream verify` reads the
events.
"""
from __future__ import annotations
import hashlib, logging, os, secrets, threading, time
from typing import Any, Callable, Dict, Iterable, List, Optional, Sequence, Tuple, TypeVar

from . import chain, ids, wire
from .revisions import revision_of_url

log = logging.getLogger("provenstream.store")

T = TypeVar("T")
Row = Tuple[int, str, str]                      # (seq, request JSON, event JSON)
NewRow = Tuple[dict, dict, str, Optional[bytes], Optional[bytes]]   # (request, event, key, meta salt, chain head)
ChainedRow = Tuple[int, str, str, Optional[bytes], Optional[bytes]]  # (seq, request, event, meta salt, chain head)


def hash_token(token: str) -> str:
    return hashlib.sha256(token.encode("utf-8", "surrogatepass")).hexdigest()


def new_token() -> str:
    return "ps_" + secrets.token_urlsafe(32)


def now() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def ask_until_answered(ask: Callable[[], T], catch=Exception,
                       failed: Callable[[BaseException, float], None] = lambda x, delay: None) -> T:
    """`ask()`, again after each failure (`failed` is told, then a backoff from 0.05 s doubling to 5 s), until it
    answers."""
    delay = 0.05
    while True:
        try:
            return ask()
        except catch as x:
            failed(x, delay)
        time.sleep(delay)
        delay = min(delay * 2, 5.0)


def _insert_token(ex, principal: str, token: str) -> None:
    ex("INSERT INTO tokens (token_hash, principal, issued_at) VALUES (%s, %s, %s)", (hash_token(token), principal, now()))


INDEX_CHUNK = 5000                       # rows per round of a backfill


def _event_dict(ev: Any) -> Any:
    """An event as stored (JSON text) or as given (a dict), read."""
    if isinstance(ev, str):
        try:
            return wire.loads(ev)
        except wire.BadJson:
            return None
    return ev


def rows_hash(rows: Sequence[Row]) -> str:
    """SHA-256 over a stream's first k rows, as stored: what a snapshot says it is the fold of."""
    h = hashlib.sha256()
    for seq, req, ev in rows:
        h.update(b"%d\x1f" % seq + req.encode("utf-8") + b"\x1f" + ev.encode("utf-8") + b"\x1e")
    return h.hexdigest()


class StreamStore:
    """The interface. The SQL here is shared by both stores, written with `%s` placeholders (SqliteStore translates
    them) and in the dialect both speak (`ON CONFLICT` needs SQLite 3.24 or later)."""

    OCTETS = "octet_length(%s)"          # the bytes of a text column, as UTF-8

    # -- backend hooks ------------------------------------------------------------------------------------------------

    def _exec(self, sql: str, args: Sequence[Any] = ()) -> List[tuple]:
        raise NotImplementedError

    def _tx(self, body) -> Any:
        """Run `body(exec)` in one transaction; roll back if it raises."""
        raise NotImplementedError

    def _unique_violation(self, x: BaseException) -> bool:
        raise NotImplementedError

    def close(self) -> None:
        raise NotImplementedError

    def _before_commit(self) -> None:
        """A seam for tests: fail after a batch's rows are written and before they commit."""

    def _after_commit(self) -> None:
        """A seam for tests: fail after a batch committed, as a lost connection would."""

    # -- the event index (the module's docstring says what it holds) --------------------------------------------------

    ORDER_OF_APPEND = "e.accepted_at, e.stream_id, e.seq"   # a backfill's order: the time (to the second), then the
                                                            # stream and seq; SqliteStore's rowid is exact

    def _lock_index(self, ex) -> None:
        """Serialise index writers of other connections for the rest of this transaction (Postgres; SQLite's
        `BEGIN IMMEDIATE` already holds the file's write lock)."""

    def _stream_revision(self, ex, stream: str) -> str:
        """The revision of a stream with rows: from its row 0 in the index, else from its stored row 0."""
        r = ex("SELECT revision FROM event_index WHERE stream_id = %s AND seq = 0", (stream,))
        if r:
            return r[0][0]
        r = ex("SELECT event FROM events WHERE stream_id = %s AND seq = 0", (stream,))
        ev = _event_dict(r[0][0]) if r else None
        return (revision_of_url(ev.get("proof_revision_url")) if isinstance(ev, dict) else None) or ""

    def _index(self, ex, rows: Sequence[Tuple[str, int, Any]], revisions: Dict[str, str]) -> None:
        """Index `rows` (`(stream, seq, event)`, the event a dict or its JSON text, in append order) at the positions
        after the last one taken, inside the caller's transaction: one row each, its stream's revision and its event
        name. `revisions` caches each stream's revision across calls; a stream it lacks is read from its row 0 (the row
        itself when `seq` is 0)."""
        if not rows:
            return
        self._lock_index(ex)
        base = ex("SELECT coalesce(max(pos), 0) FROM event_index")[0][0]
        for i, (s, seq, ev) in enumerate(rows):
            ev = _event_dict(ev)
            if s not in revisions:
                if seq == 0:
                    url = ev.get("proof_revision_url") if isinstance(ev, dict) else None
                    revisions[s] = revision_of_url(url) or ""
                else:
                    revisions[s] = self._stream_revision(ex, s)
            name = ev.get("event") if isinstance(ev, dict) and isinstance(ev.get("event"), str) else ""
            pos = base + 1 + i
            ex("INSERT INTO event_index (pos, revision, stream_id, seq, name) VALUES (%s, %s, %s, %s, %s)",
               (pos, revisions[s], s, seq, name))

    def _backfill_index(self) -> int:
        """Index every stored event the index lacks (a database from before the index: once; afterwards nothing), in
        the order they were appended as well as this store knows it (`ORDER_OF_APPEND`), in one transaction; answers how
        many were indexed. Idempotent: run at every open."""
        def body(ex):
            n, revisions = 0, {}
            while True:
                missing = ex("SELECT e.stream_id, e.seq, e.event FROM events e LEFT JOIN event_index i "
                             "ON i.stream_id = e.stream_id AND i.seq = e.seq WHERE i.pos IS NULL ORDER BY %s LIMIT %d"
                             % (self.ORDER_OF_APPEND, INDEX_CHUNK))
                if not missing:
                    return n
                self._index(ex, [tuple(r) for r in missing], revisions)
                n += len(missing)
        n = self._tx(body)
        if n:
            log.info("event index: %d stored events indexed", n)
        return n

    def find_events(self, revision: str, name: Optional[str] = None, after: int = 0,
                    limit: int = 1000) -> List[Tuple[int, str, int, str, Optional[bytes]]]:
        """The indexed events of `revision` after position `after`, in append order, at most `limit`, those named
        `name` when it is given: `(pos, stream_id, seq, event JSON, chain head)` each. One walk of the index in position
        order from `after` (on `(revision, pos)`, or `(revision, name, pos)`); the events table is joined by primary
        key for the rows answered alone."""
        sql = ["SELECT i.pos, i.stream_id, i.seq, e.event, e.chain FROM event_index i",
               "JOIN events e ON e.stream_id = i.stream_id AND e.seq = i.seq WHERE i.revision = %s AND i.pos > %s"]
        args: List[Any] = [revision, after]
        if name is not None:
            sql.append("AND i.name = %s")
            args.append(name)
        sql.append("ORDER BY i.pos LIMIT %s")
        args.append(limit)
        return [(pos, s, seq, ev, bytes(ch) if ch is not None else None)
                for pos, s, seq, ev, ch in self._exec(" ".join(sql), args)]

    # -- streams ------------------------------------------------------------------------------------------------------

    def read(self, stream: str, from_seq: int = 0) -> List[Row]:
        return [tuple(r) for r in self._exec(
            "SELECT seq, request, event FROM events WHERE stream_id = %s AND seq >= %s ORDER BY seq", (stream, from_seq))]

    def first(self, stream: str) -> Optional[Row]:
        """The stream's row 0, its creation (which names its revision), or None if it has no rows."""
        r = self._exec("SELECT seq, request, event FROM events WHERE stream_id = %s AND seq = 0", (stream,))
        return tuple(r[0]) if r else None

    def length(self, stream: str) -> int:
        return self._exec("SELECT count(*) FROM events WHERE stream_id = %s", (stream,))[0][0]

    def streams(self) -> List[str]:
        return [r[0] for r in self._exec("SELECT stream_id FROM events WHERE seq = 0 ORDER BY accepted_at, stream_id")]

    def ping(self) -> None:
        """Raises unless the database answers (`/healthz`): one trivial statement, whatever the store holds."""
        self._exec("SELECT 1")

    def count(self) -> int:
        return self._exec("SELECT count(*) FROM events")[0][0]

    def events(self) -> List[dict]:
        out: List[dict] = []
        for s in self.streams():
            out += [wire.loads(e) for _, _, e in self.read(s)]
        return out

    def append_batch(self, stream: str, expected_len: int, rows: Sequence[NewRow]) -> bool:
        """Compare-and-set. Store `rows` at `expected_len, expected_len + 1, ...` of `stream` if and only
        if the stream has exactly `expected_len` rows; otherwise store nothing and answer False. Raises on any other
        failure, with nothing stored (unless the failure came after the commit: see `find_idem`)."""
        if not rows:
            return self.length(stream) == expected_len
        prepared = [(stream, expected_len + i, wire.dumps(r[0]), wire.dumps(r[1]), r[2], now(),
                     r[3] if len(r) > 3 else None, r[4] if len(r) > 4 else None) for i, r in enumerate(rows)]

        def body(ex):
            if ex("SELECT count(*) FROM events WHERE stream_id = %s", (stream,))[0][0] != expected_len:
                return False
            for p in prepared:
                ex("INSERT INTO events (stream_id, seq, request, event, idem, accepted_at, meta_salt, chain) "
                   "VALUES (%s, %s, %s, %s, %s, %s, %s, %s)", p)
            self._index(ex, [(stream, expected_len + i, r[1]) for i, r in enumerate(rows)], {})
            self._before_commit()
            return True
        try:
            ok = self._tx(body)
        except BaseException as x:
            if self._unique_violation(x):
                return False
            raise
        if ok:
            self._after_commit()
        return ok

    def append(self, stream: str, expected_len: int, request: dict, event: dict, idem: str) -> bool:
        return self.append_batch(stream, expected_len, [(request, event, idem)])

    def export(self, out_path: str) -> int:
        """Every row, stream by stream, written to a temporary file, fsynced and renamed into place; returns the number
        of rows. JSON lines: first the header `{"provenstream_export": 2}`, then one row per line, as `stream.rows`
        answers a row plus its stream, its idempotency key and when it was accepted: `{"stream_id", "seq", "request",
        "event", "meta_salt", "chain", "idem", "accepted_at"}`, the request and event as their stored JSON text, the
        salt and head in hex (null for a row written before the chain). `provenstream verify --rows` reads it as it is.
        Tokens, snapshots and usage counters are not exported: tokens are this host's credentials, snapshots are
        rebuilt from the rows, and the counters are this host's."""
        n, tmp = 0, out_path + ".tmp"
        hx = lambda b: bytes(b).hex() if b is not None else None
        with open(tmp, "w", encoding="utf-8") as f:
            f.write('{"provenstream_export":%d}\n' % EXPORT_VERSION)
            for s in self.streams():
                for seq, req, ev, salt, ch, idem, at in self._exec(
                        "SELECT seq, request, event, meta_salt, chain, idem, accepted_at FROM events WHERE stream_id = %s "
                        "ORDER BY seq", (s,)):
                    f.write(wire.dumps({"stream_id": s, "seq": seq, "request": req, "event": ev, "meta_salt": hx(salt),
                                        "chain": hx(ch), "idem": idem, "accepted_at": at}) + "\n")
                    n += 1
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, out_path)
        return n

    def import_export(self, path: str) -> Dict[str, int]:
        """Store the rows of an export (`export`) as they are, into a store holding none of its streams; answers
        {stream: rows}. Every stream's commitments and hash chain are recomputed from its rows and checked against the
        exported heads first (chain.py); any mismatch, gap or malformed line refuses the whole file (`ImportRefused`)
        and nothing is stored. Rows are written in one transaction, with their exported idempotency keys and times, so a
        retry after the move still gets its first answer. Tokens are not in an export: issue the principals' tokens
        again on the new store (`principal.create` with `principal_id`, by the operator)."""
        streams = read_export(path)
        rows = [(s, r["seq"], r["request"], r["event"], r["idem"] or "import:%s:%d" % (s, r["seq"]),
                 r["accepted_at"] or now(), r["meta_salt"], r["chain"])
                for s, rs in streams.items() for r in rs]

        def body(ex):
            for s in streams:
                if ex("SELECT count(*) FROM events WHERE stream_id = %s", (s,))[0][0]:
                    raise ImportRefused("stream %s already has rows here: an import never adds to a stream" % s)
            for r in rows:
                ex("INSERT INTO events (stream_id, seq, request, event, idem, accepted_at, meta_salt, chain) "
                   "VALUES (%s, %s, %s, %s, %s, %s, %s, %s)", r)
            # the index, in the order the rows were accepted as well as an export says it (its times, then the stream)
            order = sorted(((s, r["seq"], r["ev"], r["accepted_at"] or "") for s, rs in streams.items() for r in rs),
                           key=lambda t: (t[3], t[0], t[1]))
            self._index(ex, [(s, seq, ev) for s, seq, ev, _ in order], {})
        try:
            self._tx(body)
        except ImportRefused:
            raise
        except BaseException as x:
            if self._unique_violation(x):
                raise ImportRefused("an exported row's stream and seq, or its idempotency key, is stored here already: "
                                    "%s" % x) from x
            raise
        return {s: len(rs) for s, rs in streams.items()}

    def read_chained(self, stream: str, from_seq: int = 0, limit: Optional[int] = None) -> List[ChainedRow]:
        """Rows with their meta salt and chain head (both None for a row written before the chain); with `limit`, at
        most that many (a page of `stream.events` or `stream.rows`)."""
        out = []
        sql = "SELECT seq, request, event, meta_salt, chain FROM events WHERE stream_id = %s AND seq >= %s ORDER BY seq"
        args: List[Any] = [stream, from_seq]
        if limit is not None:
            sql += " LIMIT %s"; args.append(limit)
        for seq, req, ev, salt, ch in self._exec(sql, args):
            out.append((seq, req, ev, bytes(salt) if salt is not None else None, bytes(ch) if ch is not None else None))
        return out

    def last_chained(self, stream: str) -> Optional[ChainedRow]:
        r = self._exec("SELECT seq, request, event, meta_salt, chain FROM events WHERE stream_id = %s "
                       "ORDER BY seq DESC LIMIT 1", (stream,))
        if not r:
            return None
        seq, req, ev, salt, ch = r[0]
        return (seq, req, ev, bytes(salt) if salt is not None else None, bytes(ch) if ch is not None else None)

    def find_idem(self, key: str) -> Optional[Tuple[str, int, str, str]]:
        """The row stored under this idempotency key, if any: `(stream, seq, request JSON, event JSON)`. How a retry
        with the same key gets the original answer, and how a writer unsure whether its commit happened finds out."""
        r = self._exec("SELECT stream_id, seq, request, event FROM events WHERE idem = %s", (key,))
        return tuple(r[0]) if r else None

    # -- snapshots ------------------------------------------------------------------------------------------------

    def put_snapshot(self, stream: str, k: int, state: dict, revision: str = "") -> None:
        """A snapshot taken by the engine of `revision` (a snapshot is that engine's state: only it reads it back)."""
        prefix = self.read(stream)[:k]
        if len(prefix) != k:
            raise ValueError("stream %s has fewer than %d rows" % (stream, k))
        args = (stream, k, wire.dumps(state), rows_hash(prefix), now(), revision)
        self._tx(lambda ex: ex("INSERT INTO snapshots (stream_id, k, state, prefix_hash, taken_at, revision) VALUES (%s, %s, %s, %s, %s, %s) ON CONFLICT DO NOTHING", args))


    def snapshots(self, stream: str, revision: str = "") -> List[Tuple[int, dict, str]]:
        """The stream's snapshots taken by the engine of `revision` that decode (another revision's are not shown).
        One that does not decode cannot be the fold of anything: it is deleted and logged, and the stream loads from
        its rows."""
        rows = self._exec("SELECT k, state, prefix_hash FROM snapshots WHERE stream_id = %s AND revision = %s ORDER BY k",
                          (stream, revision))
        out: List[Tuple[int, dict, str]] = []
        for k, st, h in rows:
            try:
                state = wire.loads(st)
            except wire.BadJson as x:
                log.warning("stream %s: snapshot at %d does not decode (%s): deleted", stream, k, x)
                self.delete_snapshot(stream, k)
                continue
            if not isinstance(state, dict):
                log.warning("stream %s: snapshot at %d is not a state: deleted", stream, k)
                self.delete_snapshot(stream, k)
                continue
            out.append((k, state, h))
        return out

    def latest_snapshot(self, stream: str, revision: str = "") -> Optional[Tuple[int, dict, str]]:
        s = self.snapshots(stream, revision)
        return s[-1] if s else None

    def delete_snapshot(self, stream: str, k: int) -> None:
        """Snapshots are not the log: a snapshot found wrong is deleted."""
        self._tx(lambda ex: ex("DELETE FROM snapshots WHERE stream_id = %s AND k = %s", (stream, k)))

    # -- tokens -------------------------------------------------------------------------------------------------------

    # -- usage ----------------------------------------------------------------------------------------------------------

    def bump_usage(self, rows: Sequence[Tuple[str, str, dict]]) -> None:
        """Add counters: each row is `(scope, key, deltas)`, scope `stream` or `revision`; `deltas` may hold
        `received`, `accepted`, `events`, `bytes`, `engine_ms` (an estimate: wall time of engine calls) and `cpu_ms`
        (measured from the engine process); `last_active` is set to now."""
        if not rows:
            return
        t = now()

        def body(ex):
            for scope, key, d in rows:
                ex("INSERT INTO usage (scope, key, received, accepted, events, bytes, engine_ms, cpu_ms, last_active) "
                   "VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s) ON CONFLICT (scope, key) DO UPDATE SET "
                   "received = usage.received + EXCLUDED.received, accepted = usage.accepted + EXCLUDED.accepted, "
                   "events = usage.events + EXCLUDED.events, bytes = usage.bytes + EXCLUDED.bytes, "
                   "engine_ms = usage.engine_ms + EXCLUDED.engine_ms, cpu_ms = usage.cpu_ms + EXCLUDED.cpu_ms, "
                   "last_active = EXCLUDED.last_active",
                   (scope, key, d.get("received", 0), d.get("accepted", 0), d.get("events", 0), d.get("bytes", 0),
                    int(d.get("engine_ms", 0)), int(d.get("cpu_ms", 0)), t))
        self._tx(body)

    def usage(self, scope: Optional[str] = None, key: Optional[str] = None) -> List[dict]:
        sql, args = "SELECT scope, key, received, accepted, events, bytes, engine_ms, cpu_ms, last_active FROM usage", []
        if scope is not None:
            sql += " WHERE scope = %s"; args.append(scope)
            if key is not None:
                sql += " AND key = %s"; args.append(key)
        sql += " ORDER BY scope, key"
        cols = ("scope", "key", "received", "accepted", "events", "bytes", "engine_ms", "cpu_ms", "last_active")
        return [dict(zip(cols, r)) for r in self._exec(sql, args)]

    def stored_bytes(self, stream: str) -> int:
        """The bytes of a stream's stored requests and events, as stored (exact, from the table)."""
        r = self._exec("SELECT coalesce(sum(%s + %s), 0) FROM events WHERE stream_id = %%s"
                       % (self.OCTETS % "request", self.OCTETS % "event"), (stream,))
        return int(r[0][0])

    # -- tokens -----------------------------------------------------------------------------------------------------

    def principal_of(self, token: str) -> Optional[str]:
        r = self._exec("SELECT principal FROM tokens WHERE token_hash = %s AND revoked_at IS NULL",
                       (hash_token(token),))
        return r[0][0] if r else None

    def known(self, principal: str) -> bool:
        """This host has ever issued a token to `principal`."""
        return bool(self._exec("SELECT 1 FROM tokens WHERE principal = %s LIMIT 1", (principal,)))

    def _issue(self, body, token: str, principal: str) -> str:
        """Run a token transaction. One that met another's new token (`tokens_one_live`) runs again, and revokes it.
        Any other failure may hide a commit whose reply was lost (`_tx` waited until it is final), so the store is
        asked whether the new token works: it does, it is returned; it does not, the error stands and nothing changed."""
        for _ in range(20):
            try:
                self._tx(body)
                return token
            except BaseException as x:
                if self._unique_violation(x):
                    continue
                if ask_until_answered(lambda: self.principal_of(token)) == principal:
                    return token
                raise
        raise RuntimeError("token for %s: 20 conflicting rotations in a row" % principal)

    def create_principal(self, principal: str) -> str:
        """Issue `principal` (an id this store holds no token for) its first token."""
        token = new_token()

        def body(ex):
            if ex("SELECT 1 FROM tokens WHERE principal = %s", (principal,)):
                raise ValueError("principal %s already holds a token here" % principal)
            _insert_token(ex, principal, token)
        return self._issue(body, token, principal)

    def rotate(self, principal: str) -> str:
        token = new_token()

        def body(ex):
            ex("UPDATE tokens SET revoked_at = %s WHERE principal = %s AND revoked_at IS NULL", (now(), principal))
            _insert_token(ex, principal, token)
        return self._issue(body, token, principal)


# ---------------------------------------------------------------------------------------------------- export files

EXPORT_VERSION = 2
EXPORT_KEYS = {"stream_id", "seq", "request", "event", "meta_salt", "chain", "idem", "accepted_at"}


class ImportRefused(ValueError):
    """An export file that cannot be imported as it is: nothing was stored."""


def read_export(path: str) -> Dict[str, List[dict]]:
    """The rows of an export file by stream, in file order, each stream's commitments and chain recomputed and checked
    against its exported heads (`chain.verify`); raises `ImportRefused` naming the line or the stream and seq."""
    streams: Dict[str, List[dict]] = {}
    header = False
    with open(path, encoding="utf-8") as f:
        for n, line in enumerate(f, 1):
            if not line.strip():
                continue
            try:
                d = wire.loads(line)
            except wire.BadJson as x:
                raise ImportRefused("line %d: not JSON: %s" % (n, x)) from x
            if not header:
                if d != {"provenstream_export": EXPORT_VERSION}:
                    raise ImportRefused("line %d: not a provenstream export of version %d (the first line must be "
                                        '{"provenstream_export": %d})' % (n, EXPORT_VERSION, EXPORT_VERSION))
                header = True
                continue
            if not (isinstance(d, dict) and {"stream_id", "seq", "request", "event"} <= set(d) <= EXPORT_KEYS):
                raise ImportRefused("line %d: expected a row with the keys %s" % (n, ", ".join(sorted(EXPORT_KEYS))))
            s, seq = d["stream_id"], d["seq"]
            if not (isinstance(s, str) and ids.CANONICAL_ID.fullmatch(s) and isinstance(seq, int)
                    and not isinstance(seq, bool) and isinstance(d["request"], str) and isinstance(d["event"], str)
                    and all(isinstance(d.get(k), (str, type(None))) for k in ("meta_salt", "chain", "idem",
                                                                                "accepted_at"))):
                raise ImportRefused("line %d: a row's stream, seq, request, event, salt, chain, key or time has the "
                                    "wrong type" % n)
            try:
                req, ev = wire.loads(d["request"]), wire.loads(d["event"])
                salt = bytes.fromhex(d["meta_salt"]) if d.get("meta_salt") else None
                head = bytes.fromhex(d["chain"]) if d.get("chain") else None
            except (wire.BadJson, ValueError) as x:
                raise ImportRefused("line %d: %s" % (n, x)) from x
            streams.setdefault(s, []).append({"seq": seq, "request": d["request"], "event": d["event"], "req": req,
                                              "ev": ev, "meta_salt": salt, "chain": head, "idem": d.get("idem"),
                                              "accepted_at": d.get("accepted_at")})
    if not header:
        raise ImportRefused("%s is empty: not a provenstream export" % path)
    for s, rs in streams.items():
        if isinstance(rs[0]["ev"], dict) and rs[0]["ev"].get("stream_id", s) != s:
            raise ImportRefused("stream %s: its row 0 opens stream %r" % (s, rs[0]["ev"].get("stream_id")))
        rep = chain.verify(s, [chain.Row(r["seq"], r["req"], r["ev"], r["meta_salt"], r["chain"]) for r in rs])
        if not rep.ok:
            raise ImportRefused("stream %s: the chain does not recompute: %s" % (s, rep.detail))
    return streams


# --------------------------------------------------------------------------------------------------------- Postgres

PG_SCHEMA = [
    """CREATE TABLE IF NOT EXISTS events (
         stream_id TEXT NOT NULL, seq INTEGER NOT NULL, request TEXT NOT NULL, event TEXT NOT NULL,
         idem TEXT NOT NULL UNIQUE, accepted_at TEXT NOT NULL, PRIMARY KEY (stream_id, seq))""",
    """CREATE OR REPLACE FUNCTION events_append_only() RETURNS trigger AS $$
         BEGIN RAISE EXCEPTION 'events are append-only'; END; $$ LANGUAGE plpgsql""",
    """DO $$ BEGIN
         IF NOT EXISTS (SELECT 1 FROM pg_trigger WHERE tgname = 'events_append_only') THEN
           CREATE TRIGGER events_append_only BEFORE UPDATE OR DELETE ON events
             FOR EACH ROW EXECUTE FUNCTION events_append_only();
         END IF; END $$""",
    """CREATE TABLE IF NOT EXISTS snapshots (
         stream_id TEXT NOT NULL, k INTEGER NOT NULL, state TEXT NOT NULL, prefix_hash TEXT NOT NULL,
         taken_at TEXT NOT NULL, PRIMARY KEY (stream_id, k))""",
    # the revision of the engine that took the snapshot (a snapshot is that engine's state: only it reads it back)
    "ALTER TABLE snapshots ADD COLUMN IF NOT EXISTS revision TEXT NOT NULL DEFAULT ''",
    """CREATE TABLE IF NOT EXISTS tokens (
         token_hash TEXT PRIMARY KEY, principal TEXT NOT NULL, issued_at TEXT NOT NULL, revoked_at TEXT)""",
    "CREATE INDEX IF NOT EXISTS tokens_principal ON tokens (principal)",
    # the per-stream hash chain (chain.py): the row's meta salt and the head after it; NULL for rows written before
    "ALTER TABLE events ADD COLUMN IF NOT EXISTS meta_salt BYTEA",
    "ALTER TABLE events ADD COLUMN IF NOT EXISTS chain BYTEA",
    # a principal is an id and its tokens: no kind (stores from before kept one; it goes, with its checks)
    "DROP TRIGGER IF EXISTS tokens_kind_fixed ON tokens",
    "DROP FUNCTION IF EXISTS tokens_kind_fixed()",
    "ALTER TABLE tokens DROP COLUMN IF EXISTS kind",
    # one live token per principal: two rotations at once cannot both leave theirs live (the loser runs again)
    "CREATE UNIQUE INDEX IF NOT EXISTS tokens_one_live ON tokens (principal) WHERE revoked_at IS NULL",
    """CREATE TABLE IF NOT EXISTS usage (
         scope TEXT NOT NULL, key TEXT NOT NULL, received BIGINT NOT NULL DEFAULT 0, accepted BIGINT NOT NULL DEFAULT 0,
         events BIGINT NOT NULL DEFAULT 0, bytes BIGINT NOT NULL DEFAULT 0, engine_ms BIGINT NOT NULL DEFAULT 0,
         cpu_ms BIGINT NOT NULL DEFAULT 0, last_active TEXT NOT NULL, PRIMARY KEY (scope, key))""",
    # the event index (the module docstring): one row per event at its position in append order
    """CREATE TABLE IF NOT EXISTS event_index (
         pos BIGINT PRIMARY KEY, revision TEXT NOT NULL, stream_id TEXT NOT NULL, seq INTEGER NOT NULL,
         name TEXT NOT NULL, UNIQUE (stream_id, seq))""",
    "CREATE INDEX IF NOT EXISTS event_index_revision ON event_index (revision, pos)",
    "CREATE INDEX IF NOT EXISTS event_index_name ON event_index (revision, name, pos)",
    """DO $$ BEGIN
         IF NOT EXISTS (SELECT 1 FROM pg_trigger WHERE tgname = 'event_index_append_only') THEN
           CREATE TRIGGER event_index_append_only BEFORE UPDATE OR DELETE ON event_index
             FOR EACH ROW EXECUTE FUNCTION events_append_only();
         END IF; END $$""",
]


class PostgresStore(StreamStore):
    """A Postgres database shared by any number of servers. `dsn` is a libpq connection string."""

    INDEX_LOCK = 551002                  # the advisory lock index writers take (`_lock_index`), for their transaction

    def __init__(self, dsn: str):
        import psycopg
        self._psycopg = psycopg
        self.dsn = dsn
        self.lock = threading.RLock()
        self.conn = self._connect()
        with self.lock:
            # concurrent first-time schema creation by several servers: serialise it
            self.conn.execute("SELECT pg_advisory_lock(551001)")
            try:
                for stmt in PG_SCHEMA:
                    self.conn.execute(stmt)
                self._backfill_index()
            finally:
                self.conn.execute("SELECT pg_advisory_unlock(551001)")

    def _connect(self):
        conn = self._psycopg.connect(self.dsn, autocommit=True)
        conn.execute("SET client_encoding TO 'UTF8'")          # text, not bytes, whatever the database's encoding
        return conn

    def _live(self):
        """The connection, replaced if a restart or a dropped link closed it: the call that found it broken failed
        (nothing stored), the next one reconnects."""
        if self.conn.closed or self.conn.broken:
            self.conn = self._connect()
        return self.conn

    def close(self) -> None:
        with self.lock:
            self.conn.close()

    def _exec(self, sql, args=()):
        with self.lock:
            cur = self._live().execute(sql, args)
            return cur.fetchall() if cur.description else []

    def _tx(self, body):
        """Run `body(exec)` in one transaction. When the connection broke after COMMIT was sent, this waits until the
        session that sent it can no longer commit (`_await_end`), then raises; the caller then reads the outcome from
        the data: the batch's keys (`find_idem`), or the new token (`principal_of`)."""
        with self.lock:
            conn, mark = self._live(), {}
            try:
                with conn.transaction() as tx:
                    def ex(sql, args=()):
                        cur = conn.execute(sql, args)
                        return cur.fetchall() if cur.description else []
                    mark["pid"], mark["start"] = ex(
                        "SELECT pg_backend_pid(), (SELECT backend_start FROM pg_stat_activity WHERE pid = pg_backend_pid())")[0]
                    out = body(ex)
                    if out is False:
                        raise self._psycopg.Rollback(tx)
                    mark["sent"] = True           # leaving the block sends COMMIT
                return out if mark.get("sent") else False
            except BaseException:
                if mark.get("sent") and conn.broken:
                    self._await_end(mark)
                raise

    def _await_end(self, mark) -> None:
        """Until the backend that sent a COMMIT (matched by pid and start time, so a reused pid is never mistaken
        for it) is gone, end it; after a restart it is gone already. Then nothing can still commit that transaction."""
        delay = 0.05
        while True:
            try:
                conn = self.conn = self._connect()
                alive = conn.execute("SELECT count(*) FROM pg_stat_activity WHERE pid = %s AND backend_start = %s",
                                     (mark["pid"], mark["start"])).fetchone()[0]
                if not alive:
                    return
                conn.execute("SELECT pg_terminate_backend(%s, 5000)", (mark["pid"],))
            except Exception as x:
                log.warning("a COMMIT reply was lost; waiting for its session to end (%r)", x)
            time.sleep(delay)
            delay = min(delay * 2, 5.0)

    def _unique_violation(self, x):
        return isinstance(x, self._psycopg.errors.UniqueViolation)

    def _lock_index(self, ex) -> None:
        """Index writers of every host on this database take turns for the rest of their transaction, so positions are
        assigned in commit order (a later committer reads a higher max): the cost is that appends to different streams
        from different hosts no longer commit at once."""
        ex("SELECT pg_advisory_xact_lock(%s)", (self.INDEX_LOCK,))


SQLITE_SUFFIXES = (".db", ".sqlite", ".sqlite3")


class NoPostgres(RuntimeError):
    """A Postgres target, and psycopg (the `postgres` extra) is not installed."""


def is_sqlite(target: str) -> bool:
    """`target` names a SQLite database: a `sqlite:` URL, `:memory:`, or a path ending .db, .sqlite or .sqlite3."""
    t = target.strip()
    return t.startswith("sqlite:") or t == ":memory:" or ("=" not in t and "://" not in t and t.endswith(SQLITE_SUFFIXES))


def open_store(target: str) -> StreamStore:
    """The store `target` names, by its form:

    - SQLite (store_sqlite.py): `sqlite:///abs/path.db` (three slashes, then the absolute path), `sqlite://rel/path.db`
      or `sqlite:rel/path.db` (relative to the working directory), `sqlite:///:memory:` or `:memory:` (in memory, gone
      at close: tests and throwaway embedding), or a bare path ending .db, .sqlite or .sqlite3; `~` is expanded.
    - Postgres, anything else: a libpq connection string, a URI (`postgresql://...`, `postgres://...`) or `key=value`
      pairs. `postgresql://` alone, or an empty string, leaves everything to libpq's own settings (PGHOST, PGPORT,
      PGUSER, PGPASSWORD, PGDATABASE, PGSERVICE, ~/.pgpass), as psql does. It needs the `postgres` extra."""
    if is_sqlite(target):
        from .store_sqlite import SqliteStore, sqlite_path
        return SqliteStore(sqlite_path(target))
    try:
        import psycopg  # noqa: F401
    except ImportError as x:
        raise NoPostgres("%s names a Postgres database, and psycopg is not installed: pip install "
                           "'provenstream[postgres]' (or name a SQLite file: sqlite:///path/streams.db)"
                           % ("the empty target" if not target else "the target")) from x
    return PostgresStore(target)


Store = open_store
