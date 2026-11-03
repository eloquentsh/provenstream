# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The host: one function, `Host.handle(message, auth) -> Answer`, behind every carrier.

Every decision about a caller's request is made here, once, so a stream behaves the same in process, over stdio and
over HTTP: refuse a message over `protocol.MAX_BODY` bytes (`protocol.too_long`), parse (`protocol.parse`), name the
method's kind (`protocol.classify`), authenticate, check the params against the method's schema, run, answer. The
carriers only move bytes and turn their credential into `Token`; the write path behind a proof command (the actor,
the route, mint, judge, compare-and-set, chain) is `service.Service`. `rpc.discover` describes all of it as an OpenRPC
document (`openrpc.py`), and HOST-PROTOCOL.md is generated from that.

Auth. `Token(t)` is what every carrier builds: the host looks `t` up, and the token alone names the caller; none, or
one the host does not know, is `unauthorized`. `Operator(principal)` exists only in process (the command line's local
mode, an embedder): whoever holds the database is already the host, and acts as any principal the store knows (one it
does not know is `invalid_params`, as a write naming an unissued principal always was). `Operator(None)` is the operator
as no principal: it may ask what needs none (the reads, `revisions.list`, `revision.describe`, `rpc.discover`,
`principal.create`) and is `unauthorized` for what acts as a principal (a proof command, `whoami`, `token.rotate`).

Methods (the registry, `METHODS`, holds each host method's param schema, result schema, summary and handler;
`rpc.discover` generates an OpenRPC document from it and from each served revision's describe):

- any command a stream's proof describes, by its name, with its params: `stream.open {proof_revision_url, meta?}`,
  `stream.close {stream_id, meta?}`, `task.open {stream_id, task_id, parent_task_id?, meta?}`, ... The host routes it
  to the engine of the stream's revision (`stream_id`; for `stream.open`, the revision its URL names) and mints the
  fresh ids. Every proof command takes an optional `actor_id`, which must be the caller's own principal
  (`actor_id_must_match_the_token`) and is filled in from the token when absent, and an optional `idempotency_key`,
  which makes a retry by the same caller return the first answer (the same key from two callers is two writes).
  Result `{"seq", "event", "chain"}`: `chain` is the receipt, the stream's head after this row (chain.py). A
  well-formed name the stream's revision does not describe is `method_not_found`, its detail naming the revision;
  params malformed for a command it does describe are `invalid_params`.
- `stream.get {stream_id}`: the stream as its engine reads it;
- `stream.events {stream_id, from?, limit?}`: its events from seq `from`, each with `seq` and the stream's `chain`
  head after it; `stream.rows {stream_id, from?, limit?}`: the stored rows as stored, with each row's `meta_salt` and
  `chain` (hex; null for rows written before the chain), for `provenstream verify`. Both page: at most `limit` (default
  and most `PAGE`) per answer, and `next` is the `from` of the next page, or null at the end;
- `stream.head {stream_id}`: `{"stream_id", "length", "chain"}`, the stream's current head;
- `stream.describe {stream_id}` / `revision.describe {revision}`: the engine's description;
- `revisions.list`: the revisions this host serves (each a commit and a package) and whether each engine runs now;
- `usage.get {scope?, key?}`: the usage counters (`engine_ms` is an estimate, `cpu_ms` measured); see `_usage`;
- `whoami`: `{"principal_id"}` of the caller;
- `rpc.discover`: the OpenRPC document of this registry and of every served revision's commands;
- `token.rotate` (a host command): a new token for the caller, the old one revoked;
- `principal.create {principal_id?}` (a host command): any signed-in principal, and the operator, gets a new principal
  and its first token, `{"principal_id", "token"}`. With `principal_id` (the operator only: a token's caller is refused
  `only_the_operator_can_reissue_a_principal`) it issues a first token for an id this store holds no token for, as
  after `import` (which moves no tokens); an id that holds one is `principal_must_have_no_token` (rotate its token
  instead).

Reading is unrestricted (`gap_read_visibility` is outside the model): any authenticated principal reads any stream, and
the operator reads as no principal too. A read of a stream with no rows is refused `stream_must_exist`.

Errors are the answer table's (`protocol.ANSWERS`). Refusals by the host itself (`data.reason`), each named for the rule
broken: `stream_must_exist`, `revision_must_be_installed`, `repository_must_match_the_engine` (a `stream.open` whose URL
names another repository than the one the revision's engine was built from), `engine_must_implement_the_interface` (a
`stream.open` naming a revision whose engine does not implement the stream interface, `interface.py`),
`actor_id_must_match_the_token`, `idempotency_key_must_match_its_request`, and for `principal.create`
`only_the_operator_can_reissue_a_principal` and `principal_must_have_no_token`; any other reason is the proof's rule, `revision_url_must_name_a_commit` included,
which the host applies itself, as the core reads it, to a `stream.open` URL that names no revision.
Anything that goes wrong inside is `unavailable` with an incident id, its detail logged, never sent.
"""
from __future__ import annotations
import logging, os, re
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, Mapping, Optional, Tuple, Union

from . import ids, protocol, wire
from .protocol import Answer, HOST_COMMAND, PROOF_COMMAND, QUERY
from .revisions import REVISION_KEY, load_map, split_key
from .service import Accepted, Malformed, Principal, Rejected, Service, Unavailable, Undescribed

log = logging.getLogger("provenstream.host")

PAGE = 1000        # rows per page of stream.events and stream.rows: the default limit and the most a caller may ask


@dataclass(frozen=True)
class Token:
    """A carrier's credential: the bearer token as received (None when the request carried none)."""
    token: Optional[str]


@dataclass(frozen=True)
class Operator:
    """In process only: the embedder acting as `principal` (None: as no principal). No carrier builds one."""
    principal: Optional[str]


Auth = Union[Token, Operator]


class HostError(Exception):
    """An error answer, raised: by handlers inside `handle`, and by `Host.command` / `Host.query` to their callers."""

    def __init__(self, answer: Answer):
        self.answer = answer
        super().__init__("%s: %s" % (answer.code, wire.dumps(answer.data)))


# -- params: a small JSON Schema subset, enough to check params and to describe them (OpenRPC, M4) ---------------------

UUID = {"type": "string", "pattern": ids.CANONICAL_ID.pattern, "description": "a canonical lowercase UUID"}
STREAM = UUID
SEQ = {"type": "integer", "minimum": 0, "description": "a natural number"}
LIMIT = {"type": "integer", "minimum": 1, "maximum": PAGE, "description": "an integer from 1 to %d" % PAGE}
REVISION = {"type": "string", "pattern": REVISION_KEY.pattern,
            "description": "a revision: a full commit, and /<package> for a package other than the root"}


def schema(required: Tuple[str, ...] = (), **properties: dict) -> dict:
    return {"type": "object", "properties": properties, "required": list(required), "additionalProperties": False}


def check_params(spec: dict, params: Dict[str, Any]) -> Optional[str]:
    """Why `params` do not fit `spec` (the detail of `invalid_params`), or None when they do."""
    props = spec["properties"]
    for k in params:
        if k not in props:
            return "params: unknown key %s (expected {%s})" % (k, ", ".join(
                p + ("" if p in spec["required"] else "?") for p in props)) if props else "params: expected none"
    for k in spec["required"]:
        if k not in params:
            return "%s: required" % k
    for k, v in params.items():
        p = props[k]
        t = p.get("type")
        good = ((t == "string" and isinstance(v, str)) or
                (t == "integer" and isinstance(v, int) and not isinstance(v, bool)))
        if good and t == "string":
            good = ("pattern" not in p or re.fullmatch(p["pattern"], v) is not None) and v in p.get("enum", [v])
        if good and t == "integer":
            good = p.get("minimum", v) <= v <= p.get("maximum", v)
        if not good:
            return "%s: expected %s" % (k, p.get("description") or ("one of " + "|".join(p["enum"]) if "enum" in p
                                                                       else t))
    return None


# -- the registry ---------------------------------------------------------------------------------------------------

ANYONE, PRINCIPAL, OPERATOR = "anyone", "principal", "operator"


@dataclass
class Call:
    host: "Host"
    caller: Optional[Principal]
    params: Dict[str, Any]
    operator: bool = False               # in process, as the operator (`Operator`)


@dataclass(frozen=True)
class Method:
    name: str
    kind: str                            # protocol.QUERY or protocol.HOST_COMMAND
    summary: str
    params: dict                         # its param schema
    who: str                             # ANYONE (any authenticated caller, or the operator as no principal),
                                         # PRINCIPAL (a caller that is a principal), or OPERATOR (in process only)
    handler: Callable[[Call], Any] = field(compare=False)
    result: dict = field(default_factory=dict, compare=False)     # its result schema, for rpc.discover


def _refuse(reason: str) -> HostError:
    return HostError(protocol.refused(reason))


def _known_stream(c: Call) -> str:
    """The stream the params name, which must have rows (`stream_must_exist`)."""
    s = c.params["stream_id"]
    if c.host.store.last_chained(s) is None:
        raise _refuse("stream_must_exist")
    return s


def _stream_get(c: Call) -> Any:
    view = c.host.service.read_stream(_known_stream(c))
    if not isinstance(view, dict) or "error" in view:
        raise _refuse("stream_must_exist")
    return view


def _page(c: Call):
    """A page of a stream's rows from the cursor, with the head after each row, and the next cursor."""
    s, start, limit = _known_stream(c), c.params.get("from", 0), c.params.get("limit", PAGE)
    rows = c.host.store.read_chained(s, start, limit + 1)
    page, more = rows[:limit], len(rows) > limit
    before = None
    if page and any(r[4] is None for r in page) and start > 0:   # a row from before the chain needs the head before
        before = c.host.service.chain_at(s, start - 1)
    heads = c.host.service.walk(s, page, before)
    return s, page, heads, (page[-1][0] + 1 if more else None)


def _stream_events(c: Call) -> Any:
    s, page, heads, nxt = _page(c)
    return {"stream_id": s, "events": [dict(wire.loads(e), seq=seq, chain=h.hex())
                                       for (seq, _, e, _, _), h in zip(page, heads)], "next": nxt}


def _stream_rows(c: Call) -> Any:
    s, page, _, nxt = _page(c)
    hx = lambda b: b.hex() if b is not None else None
    return {"stream_id": s, "rows": [{"seq": seq, "request": r, "event": e, "meta_salt": hx(salt), "chain": hx(ch)}
                                     for seq, r, e, salt, ch in page], "next": nxt}


def _stream_head(c: Call) -> Any:
    s = c.params["stream_id"]
    length, h = c.host.service.head(s)
    if not length:
        raise _refuse("stream_must_exist")
    return {"stream_id": s, "length": length, "chain": h.hex()}


def _stream_describe(c: Call) -> Any:
    rev = c.host.service.revision_of_stream(c.params["stream_id"])
    if rev is None:
        raise _refuse("stream_must_exist")
    return c.host.service.describe(rev)


def _revision_describe(c: Call) -> Any:
    rev = c.params["revision"]
    if rev not in c.host.service.judges:
        raise _refuse("revision_must_be_installed")
    return c.host.service.describe(rev)


def _revisions_list(c: Call) -> Any:
    out = []
    for r, up in sorted(c.host.service.running().items()):
        commit, package = split_key(r)
        out.append({"revision": r, "commit": commit, "package": package, "running": up})
    return {"revisions": out}


def _whoami(c: Call) -> Any:
    return {"principal_id": c.caller.principal}


USAGE_NOTES = {"engine_ms": "estimate: wall time of engine calls",
               "cpu_ms": "measured from the engine process (per revision)",
               "bytes": "bytes of requests and events appended by this host",
               "bytes_stored": "exact: bytes of the stream's stored rows"}


def _usage(c: Call) -> Any:
    """Stream counters are read one stream at a time (`scope: stream, key: S`, a stream with rows); revision counters
    (`scope: revision`, with or without a `key`) are the host's per engine, sums over every stream of that revision;
    with no scope, those are what is answered."""
    scope, key = c.params.get("scope"), c.params.get("key")
    if key is not None and scope is None:
        raise HostError(protocol.invalid_params("key: needs a scope (expected {scope?: stream|revision, key?})"))
    if scope == "stream":
        if key is None:
            raise HostError(protocol.invalid_params("key: required with scope stream (a stream's counters are read "
                                                    "one stream at a time)"))
        if not ids.CANONICAL_ID.fullmatch(key) or c.host.store.last_chained(key) is None:
            raise _refuse("stream_must_exist")
    return {"usage": c.host.service.usage_report(scope or "revision", key), "notes": dict(USAGE_NOTES)}


def _token_rotate(c: Call) -> Any:
    return {"token": c.host.store.rotate(c.caller.principal)}


def _principal_create(c: Call) -> Any:
    store, p = c.host.store, c.params.get("principal_id")
    if p is None:
        p = ids.uuid7()
    else:
        if not c.operator:
            raise _refuse("only_the_operator_can_reissue_a_principal")
        if store.known(p):
            raise _refuse("principal_must_have_no_token")
    try:
        token = store.create_principal(p)
    except ValueError:
        raise _refuse("principal_must_have_no_token")
    return {"principal_id": p, "token": token}


def _discover(c: Call) -> Any:
    from . import openrpc
    return openrpc.discover(c.host)


NONE = schema()
HEX = {"type": "string", "pattern": "[0-9a-f]{64}", "description": "a chain head: 64 hex digits (chain.py)"}
NEXT = {"type": ["integer", "null"], "description": "the `from` of the next page, or null at the end"}


def obj(**properties: dict) -> dict:
    """A result's schema: an object with these keys (results are open: within a protocol they only gain keys)."""
    return {"type": "object", "properties": properties}


DESCRIBED = obj(revision={"type": "string"}, repo={"type": "string"}, package={"type": "string"},
                protocol={"type": "integer"}, schema=obj(commands={"type": "array"}))
PAGE_PARAMS = {"from": SEQ, "limit": LIMIT}           # a paged query: rows from seq `from` (0), at most `limit` (PAGE)
ONE_STREAM = schema(("stream_id",), stream_id=STREAM)
METHODS: Dict[str, Method] = {m.name: m for m in [
    Method("stream.get", QUERY, "the stream as its revision's engine reads it", ONE_STREAM, ANYONE, _stream_get,
           result=dict(obj(stream_id=STREAM, opener_id=UUID, proof_revision_url={"type": "string"},
                           closed={"type": "boolean"}), description="the engine's view; a layer's adds its own keys")),
    Method("stream.events", QUERY, "a page of the stream's events, each with its seq and the chain head after it",
           schema(("stream_id",), stream_id=STREAM, **PAGE_PARAMS), ANYONE, _stream_events,
           result=obj(stream_id=STREAM, events={"type": "array", "items": obj(
               seq=SEQ, event={"type": "string"}, stream_id=STREAM, actor_id=UUID, chain=HEX)}, next=NEXT)),
    Method("stream.rows", QUERY, "a page of the stream's stored rows as stored, with meta salts and chain heads",
           schema(("stream_id",), stream_id=STREAM, **PAGE_PARAMS), ANYONE, _stream_rows,
           result=obj(stream_id=STREAM, rows={"type": "array", "items": obj(
               seq=SEQ, request={"type": "string", "description": "the stored request, as JSON text"},
               event={"type": "string", "description": "the stored event, as JSON text"},
               meta_salt={"type": ["string", "null"]}, chain={"type": ["string", "null"]})}, next=NEXT)),
    Method("stream.head", QUERY, "the stream's length and current chain head", ONE_STREAM, ANYONE, _stream_head,
           result=obj(stream_id=STREAM, length=SEQ, chain=HEX)),
    Method("stream.describe", QUERY, "the description of the stream's revision (its commands)", ONE_STREAM, ANYONE,
           _stream_describe, result=DESCRIBED),
    Method("revision.describe", QUERY, "the description of a revision this host serves",
           schema(("revision",), revision=REVISION), ANYONE, _revision_describe, result=DESCRIBED),
    Method("revisions.list", QUERY, "the revisions this host serves (a commit and a package each), and whether each "
           "engine runs now", NONE, ANYONE, _revisions_list,
           result=obj(revisions={"type": "array", "items": obj(revision={"type": "string"}, commit={"type": "string"},
                                                               package={"type": "string"},
                                                               running={"type": "boolean"})})),
    Method("whoami", QUERY, "the caller's principal", NONE, PRINCIPAL, _whoami, result=obj(principal_id=UUID)),
    Method("usage.get", QUERY, "usage counters: one stream's, or per revision",
           schema((), scope={"type": "string", "enum": ["stream", "revision"], "description": "stream or revision"},
                  key={"type": "string", "description": "a string: the stream or revision"}), ANYONE, _usage,
           result=obj(usage={"type": "array"}, notes={"type": "object"})),
    Method("rpc.discover", QUERY, "this host's OpenRPC document: every method, and every served revision's commands",
           NONE, ANYONE, _discover, result={"type": "object", "description": "an OpenRPC 1.3 document"}),
    Method("token.rotate", HOST_COMMAND, "a new token for the caller, the old one revoked", NONE, PRINCIPAL,
           _token_rotate, result=obj(token={"type": "string"})),
    Method("principal.create", HOST_COMMAND, "a new principal and its first token (with `principal_id`, the operator "
           "only: a first token for an id this store holds no token for)",
           schema((), principal_id=UUID), ANYONE, _principal_create,
           result=obj(principal_id=UUID, token={"type": "string"})),
]}


# -- the host -------------------------------------------------------------------------------------------------------

class Host:
    """The interface over one `Service`. `Host.open` builds the store and the service and owns both; `Host(service)`
    wraps a service its caller keeps (and closes)."""

    def __init__(self, service: Service, owns_store: bool = False):
        self.service, self.store = service, service.store
        self._owns_store = owns_store

    @classmethod
    def open(cls, db: str, engines: Union[None, str, Mapping[str, Any]] = None, **service_kwargs: Any) -> "Host":
        """The store at `db` (`store.open_store`) and a service over it with `engines`: an engines directory (its
        revisions.json), a revision map {revision key: engine command}, or None for none."""
        from .store import open_store
        if engines is None:
            emap: Dict[str, Any] = {}
        elif isinstance(engines, str):
            emap = load_map(os.path.join(engines, "revisions.json"))
        else:
            emap = dict(engines)
        store = open_store(db)
        try:
            return cls(Service(store, emap, **service_kwargs), owns_store=True)
        except BaseException:
            store.close()
            raise

    def close(self) -> None:
        self.service.close()
        if self._owns_store:
            self.store.close()

    def healthy(self) -> bool:
        """The store answers (`/healthz`); a failure is logged, not answered."""
        try:
            self.store.ping()
            return True
        except Exception:
            log.exception("healthz: the store does not answer")
            return False

    # -- the interface --------------------------------------------------------------------------------------------

    def handle(self, message: Any, auth: Auth) -> Answer:
        """One request (a JSON-RPC 2.0 request object, or its bytes or text), as `auth`: always one answer."""
        if not isinstance(auth, (Token, Operator)):
            raise TypeError("auth: expected Token or Operator, not %r" % type(auth).__name__)
        if isinstance(message, (bytes, bytearray, str)):
            size = len(message.encode("utf-8", "surrogatepass")) if isinstance(message, str) else len(message)
            if size > protocol.MAX_BODY:
                return protocol.too_long()             # as every carrier answers it, so in process is no exception
        req = protocol.parse(message)
        if isinstance(req, Answer):
            return req
        try:
            return self._handle(req, auth).with_id(req.id)
        except HostError as x:
            return x.answer.with_id(req.id)
        except Unavailable as x:
            return protocol.unavailable("%s: %s" % (req.method, x), req.id)
        except Exception as x:
            return protocol.unavailable("%s: %s: %s" % (req.method, type(x).__name__, x), req.id, exc_info=True)

    def command(self, name: str, *, auth: Auth, **params: Any) -> Any:
        """A proof command or host command, in process: its result, or `HostError` carrying the answer."""
        return self._call((PROOF_COMMAND, HOST_COMMAND), name, auth, params)

    def query(self, name: str, *, auth: Auth, **params: Any) -> Any:
        """A query, in process: its result, or `HostError` carrying the answer."""
        return self._call((QUERY,), name, auth, params)

    def _call(self, kinds, name: str, auth: Auth, params: Dict[str, Any]) -> Any:
        if protocol.classify(name, METHODS) not in kinds:
            raise HostError(protocol.error("method_not_found"))
        ans = self.handle({"jsonrpc": "2.0", "id": 0, "method": name, "params": params}, auth)
        if not ans.ok:
            raise HostError(ans)
        return ans.result

    def _handle(self, req: protocol.Request, auth: Auth) -> Answer:
        kind = protocol.classify(req.method, METHODS)
        if kind is None:
            return protocol.error("method_not_found")       # before authenticating, as hosts always have
        caller = self._authenticate(auth)
        if kind == PROOF_COMMAND:
            return self._proof_command(self._principal(caller), req.method, req.params)
        m = METHODS[req.method]
        why = check_params(m.params, req.params)
        if why is not None:
            return protocol.invalid_params(why)
        c = Call(self, caller, req.params, operator=isinstance(auth, Operator))
        if m.who == OPERATOR and not c.operator:
            return protocol.refused("only_the_operator_can_" + m.name.replace(".", "_"))
        if m.who == PRINCIPAL:
            self._principal(caller)
        return protocol.ok(m.handler(c))

    def _authenticate(self, auth: Auth) -> Optional[Principal]:
        if isinstance(auth, Token):
            found = self.store.principal_of(auth.token) if auth.token else None
            if found is None:
                raise HostError(protocol.error("unauthorized"))
            return Principal(found)
        if auth.principal is None:
            return None
        if not self.store.known(auth.principal):
            raise HostError(protocol.invalid_params("caller: no principal %s was issued by this host" % auth.principal))
        return Principal(auth.principal)

    @staticmethod
    def _principal(caller: Optional[Principal]) -> Principal:
        if caller is None:
            raise HostError(protocol.error("unauthorized", detail="this method acts as a principal: name one"))
        return caller

    def _proof_command(self, caller: Principal, method: str, params: Dict[str, Any]) -> Answer:
        out = self.service.submit(caller, method, params)
        if isinstance(out, Undescribed):
            return protocol.error("method_not_found", detail=out.detail)
        if isinstance(out, Malformed):
            return protocol.invalid_params(out.detail)
        if isinstance(out, Rejected):
            return protocol.refused(out.reason)
        assert isinstance(out, Accepted)
        return protocol.ok({"seq": out.seq, "event": out.event, "chain": out.chain})
