# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The host's interface as messages, apart from any carrier: protocol 2.

Every caller speaks JSON-RPC 2.0 to the host, whatever carries the bytes (an HTTP body, a line on stdin, a dict handed
over in process), so a stream answers alike on a laptop and on a shared host. This module is the message layer only:
it reads a request strictly, names the kind of method it asks for, and renders an answer. Deciding what the answer is
belongs to `host.Host.handle`; moving bytes belongs to the carriers (`api.py` for HTTP).

Requests. One JSON-RPC 2.0 request object per message, read by `wire.loads` (no repeated keys, no NaN, no lone
surrogates). A dict handed over in process is re-encoded and read the same way, so an embedder cannot send what the wire
would refuse. Batches (arrays) and notifications (no `id`) are `invalid_request` in protocol 2, so every request gets
exactly one answer and a carrier never has to decide which answers to hold back. An `id` is a string, an integer or
null (JSON-RPC discourages null but allows it, and the host has always echoed it); anything else is `invalid_request`.
Absent params are `{}`; params that are not an object are `invalid_params`. A message over `MAX_BODY` bytes is
`invalid_request` (`too_long`), one answer wherever it is refused: by `Host.handle`, for bytes or text handed to it, and
by a carrier before it has read the rest (an HTTP body, a stdin line), so no carrier answers it otherwise.

Answers. `Answer` is ok with a result, or one code of `ANSWERS`: the one table, read by every carrier, the command line
(its exit codes) and later the generated documentation. Every error's `data` carries `"code"`, the code string, so a
caller can branch on a name instead of a number. `unavailable` carries `retry: true` and an `incident` id and nothing
else: the exception behind it is logged under that id (`incident`), never sent, because its text can hold engine
output, paths or database detail a caller has no business seeing.

Methods come in three kinds (`classify`): a query (reads, safe to retry) and a host command (changes host state, never a
stream) are the host's, listed in its registry with a param schema each; any other dotted name (`COMMAND_NAME`) is a
proof command, which only the stream's revision can say exists, so it is routed there.

Protocol 2 (from protocol 1): every id param and result key ends in `_id` (`stream_id`, `principal_id`), principals
have no kind, every proof command takes `actor_id`, a revision is a commit and a package, and every refusal names the
rule broken (the host's own included).
"""
from __future__ import annotations
import logging, re
from dataclasses import dataclass, field
from typing import Any, Dict, Mapping, NamedTuple, Optional, Union

from . import ids, wire

PROTOCOL_VERSION = 2
MAX_BODY = 1 << 20
COMMAND_NAME = re.compile(r"[a-z][a-z0-9_]*(\.[a-z][a-z0-9_]*)+")

QUERY, HOST_COMMAND, PROOF_COMMAND = "query", "host_command", "proof_command"

log = logging.getLogger("provenstream.protocol")


class Kind(NamedTuple):
    rpc: Optional[int]       # the JSON-RPC error code (None for ok)
    message: str             # the JSON-RPC error message, as the deployed host has always sent it
    exit: int                # the command line's exit code
    meaning: str = ""        # when it is answered (the generated documentation's words)
    data: str = ""           # what `data` carries besides `code`


# The answer table. The JSON-RPC codes and messages are the ones hosts have answered with since protocol 1 began;
# changing one is a new protocol.
ANSWERS: Dict[str, Kind] = {
    "ok": Kind(None, "ok", 0, "done", "the result"),
    "parse_error": Kind(-32700, "parse error", 5, "not strict JSON (a repeated key, NaN, a lone surrogate)", "detail"),
    "invalid_request": Kind(-32600, "invalid request", 5, "not one JSON-RPC 2.0 request: also a batch, a notification, "
                            "a message over %d bytes" % MAX_BODY, "detail"),
    "method_not_found": Kind(-32601, "method not found", 5, "neither in the host's registry nor described by the "
                             "stream's revision", "detail, for a proof command: the revision"),
    "invalid_params": Kind(-32602, "invalid params", 5, "params malformed for the method's schema (the engine's "
                           "malformed lands here)", "detail"),
    "unauthorized": Kind(-32001, "unauthorized", 3, "no token, or one the host does not know; or a method that acts "
                         "as a principal asked without one", "detail, sometimes"),
    "refused": Kind(-32002, "refused", 4, "a proof rule or a host check said no; nothing stored",
                    "reason: the rule broken"),
    "unavailable": Kind(-32003, "unavailable", 6, "nothing stored; retry with the same idempotency key",
                        "retry: true, incident (the detail is logged under it, never sent)"),
}
CODE_OF_RPC: Dict[int, str] = {k.rpc: c for c, k in ANSWERS.items() if k.rpc is not None}

RequestId = Union[str, int, None]


@dataclass
class Answer:
    """The host's answer to one request: `code` "ok" with `result`, or an error code of `ANSWERS` with `data` (which
    always holds `"code"`). `id` is the request's, once known."""
    code: str = "ok"
    result: Any = None
    data: Dict[str, Any] = field(default_factory=dict)
    id: RequestId = None

    @property
    def ok(self) -> bool:
        return self.code == "ok"

    @property
    def exit_code(self) -> int:
        return ANSWERS[self.code].exit

    def with_id(self, rid: RequestId) -> "Answer":
        return Answer(self.code, self.result, self.data, rid)

    def response(self) -> Dict[str, Any]:
        """The JSON-RPC 2.0 response object."""
        body: Dict[str, Any] = {"jsonrpc": "2.0", "id": self.id}
        if self.ok:
            body["result"] = self.result
        else:
            k = ANSWERS[self.code]
            body["error"] = {"code": k.rpc, "message": k.message, "data": self.data}
        return body

    def dumps(self) -> str:
        return wire.dumps(self.response())


def ok(result: Any, rid: RequestId = None) -> Answer:
    return Answer("ok", result, {}, rid)


def error(code: str, rid: RequestId = None, **data: Any) -> Answer:
    if code not in ANSWERS or code == "ok":
        raise ValueError("not an error code of the answer table: %r" % code)
    return Answer(code, None, dict({"code": code}, **data), rid)


def too_long(limit: int = MAX_BODY) -> Answer:
    """The answer to a message over `limit` bytes, with id null (the id is in what was not read)."""
    return error("invalid_request", detail="message over %d bytes" % limit)


def refused(reason: str, rid: RequestId = None) -> Answer:
    return error("refused", rid, reason=reason)


def invalid_params(detail: str, rid: RequestId = None) -> Answer:
    return error("invalid_params", rid, detail=detail)


def unavailable(detail: str, rid: RequestId = None, exc_info: Any = None) -> Answer:
    """Nothing was stored; the caller may retry with the same idempotency key. `detail` goes to the log under a fresh
    incident id, which is all the caller gets of it."""
    incident = ids.uuid7()
    log.error("incident %s: %s", incident, detail, exc_info=exc_info)
    return error("unavailable", rid, retry=True, incident=incident)


@dataclass
class Request:
    id: RequestId
    method: str
    params: Dict[str, Any]


def _id_ok(rid: Any) -> bool:
    return rid is None or isinstance(rid, str) or (isinstance(rid, int) and not isinstance(rid, bool))


def parse(message: Any) -> Union[Request, Answer]:
    """One request, read strictly: bytes or text as received, or an already decoded object. Answers the `Request`, or
    the error `Answer` to send instead (with the request's id when it had a valid one)."""
    if isinstance(message, (bytes, bytearray, str)):
        try:
            msg = wire.loads(message)
        except wire.BadJson as x:
            return error("parse_error", detail=str(x))
    else:
        try:
            msg = wire.loads(wire.dumps(message))      # in process: the same strictness as the wire
        except (TypeError, ValueError) as x:
            return error("parse_error", detail="not JSON: %s" % x)
    if isinstance(msg, list):
        return error("invalid_request", detail="batches are not accepted (protocol %d)" % PROTOCOL_VERSION)
    if not isinstance(msg, dict):
        return error("invalid_request", detail="expected a JSON-RPC 2.0 request object")
    rid = msg.get("id")
    if not _id_ok(rid):
        return error("invalid_request", detail="id: expected a string, an integer or null")
    if "id" not in msg:
        return error("invalid_request", detail="notifications (requests without an id) are not accepted (protocol %d)"
                     % PROTOCOL_VERSION)
    if msg.get("jsonrpc") != "2.0" or not isinstance(msg.get("method"), str) or \
            not set(msg) <= {"jsonrpc", "id", "method", "params"}:
        return error("invalid_request", rid, detail="expected {jsonrpc: \"2.0\", id, method, params?}")
    params = msg.get("params", {})
    if not isinstance(params, dict):
        return error("invalid_params", rid, detail="params: expected an object")
    return Request(rid, msg["method"], params)


def classify(method: str, registry: Mapping[str, Any]) -> Optional[str]:
    """The kind of `method`: the registry entry's (`QUERY` or `HOST_COMMAND`), else `PROOF_COMMAND` for a dotted name
    the stream's revision may describe, else None (`method_not_found`). The registry comes first, so no proof can
    shadow a host method."""
    entry = registry.get(method)
    if entry is not None:
        return entry.kind
    return PROOF_COMMAND if COMMAND_NAME.fullmatch(method) else None


def code_of(rpc_code: Any, data: Any) -> str:
    """The code string of a JSON-RPC error as received: `data.code` when it names one, else by the JSON-RPC code (a
    host from before `data.code`); an unknown code reads as unavailable."""
    if isinstance(data, dict) and data.get("code") in ANSWERS and data["code"] != "ok":
        return data["code"]
    return CODE_OF_RPC.get(rpc_code, "unavailable")
