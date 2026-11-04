# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""Discovery: the host's interface as an OpenRPC 1.3 document (`rpc.discover`), and HOST-PROTOCOL.md generated from it.

OpenRPC (https://spec.open-rpc.org/) is to JSON-RPC what OpenAPI is to REST, so a caller, or an adapter (MCP tools, a
REST route per method), can be generated from one document instead of from prose. The document is built from what
decides, never written beside it: the host's registry (`host.METHODS`, each method's param and result schema), the
describe of every revision served (its proof commands, params, minted fields, who, event and rules), and the answer table
(`protocol.ANSWERS`, as `components.errors`). It is deterministic (methods by name, revisions sorted, no times, no
counts), so two hosts' documents can be diffed and the committed HOST-PROTOCOL.md checked for staleness.

Proof commands. Each command of each served revision is a method: a param of kind `uuid` is a required canonical id,
`uuid?` an optional one, `meta` an optional string, `ref` an optional position in the stream, any other kind a required
text the engine checks the form of. Minted fields are never params: the host mints them, and they are in the result's
event. `actor_id` (the caller, filled in from the token) and `idempotency_key` are optional params of every proof
command. Who may send it (`x-provenstream-who`), its event (`x-provenstream-event`) and the rules that can refuse it, in
order (`x-provenstream-rules`), are the description's. A command several revisions describe alike is one method listing
them all in `x-provenstream-revisions`; where they differ, its params are the union (required only where every revision
requires it) and `x-provenstream-variants` gives each revision's exactly.

Versions. `x-provenstream-protocol` is the host's protocol (`protocol.PROTOCOL_VERSION`); within a protocol changes
are additive only: new methods, new optional params, new result keys. Each revision's engine protocol is listed with
it (`describe`'s `"protocol"`: 2, the only one this host serves).

    python3 -m provenstream.openrpc --engine ENGINE [--markdown]     the document (or HOST-PROTOCOL.md) of one engine
    scripts/gen_host_protocol [--check]                              HOST-PROTOCOL.md from the core engine
"""
from __future__ import annotations
import argparse, json, sys
from typing import Any, Dict, List, Mapping, Optional

from . import __version__, ids, protocol
from .schema import CommandSpec, commands_of, protocol_of

OPENRPC = "1.3.2"
TITLE = "Provenstream host"
ERRORS = [c for c in protocol.ANSWERS if c != "ok"]
CALL_ERRORS = ["invalid_params", "unauthorized", "refused", "unavailable"]

UUID = {"type": "string", "pattern": ids.CANONICAL_ID.pattern, "description": "a canonical lowercase UUID"}
FIELD_KINDS: Dict[str, dict] = {
    "uuid": UUID,
    "uuid?": {"type": ["string", "null"], "pattern": ids.CANONICAL_ID.pattern,
              "description": "optional: a canonical lowercase UUID, or null"},
    "meta": {"type": ["string", "null"], "description": "optional opaque text: at most 4096 UTF-8 bytes, no control "
                                                        "character (committed to by the chain, erasable)"},
    "ref": {"type": ["integer", "null"], "minimum": 0, "description": "optional: the 0-based position of an earlier "
                                                                      "event of the same stream"},
}
OPTIONAL_KINDS = ("uuid?", "meta", "ref")
IDEMPOTENCY_KEY = {"type": "string", "minLength": 1, "maxLength": 200,
                   "description": "makes a retry by the same caller answer the first answer (two callers' same key "
                                  "is two writes)"}
ACTOR_ID = dict(UUID, description="the caller's own principal_id (filled in from the token when absent; any other is "
                                  "refused actor_id_must_match_the_token)")
CHAIN_HEAD = {"type": "string", "pattern": "[0-9a-f]{64}", "description": "the stream's chain head after this row"}


def field_schema(kind: str) -> dict:
    """The JSON schema of a field of `kind`; a kind the table does not name is a text the engine checks."""
    if kind in FIELD_KINDS:
        return dict(FIELD_KINDS[kind])
    return {"type": "string", "description": "%s, its form checked by the engine" % (
        "text" if kind == "text" else "text (%s)" % kind)}


def _param(name: str, schema: dict, required: bool) -> dict:
    s = dict(schema)
    d = s.pop("description", None)
    out: Dict[str, Any] = {"name": name, "required": required, "schema": s}
    if d:
        out["description"] = d
    return out


def _errors(codes: List[str]) -> List[dict]:
    return [{"$ref": "#/components/errors/%s" % c} for c in codes]


# -- proof commands ---------------------------------------------------------------------------------------------------

def proof_variant(spec: CommandSpec) -> dict:
    """What one revision says of one command: its params, its result, its minted fields, who, event and rules."""
    params = [_param(f, field_schema(k), k not in OPTIONAL_KINDS) for f, k in spec.params]
    params.append(_param("actor_id", ACTOR_ID, False))
    params.append(_param("idempotency_key", IDEMPOTENCY_KEY, False))
    kinds = dict(spec.params)
    event: Dict[str, Any] = {}
    for f in spec.event_fields:
        if f == "event":
            event[f] = {"type": "string", "const": spec.event}
        elif f == "actor_id":
            event[f] = dict(UUID, description="the caller")
        elif f in spec.minted:
            event[f] = dict(UUID, description="minted by the host")
        else:
            event[f] = field_schema(kinds.get(f, "text"))
    result = {"type": "object", "properties": {
        "seq": {"type": "integer", "minimum": 0, "description": "the event's position in the stream"},
        "event": {"type": "object", "properties": event, "required": list(spec.event_fields)},
        "chain": CHAIN_HEAD}, "required": ["seq", "event", "chain"]}
    return {"params": params, "result": result, "minted": list(spec.minted), "stream_id": spec.stream,
            "who": spec.who, "event": {"name": spec.event, "fields": list(spec.event_fields)},
            "rules": list(spec.rules)}


def _same(a: Any, b: Any) -> bool:
    return json.dumps(a, sort_keys=True) == json.dumps(b, sort_keys=True)


def _union(variants: List[dict]) -> List[dict]:
    """Params accepted by some variant: required only where every variant requires them; a schema that differs
    between variants is any of theirs."""
    order: List[str] = []
    by: Dict[str, List[dict]] = {}
    for v in variants:
        for p in v["params"]:
            if p["name"] not in by:
                order.append(p["name"])
                by[p["name"]] = []
            by[p["name"]].append(p)
    out = []
    for n in order:
        ps = by[n]
        required = len(ps) == len(variants) and all(p["required"] for p in ps)
        schemas: List[dict] = []
        for p in ps:
            if not any(_same(p["schema"], s) for s in schemas):
                schemas.append(p["schema"])
        q = _param(n, schemas[0] if len(schemas) == 1 else {"anyOf": schemas}, required)
        if "description" in ps[0]:
            q["description"] = ps[0]["description"]
        out.append(q)
    return out


def proof_methods(describes: Mapping[str, Any]) -> List[dict]:
    """A method per proof command of every revision in `describes` ({revision: its describe})."""
    seen: Dict[str, List[tuple]] = {}
    for rev in sorted(describes):
        for name, spec in commands_of(describes[rev]).items():
            seen.setdefault(name, []).append((rev, proof_variant(spec)))
    out = []
    for name in sorted(seen):
        groups: List[dict] = []                         # distinct variants, each with the revisions describing it
        for rev, v in seen[name]:
            for g in groups:
                if _same(g["variant"], v):
                    g["revisions"].append(rev)
                    break
            else:
                groups.append({"variant": v, "revisions": [rev]})
        first = groups[0]["variant"]
        m: Dict[str, Any] = {
            "name": name, "summary": "a proof command: appends at most one event, if the stream's proof accepts it",
            "paramStructure": "by-name",
            "params": first["params"] if len(groups) == 1 else _union([g["variant"] for g in groups]),
            "result": {"name": "accepted", "schema": first["result"]},
            "errors": _errors(["method_not_found"] + CALL_ERRORS),
            "x-provenstream-kind": protocol.PROOF_COMMAND, "x-provenstream-auth": "principal",
            "x-provenstream-revisions": sorted(r for g in groups for r in g["revisions"]),
            "x-provenstream-minted": first["minted"], "x-provenstream-stream-id": first["stream_id"],
            "x-provenstream-who": first["who"], "x-provenstream-event": first["event"],
            "x-provenstream-rules": first["rules"],
        }
        if len(groups) > 1:
            m["x-provenstream-variants"] = [dict(g["variant"], revisions=sorted(g["revisions"])) for g in groups]
        out.append(m)
    return out


# -- host methods -----------------------------------------------------------------------------------------------------

def host_methods() -> List[dict]:
    from .host import METHODS, OPERATOR
    out = []
    for name in sorted(METHODS):
        m = METHODS[name]
        props, req = m.params["properties"], m.params["required"]
        out.append({
            "name": name, "summary": m.summary, "paramStructure": "by-name",
            "params": [_param(p, props[p], p in req) for p in props],
            "result": {"name": "result", "schema": m.result},
            "errors": _errors(CALL_ERRORS),
            "x-provenstream-kind": m.kind, "x-provenstream-auth": m.who,
            **({"x-provenstream-in-process-only": True} if m.who == OPERATOR else {}),
        })
    return out


def document(describes: Mapping[str, Any], unavailable: Optional[List[str]] = None) -> dict:
    """The OpenRPC document of the registry and of the revisions in `describes` ({revision: describe})."""
    methods = sorted(host_methods() + proof_methods(describes), key=lambda m: m["name"])
    doc: Dict[str, Any] = {
        "openrpc": OPENRPC,
        "info": {"title": TITLE, "version": __version__,
                 "description": "JSON-RPC 2.0, one request per message; the same answers in process, over stdio and "
                                "over HTTP (POST /rpc)"},
        "x-provenstream-protocol": protocol.PROTOCOL_VERSION,
        "x-provenstream-revisions": [{"revision": r, "protocol": protocol_of(describes[r])} for r in sorted(describes)],
        "methods": methods,
        "components": {"errors": {c: {"code": protocol.ANSWERS[c].rpc, "message": protocol.ANSWERS[c].message,
                                      "data": {"code": c},
                                      "x-provenstream-meaning": protocol.ANSWERS[c].meaning,
                                      "x-provenstream-data": protocol.ANSWERS[c].data,
                                      "x-provenstream-exit": protocol.ANSWERS[c].exit} for c in ERRORS}},
    }
    if unavailable:
        doc["x-provenstream-revisions-unavailable"] = sorted(unavailable)
    return doc


def discover(host) -> dict:
    """`rpc.discover`: the document of `host`, describing every revision it serves (starting an engine never
    described). A revision whose engine cannot describe itself now is listed as unavailable rather than failing the
    whole document, so one broken engine does not hide the rest."""
    from .service import Unavailable
    describes, down = {}, []
    for rev in sorted(host.service.judges):
        try:
            describes[rev] = host.service.describe(rev)
        except Unavailable:
            down.append(rev)
    return document(describes, down)


# -- HOST-PROTOCOL.md -------------------------------------------------------------------------------------------------

def _brief(schema: dict) -> str:
    """A schema in a few words, for a table cell."""
    if "anyOf" in schema:
        return " or ".join(_brief(s) for s in schema["anyOf"])
    t = schema.get("type", "any")
    t = " or ".join(t) if isinstance(t, list) else t
    if "const" in schema:
        return "`%s`" % json.dumps(schema["const"])
    if "enum" in schema:
        return " or ".join("`%s`" % e for e in schema["enum"])
    if schema.get("pattern") == ids.CANONICAL_ID.pattern:
        return "UUID"
    bounds = []
    if "minimum" in schema:
        bounds.append(">= %d" % schema["minimum"])
    if "maximum" in schema:
        bounds.append("<= %d" % schema["maximum"])
    if "maxLength" in schema:
        bounds.append("%d to %d chars" % (schema.get("minLength", 0), schema["maxLength"]))
    return t + (" (%s)" % ", ".join(bounds) if bounds else "")


def _keys(schema: dict) -> str:
    props = schema.get("properties") or {}
    return "{%s}" % ", ".join(props) if props else (schema.get("description") or schema.get("type") or "")


AUTH_WORDS = {"anyone": "any authenticated caller, or the operator as no principal",
              "principal": "a principal (a token's, or the operator acting as one)",
              "operator": "in process only (`Operator`): a token's caller is refused `only_the_operator_can_<act>`"}

PROSE = """\
# The host protocol

<!-- Generated by scripts/gen_host_protocol (python3 -m provenstream.openrpc --markdown) from the host's registry
(host/provenstream/host.py), the core engine's description and the answer table (host/provenstream/protocol.py). Do
not edit: scripts/check.sh regenerates it and fails when this file differs. -->

How callers talk to a Provenstream host: protocol {protocol}, host version {version}. The engine behind the host has
its own line protocol, [PROTOCOL.md](PROTOCOL.md); this is the outer one, the same whatever carries the bytes. A host
answers `rpc.discover` with this description as an OpenRPC {openrpc} document (methods, params, results, errors), for
tools and generated clients.

## Messages

JSON-RPC 2.0. One request object per message: `{{"jsonrpc": "2.0", "id": ID, "method": NAME, "params": {{...}}}}`,
with `id` a string, an integer or null and `params` an object (absent is `{{}}`). JSON is read strictly: a repeated
key, `NaN` or a lone surrogate is `parse_error`. Batches and notifications (no `id`) are `invalid_request` in protocol
{protocol}, so every request gets exactly one answer. A message over {max_body} bytes (1 MiB) is `invalid_request`. Every error's `data`
holds `"code"`, the name of its row in the answer table below.

| carrier | how | caller |
|---|---|---|
| in process | `Host.open(db, engines).handle(message, auth)`, or `host.command(name, auth=..., **params)` / `host.query(...)` | `Token(t)` or `Operator(principal)` |
| stdio | `provenstream serve --stdio`: one request per line on stdin, one answer per line on stdout, in order | one per session, fixed at launch: `--as PRINCIPAL` or `--token-file FILE` |
| HTTP | `provenstream serve`: `POST /rpc` (always HTTP 200; the outcome is in the body), `GET /healthz` | `Authorization: Bearer TOKEN` |

The answer to a message is the same bytes on every carrier for the same caller. The cases of
[conformance/](conformance/README.md) check a host against this document (`provenstream conform`, on any carrier or
against a host at a URL); a host that passes them is Provenstream-compatible for protocol {protocol}.

## Callers

A token names its caller; no token, or one the host does not know, is `unauthorized`. `Operator(principal)` exists
in process only: whoever holds the database is already the host, and acts as any principal the store knows (as
`--as` does on the command line). `Operator(None)` is the operator as no principal: it may call what needs none.

A principal is an id and its tokens: no kind, no role, no account. Every proof command carries the caller's
`actor_id`: the token's principal (or the operator's), filled in when the caller leaves it out, and refused
`actor_id_must_match_the_token` when it names another.

**Reads.** Reading is unrestricted: any authenticated principal reads any stream (no proof says who reads). A read of a
stream with no rows is refused `stream_must_exist`; `revision.events` on a revision with no engine here is
`revision_must_be_installed`.

**Paging.** `stream.events` and `stream.rows` answer at most `limit` rows (default and most {page}) from seq `from`
(default 0), and `next`: the `from` of the next page, or null at the end. `revision.events` pages the same way across
every stream of a revision, in the host's append order (an event committed later always comes later, whatever its
stream): its `from` and `next` are positions in that order, not seqs, and a caller stores the last `next` it got and
polls from it, as a `stream.events` caller keeps the last seq, getting every later event once. `event` narrows a page
to one event name, so a principal finds the events that name it (`{{"event": "work.asked"}}`, then its own id among
the `preparer_id`s) without being told which streams exist. The host answers from an index kept beside the events,
never by reading streams, and knows no layer's event names.

**Revisions.** A revision is a commit and a package path, so one commit serves all its proofs side by side. Its URL:
`<repo>/commit/<commit>` (or `<repo>#<commit>`, `<repo>@<commit>`) names the repository's root package,
`<repo>/tree/<commit>/<package>` another (`<package>`: `/`-separated segments of `[A-Za-z0-9._-]`, none `.` or `..`).
`revision.describe` and `revisions.list` name a revision by its key: `<commit>`, or `<commit>/<package>`.

## Answers

| `data.code` | JSON-RPC | CLI exit | when | `data` |
|---|---|---|---|---|
{answers}

Every refusal's `data.reason` names the rule broken. The host's own: `stream_must_exist` (a command or a read naming a
stream with no rows), `revision_must_be_installed` (a `stream.open` or `revision.describe` naming a revision with no
engine here), `repository_must_match_the_engine` (a `stream.open` whose URL names another repository than its engine
was built from), `engine_must_implement_the_interface` (its engine does not implement the stream interface),
`actor_id_must_match_the_token`, `idempotency_key_must_match_its_request` (a key reused for another request), and for
`principal.create` `only_the_operator_can_reissue_a_principal` and `principal_must_have_no_token`. Any other reason is
the proof's rule (`ref_must_name_an_earlier_event`, the layer mechanism's, among them). A `stream.open` whose
`proof_revision_url` is a string but no revision URL is refused with the core's own rule,
`revision_url_must_name_a_commit`, the host reading the URL exactly as the core does (it names no engine to ask); a
missing or non-string URL is `invalid_params`. `unavailable` never carries the
failure's text: it is logged under the incident id.

## Host methods

Queries change nothing and are safe to retry; host commands change the host's state, never a stream.

{host}
## Proof commands

Any other dotted name is a proof command: the stream's revision decides whether it exists (`method_not_found`, naming
the revision, if not) and whether to accept it. An accepted command appends exactly one event and answers `{{seq,
event, chain}}`; `chain` is the receipt, the stream's head after this row. A refused one stores nothing. Every proof
command takes an optional `idempotency_key`: a retry by the same caller with the same key answers the first answer,
and an optional `actor_id` (see Callers). Minted fields are fresh ids the host mints, in the event. The commands below
are the core's, which every revision has; a layer adds its own, listed by `rpc.discover`, by `stream.describe` and by
`provenstream -h --proof`.

{proof}
## Versions

This is protocol {protocol} (`x-provenstream-protocol`). Within protocol {protocol} changes are additive only: new
methods, new optional params, new result keys, new refusal reasons. A caller ignores result keys it does not know. A
change to anything else (a code, a message, a param's meaning) is a new protocol. An engine's `describe` says its own
protocol (`"protocol": 2`); a host serves engines of protocol 2 only, listed by `rpc.discover`.
"""


def _params_table(params: List[dict]) -> str:
    if not params:
        return "No params.\n"
    rows = ["| param | | type | note |", "|---|---|---|---|"]
    for p in params:
        sc, brief = p["schema"], _brief(p["schema"])
        said = brief not in ("string", "integer", "string or null", "integer or null")   # the type column says it
        rows.append("| `%s` | %s | %s | %s |" % (p["name"], "required" if p["required"] else "optional", brief,
                                                 "" if said else p.get("description", "")))
    return "\n".join(rows) + "\n"


def markdown(doc: dict) -> str:
    host, proof = [], []
    for m in doc["methods"]:
        if m["x-provenstream-kind"] == protocol.PROOF_COMMAND:
            mint = ", ".join("`%s`" % f for f in m["x-provenstream-minted"])
            ev = m["x-provenstream-event"]
            proof.append("### `%s`\n\nWho may send it: %s.\n\n%s\nEvent `%s`: {%s}. Minted: %s.\n\nRules, in order: "
                         "%s.\n" % (m["name"], m["x-provenstream-who"] or "(not said)", _params_table(m["params"]),
                                    ev["name"], ", ".join(ev["fields"]), mint or "none",
                                    ", ".join(m["x-provenstream-rules"]) or "none"))
        else:
            kind = "A query" if m["x-provenstream-kind"] == protocol.QUERY else "A host command"
            host.append("### `%s`\n\n%s: %s. Caller: %s.\n\n%s\nResult: %s.\n" % (
                m["name"], kind, m["summary"], AUTH_WORDS[m["x-provenstream-auth"]], _params_table(m["params"]),
                _keys(m["result"]["schema"])))
    errs = doc["components"]["errors"]
    answers = ["| `ok` | result | 0 | %s | %s |" % (protocol.ANSWERS["ok"].meaning, protocol.ANSWERS["ok"].data)]
    answers += ["| `%s` | %d | %d | %s | %s |" % (c, e["code"], e["x-provenstream-exit"], e["x-provenstream-meaning"],
                                                  e["x-provenstream-data"]) for c, e in errs.items()]
    from .host import PAGE
    return PROSE.format(protocol=doc["x-provenstream-protocol"], version=doc["info"]["version"],
                        openrpc=doc["openrpc"], max_body=protocol.MAX_BODY, page=PAGE, answers="\n".join(answers),
                        host="\n".join(host), proof="\n".join(proof))


def main(argv: Optional[List[str]] = None) -> int:
    p = argparse.ArgumentParser(prog="python3 -m provenstream.openrpc",
                                description="the OpenRPC document of the host with one engine, or HOST-PROTOCOL.md")
    p.add_argument("--engine", required=True, help="an engine (the core engine, for HOST-PROTOCOL.md)")
    p.add_argument("--markdown", action="store_true", help="HOST-PROTOCOL.md instead of the JSON document")
    a = p.parse_args(argv)
    from .engine import Engine
    e = Engine([a.engine])
    e.start()
    try:
        d = e.describe()
    finally:
        e.stop()
    # named by role, not by commit: the document of the code, the same at every commit that does not change it
    doc = document({"core": d})
    sys.stdout.write(markdown(doc) if a.markdown else json.dumps(doc, indent=2, ensure_ascii=False) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
