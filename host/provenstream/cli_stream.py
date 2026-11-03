# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The commands about streams: `stream open|close|head|events|use|alias`, `revision list|describe`, `api` and
`principal create`, each also under its flat name (`open`, `close`, `head`, ..., `revisions`, `call`), which builds
the same arguments and runs the same function (cli.py).

Every call goes through the mode's carrier (`target`): `client.Remote` or `mode.Local`, one `handle(method, params)`.
Stream arguments are resolved first (`context.resolve_stream`: a UUID, an alias, or a known id's suffix), and `head`,
`events` and `verify` fall back to the current stream (`context.py`).

A proof command (`stream open`, `stream close`, and `api` with any name that is not a host method) is checked against
its revision's description before it is sent (`proofs.check`: method_not_found or invalid_params, exit 5, nothing
sent): the description of `--proof` when it is given, else of the revision the stream's first event names (or, for
`stream.open`, the one its URL names), from the cache or the host's `revision.describe`. Its `actor_id` is filled in
from the signed-in principal unless the caller gave one (`actor`): `--as` in local mode; in remote mode the stored
login's principal, or, for a token from `--token-file` or `PROVENSTREAM_TOKEN`, the host's `whoami`.

`stream open` takes its proof URL from PROOF_URL; else from the project file's or the config's `proof_revision_url`;
else from git (`--from-git` skips the configured one). A PROOF_URL of 7 or more hex digits alone is a revision prefix
among those served, its URL the revision's own repository (`revision.describe`) and commit. The stream opened becomes
the current one (unless `--no-use`), in the project file if there is one, else the user config, and `--alias NAME`
names it there. Neither is a reason to fail: the stream is open whatever happens to them, so a failure to record
either is a warning.

`close` is final, so it never acts on the current stream implicitly and it asks first. On a terminal (stdin and
stderr) it shows the stream (id, alias, proof URL, opener, from `stream.get`) and closes only when the answer is the
alias, the full id or its last 8 characters; a wrong answer sends nothing (exit 1). Elsewhere it needs `--yes`, or
`--confirm STREAM` naming the same stream (else exit 2, nothing sent). `--dry-run` reads the stream and the caller
(`whoami`) and reports whether a close would be accepted (the caller is the opener and the stream is open), sending
nothing.

`principal create` asks the host (`principal.create`) for a new principal as the caller (remote: the token's; local:
`--as`, or the operator) and prints only its `principal_id`: the token goes to `--token-file PATH` (created 0600, never
over an existing file) or is stored for the host under `--save-as NAME` (remote only; `--principal NAME` then sends it).
It is never printed.
"""
from __future__ import annotations
import contextlib, json, os, sys
from typing import Any, Dict, Optional

from . import auth, client, config, context, ids, mode, proofs, protocol
from .client import ClientError, EXIT_PARAMS
from .revisions import revision_of_url, revision_url, split_key


def target(a):
    """The mode's carrier, an object with `handle(method, params)`: the host over JSON-RPC, or the database in
    process as `--as`."""
    if a.R.mode == "remote":
        c = auth.remote_choice(a)
        a._signed_in = c.principal                    # the stored login's principal, when the token is a stored one
        return client.Remote(a.R.base_url, c.token)
    from .cli import _engines
    return mode.Local(a.R.db, _engines(a, False), a.actor)


def actor(a, t) -> Optional[str]:
    """The signed-in principal: `--as` in local mode; remote, the stored login's principal, else the host's whoami."""
    if a.R.mode != "remote":
        return a.actor
    p = getattr(a, "_signed_in", None)
    if not p:
        p = a._signed_in = t.handle("whoami", {}).get("principal_id")
    return p


def is_proof_command(method: str) -> bool:
    from .host import METHODS
    return protocol.classify(method, METHODS) == protocol.PROOF_COMMAND


def description_for(a, t, method: str, params: Dict[str, Any]) -> Optional[dict]:
    """The description a proof command is checked against: `--proof`'s, else its stream's revision's (for
    `stream.open`, the revision its URL names). None for a `stream.open` whose URL is no revision URL: there is no
    revision to describe, and the host refuses it with the core's rule (revision_url_must_name_a_commit). A host that
    cannot be asked for it is `Unavailable` (exit 6); a stream it does not have is its refusal (stream_must_exist)."""
    if getattr(a, "proof", None):
        return proofs.resolve(a.proof, lambda: contextlib.nullcontext(t))
    if method == "stream.open":
        url = params.get("proof_revision_url")
        if not isinstance(url, str):
            raise ClientError(EXIT_PARAMS, "invalid params: stream.open: proof_revision_url: required, a string (a "
                                           "revision URL); nothing sent")
        key = revision_of_url(url)
        if key is None:
            return None
        what = "revision %s" % key
    else:
        s = params.get("stream_id")
        if not (isinstance(s, str) and ids.CANONICAL_ID.fullmatch(s)):
            raise ClientError(EXIT_PARAMS, "invalid params: %s: stream_id: %s; nothing sent" % (
                method, "required: a proof command names its stream (or check it against --proof)" if s is None
                else "expected a canonical lowercase UUID"))
        what = "stream %s's revision" % s
        try:
            first = t.handle("stream.events", {"stream_id": s, "limit": 1})["events"]
        except ClientError as x:
            if x.exit_code in (client.EXIT_UNAUTHORIZED, client.EXIT_UNAVAILABLE):
                raise proofs.unreachable(what, x.message)
            raise
        key = revision_of_url(first[0].get("proof_revision_url")) if first else None
        if key is None:
            raise proofs.Unavailable("unavailable: stream %s names no revision a description can be had for" % s)
    try:
        return proofs.description_of(key, t)
    except ClientError as x:
        if x.exit_code in (client.EXIT_UNAUTHORIZED, client.EXIT_UNAVAILABLE):
            raise proofs.unreachable(what, x.message)
        raise


def send(a, t, method: str, params: Dict[str, Any]) -> Any:
    """A proof command: checked against its description, its actor_id filled in, then sent."""
    desc = description_for(a, t, method, params)
    if desc is not None:
        proofs.check(desc, method, params)
    if "actor_id" not in params:
        who = actor(a, t)
        if who:
            params = dict(params, actor_id=who)
    return t.handle(method, params)


def pages(t, method: str, params, key: str):
    """Every page of a paged query (`stream.events`, `stream.rows`), following `next` from `from`, as one answer."""
    out = t.handle(method, params)
    while out.get("next") is not None:
        more = t.handle(method, dict(params, **{"from": out["next"]}))
        out[key] += more[key]
        out["next"] = more.get("next")
    return out


def field(a) -> Optional[str]:
    return getattr(a, "field", None)


def do(a, method: str, params, key: Optional[str] = None) -> int:
    """One call (every page of it, for a paged query's `key`), its result printed (or its `-q` field)."""
    with target(a) as t:
        client.show(pages(t, method, params, key) if key else t.handle(method, params), field(a))
    return 0


def _tty() -> bool:
    return sys.stderr is not None and sys.stderr.isatty()


def _warn(msg: str) -> None:
    print("provenstream: warning: %s" % msg, file=sys.stderr)


# -- calls ----------------------------------------------------------------------------------------------------------

def cmd_call(a) -> int:
    try:
        params = json.loads(a.params) if a.params else {}
    except ValueError as x:
        raise ClientError(EXIT_PARAMS, "invalid params: JSON_PARAMS is not JSON: %s" % x)
    if not isinstance(params, dict):
        raise ClientError(EXIT_PARAMS, "invalid params: JSON_PARAMS must be an object")
    for f in getattr(a, "fields", None) or []:
        k, eq, v = f.partition("=")
        if not eq or not k:
            raise ClientError(EXIT_PARAMS, "invalid params: -f %r: expected key=value" % f)
        try:
            params[k] = json.loads(v)            # a number, true, null, an object ... as JSON; anything else a string
        except ValueError:
            params[k] = v
    if not is_proof_command(a.method):
        if getattr(a, "proof", None):
            raise ClientError(EXIT_PARAMS, "invalid params: --proof checks a proof command, and %s is the host's "
                                           "method; nothing sent" % a.method)
        return do(a, a.method, params)
    with target(a) as t:
        client.show(send(a, t, a.method, params), field(a))
    return 0


def cmd_revisions(a) -> int:
    return do(a, "revisions.list", {})


def _revision(t, prefix: str) -> str:
    return context.resolve_revision(prefix, proofs.served(t))


def cmd_revision_describe(a) -> int:
    with target(a) as t:
        client.show(t.handle("revision.describe", {"revision": _revision(t, a.revision)}), field(a))
    return 0


# -- reads ----------------------------------------------------------------------------------------------------------

def cmd_head(a) -> int:
    return do(a, "stream.head", {"stream_id": context.stream_or_current(a.stream, "head")})


def cmd_events(a) -> int:
    p: Dict[str, Any] = {"stream_id": context.stream_or_current(a.stream, "events")}
    if a.start:
        p["from"] = a.start
    return do(a, "stream.events", p, "events")


# -- principals -----------------------------------------------------------------------------------------------------

def write_token_file(path: str, token: str) -> None:
    """The token to a new file, readable by its owner only (0600); never over an existing file."""
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, "w", encoding="utf-8") as f:
        f.write(token + "\n")


def token_file_free(path: Optional[str]) -> None:
    """Before a token is asked for: its file must be new, so that writing it cannot fail on an existing one."""
    if path and os.path.lexists(path):
        raise ClientError(1, "%s exists: a token file is never overwritten; nothing sent" % path)


def cmd_principal_create(a) -> int:
    if bool(a.token_out) == bool(a.save_as):
        raise ClientError(2, "usage: principal create needs --token-file PATH or --save-as NAME (one of them): its "
                             "token is never printed")
    if a.save_as and a.R.mode != "remote":
        raise ClientError(client.EXIT_MODE, "mode: --save-as stores the token for a host, but the mode is local "
                                            "(decided by %s): use --token-file PATH" % a.R.why)
    if a.save_as:
        auth.check_name(a.save_as)
    token_file_free(a.token_out)
    with target(a) as t:
        got = t.handle("principal.create", {})
    p, tok = got.get("principal_id"), got.get("token")
    if not (isinstance(p, str) and isinstance(tok, str)):
        raise ClientError(client.EXIT_UNAVAILABLE, "unavailable: the host's principal.create named no principal")
    if a.token_out:
        write_token_file(a.token_out, tok)
    else:
        auth.put(config.normalize_host(a.R.base_url), p, tok, auth.default_storage(), make_active=False,
                 name=a.save_as)
    client.show({"principal_id": p}, field(a) or "principal_id")
    return 0


# -- open -----------------------------------------------------------------------------------------------------------

def _proof_url(a, t) -> str:
    if a.proof_url and a.from_git:
        raise ClientError(2, "usage: PROOF_URL and --from-git both name the proof; give one")
    if a.proof_url:
        if not context.looks_like_revision(a.proof_url):
            return a.proof_url
        rev = _revision(t, a.proof_url)
        repo = proofs.description_of(rev, t).get("repo")
        if not isinstance(repo, str) or not repo or repo == "unknown":
            raise ClientError(EXIT_PARAMS, "invalid params: revision %s does not name its repository; give the full "
                                           "PROOF_URL" % rev)
        url = revision_url(repo, *split_key(rev))
        print("proof URL: %s" % url, file=sys.stderr)
        return url
    if not a.from_git:
        pr = context.load_project()
        v, _ = config.effective("proof_revision_url", None, project=(pr.path, pr.data))
        if v:
            return v
    url = context.proof_url_from_git()
    print("proof URL from git: %s" % url, file=sys.stderr)
    return url


def cmd_open(a) -> int:
    if a.alias:
        context.check_alias(a.alias)                       # before anything is opened
    with target(a) as t:
        p = {"proof_revision_url": _proof_url(a, t)}
        if a.meta is not None:
            p["meta"] = a.meta
        res = send(a, t, "stream.open", p)
    s = res.get("event", {}).get("stream_id") if isinstance(res, dict) else None
    if isinstance(s, str):
        try:
            context.remember(s)
            place = context.Place()
            if not a.no_use or a.alias:
                data = place.read()
                if not a.no_use:
                    data["stream"] = s
                if a.alias:
                    data["aliases"] = dict(data.get("aliases") or {}, **{a.alias: s})
                place.write(data)
            if _tty():
                print("stream: %s%s%s" % (context.label(s), "" if a.no_use else ", now the current stream",
                                          ", in %s" % place.name if not a.no_use or a.alias else ""), file=sys.stderr)
        except (OSError, ClientError) as x:
            _warn("the stream is open, but it could not be recorded as current: %s" % getattr(x, "message", x))
    client.show(res, field(a))
    return 0


# -- close ----------------------------------------------------------------------------------------------------------

def summary(stream: str, view: Dict[str, Any], alias: Optional[str]) -> str:
    return "\n".join(["close stream %s" % stream,
                      "  alias:   %s" % (alias or "(none)"),
                      "  proof:   %s" % view.get("proof_revision_url", "?"),
                      "  opener:  %s" % (view.get("opener_id") or "?")] +
                     (["  closed:  already (the host will refuse)"] if view.get("closed") else []) +
                     ["Closing is final: nothing can be appended to the stream after it."])


def answer_matches(answer: str, stream: str, alias: Optional[str]) -> bool:
    a = answer.strip()
    return bool(a) and (a == alias or context.canonical(a) == stream or a.lower() == stream[-8:])


def confirm(stream: str, view: Dict[str, Any], alias: Optional[str], read=None, write=None) -> bool:
    """Show the stream on `write` (stderr) and read one answer from `read` (stdin): True when it names the stream."""
    write = write or sys.stderr
    write.write(summary(stream, view, alias) + "\n")
    write.write("type %sthe full id or its last 8 characters (%s) to close it: "
                % ("its alias (%s), " % alias if alias else "", stream[-8:]))
    write.flush()
    line = (read or sys.stdin).readline()
    return answer_matches(line, stream, alias)


def cmd_close(a) -> int:
    s = context.resolve_stream(a.stream)
    alias = context.alias_of(s)
    if a.confirm is not None and context.resolve_stream(a.confirm) != s:
        raise ClientError(1, "not closed: --confirm %s names another stream than %s; nothing sent" % (a.confirm, s))
    interactive = sys.stdin is not None and sys.stdin.isatty() and _tty()
    if not (a.dry_run or a.yes or a.confirm is not None or interactive):
        raise ClientError(2, "close is final and asks for confirmation, and there is no terminal to ask on: pass "
                             "--yes, or --confirm STREAM (the same stream again), or --dry-run to see what it would do")
    with target(a) as t:
        if a.dry_run:
            view = t.handle("stream.get", {"stream_id": s})
            caller = actor(a, t)
            opener = view.get("opener_id")
            is_opener = caller is not None and caller == opener
            client.show({"stream_id": s, "alias": alias, "proof_revision_url": view.get("proof_revision_url"),
                         "opener_id": opener, "caller_id": caller, "caller_is_opener": is_opener,
                         "closed": bool(view.get("closed")), "would_close": is_opener and not view.get("closed"),
                         "sent": False}, field(a))
            return 0
        params: Dict[str, Any] = {"stream_id": s}
        if a.meta is not None:
            params["meta"] = a.meta
        proofs.check(description_for(a, t, "stream.close", params), "stream.close", params)
        if not (a.yes or a.confirm is not None):
            if not confirm(s, t.handle("stream.get", {"stream_id": s}), alias):
                raise ClientError(1, "not closed: the answer does not name %s; nothing sent" % s)
        client.show(send(a, t, "stream.close", params), field(a))
    return 0


# -- the current stream and aliases (files only) --------------------------------------------------------------------

def cmd_use(a) -> int:
    if a.view:
        if a.stream or a.unset:
            raise ClientError(2, "usage: stream use --view shows the current stream; it takes no STREAM or --unset")
        given, src = context.current()
        s = context.resolve_stream(given) if given else None
        client.show({"stream": s, "alias": context.alias_of(s) if s else None, "from": src,
                     "project": context.load_project().path}, field(a))
        return 0
    place = context.Place(a.project)
    if a.unset:
        if a.stream:
            raise ClientError(2, "usage: stream use --unset takes no STREAM")
        data = place.read()
        if "stream" not in data:
            raise ClientError(1, "no current stream in %s" % place.name)
        del data["stream"]
        place.write(data)
        print("current stream unset in %s" % place.name)
        return 0
    if not a.stream:
        raise ClientError(2, "usage: stream use STREAM (an id, an alias or a suffix), or --unset, or --view")
    s = context.resolve_stream(a.stream)
    context.use(s, place)
    context.remember(s)
    print("current stream: %s, in %s" % (context.label(s), place.name))
    if os.environ.get("PROVENSTREAM_STREAM"):
        _warn("PROVENSTREAM_STREAM is set, and wins over %s until it is unset" % place.name)
    return 0


def cmd_alias(a) -> int:
    if a.list:
        if a.name or a.stream or a.remove:
            raise ClientError(2, "usage: stream alias --list takes nothing else")
        client.show({n: s for n, s, _ in context.aliases()}, field(a))
        return 0
    if a.remove:
        if a.name or a.stream:
            raise ClientError(2, "usage: stream alias --remove NAME takes nothing else")
        pr = context.load_project()
        if a.remove in (pr.data.get("aliases") or {}):
            data = dict(pr.data)
            data["aliases"] = {n: s for n, s in data["aliases"].items() if n != a.remove}
            context.save_project(pr.path, data)
            print("alias %s removed from %s" % (a.remove, pr.path))
        elif config.unset("aliases." + a.remove):
            print("alias %s removed from %s" % (a.remove, config.path()))
        else:
            raise ClientError(1, "no alias %s (in %s)" % (a.remove, " or ".join(p for p in (pr.path, config.path())
                                                                                 if p)))
        return 0
    if not (a.name and a.stream):
        raise ClientError(2, "usage: stream alias NAME STREAM, or --list, or --remove NAME")
    context.check_alias(a.name)
    s = context.resolve_stream(a.stream)
    place = context.Place(a.project)
    data = place.read()
    data["aliases"] = dict(data.get("aliases") or {}, **{a.name: s})
    place.write(data)
    print("alias %s = %s, in %s" % (a.name, s, place.name))
    return 0
