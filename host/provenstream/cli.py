# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The `provenstream` command line: a tree of nouns and actions, each command in a mode, the flat verbs kept as aliases.

Mode, once per invocation (`mode.py`): `PROVENSTREAM_MODE` (`remote` or `local`) if set; else local if `--db` or
`PROVENSTREAM_DATABASE_URL`; else local for a local-only command when no base URL is named (the configured
`default_host`, or a project file's `host`, does not name one); else remote. Remote: JSON-RPC to `--base-url` (else
`PROVENSTREAM_BASE_URL`, else the project file's `host`, else the configured `default_host`, else the local host at
http://127.0.0.1:8080, where `provenstream serve` listens with no flags) as the token's principal (`--token-file`,
else `PROVENSTREAM_TOKEN`, else the token `provenstream login` stored for that host: its active principal's, or
`--principal P`'s). Local: the database, in process, with the engines of `--engines` (else `PROVENSTREAM_ENGINES`,
else the configured `local.engines`); calls act as `--as PRINCIPAL`. Mixing the modes' settings is an error (exit 8).
Settings resolve flag > env > project file > config > default (`config.py`, `context.py`).

The tree (`COMMANDS` lists it with each flat alias; `help` prints it). A tree command and its alias build the same
arguments and set the same `cmd`, so they are one command, with one mode and one output:

    stream open [PROOF_URL] [--meta M] [--no-use] [--alias NAME] [--from-git]     (open)
    stream close STREAM [--yes | --confirm STREAM | --dry-run] [--meta M]         (close)
    stream head [STREAM]   stream events [STREAM] [--from N]   stream verify [STREAM] ...   (head, events, verify)
    stream use STREAM [--project] | --unset | --view    stream alias NAME STREAM | --list | --remove NAME
    revision list (revisions)   revision describe REV   api METHOD [JSON] [-f key=value ...] [--proof P] (call)
    principal create [--token-file PATH | --save-as NAME]   status (mode)
    host serve|replay|export|import|principal create|token rotate (serve, replay, ...)
    engine init|check|build|install|describe (init, check, ...)

The stream commands are `cli_stream.py`: the current stream that head, events and verify fall back to, aliases, short
ids and the proof URL from git are `context.py`; close asks for a confirmation. A proof command is checked against its
revision's description before it is sent (`proofs.py`), and `-h --proof PROOF` prints that description as Markdown.
`-q PATH` on every command that prints a JSON result prints the value at PATH alone (`client.pick`).

Remote only (exit 8 in local mode): `auth login [--base-url URL] [--token-file F] [--storage keyring|file]
[--default]` (the token on stdin, or a prompt that does not echo it; never an argument), `auth logout [--principal P |
--all]`, `auth status [--json]`, `auth rotate [--principal P]` (`auth.py`); `login`, `logout` and `whoami` are
`auth login`, `auth logout` and `auth status`.

Local only (exit 7 in remote mode): `serve [--stdio (--as P | --token-file F)]`, `host principal create [--id ID]
[--token-file PATH]`, `token rotate PRINCIPAL`, `replay [--head STREAM:SEQ:HEX ...]`, `export FILE`, `import FILE`.
With no database and no host named they use the default database, the SQLite file ~/.provenstream/streams.db.

One code path per command: a command that calls the host builds its params and calls `handle(method, params)` on the
mode's carrier, `client.Remote` (JSON-RPC over HTTP) or `mode.Local` (`Host.handle` in process, as `Operator(--as)`),
and prints the result or exits with the answer table's code. `principal create` (either mode), `host principal create`
and `token rotate` are the host commands `principal.create` and `token.rotate`. Only operator tooling that reads every stream (`replay`,
`export`, `import`, `verify` on a database) reads the store itself.

A throwaway host of its own, or the host named: `conform [--target inprocess|stdio|http | --compare | --base-url URL
--tokens FILE --revision-url URL]`, the conformance suite (conformance/, `conform.py`).

Files only: `init NAME`, `check [PROJECT]`, `build --repo R --commit C --out DIR [--package P]`, `install BUILD_DIR`,
`describe ENGINE`, `config get KEY | set KEY VALUE | unset KEY | list`, `stream use`, `stream alias`, `help`.

Exit codes: 0 done, 1 a check or verify failed (or a confirmation did not match), 2 usage (and close with no
terminal to confirm on), 3 unauthorized, 4 refused (the rule is printed), 5 method not found or invalid params,
6 unavailable (and no description of a proof to be had), 7 needs local mode, 8 mode misconfigured.
"""
from __future__ import annotations
import argparse, json, os, shutil, sys, tempfile
from typing import List, Optional

from . import __version__, auth, build as buildmod, chain, cli_stream, client, config, context, mode, project, proofs, \
    scaffold, wire
from .engine import Engine, EngineFailure, EngineRefusedLog
from .revisions import load_map, revision_of_url, split_key


def _err(msg: str) -> int:
    print("provenstream: %s" % msg, file=sys.stderr)
    return 1


def cmd_init(a) -> int:
    d = scaffold.init(a.name, a.dir, a.core, a.core_git, a.core_rev)
    print("init: %s (check it: provenstream check %s)" % (d, d))
    return 0


def cmd_check(a) -> int:
    try:
        project.check(a.project)
    except project.CheckFailed as x:
        return _err("check FAILED: %s" % x)
    print("check: all passed")
    return 0


def cmd_build(a) -> int:
    try:
        m = buildmod.build_engine(a.repo, a.commit, a.out, a.package, a.repo_url, a.reuse_lake)
    except buildmod.BuildFailed as x:
        return _err("build FAILED: %s" % x)
    out = {k: m[k] for k in ("revision", "proof_url", "engine")}
    _emit(a, out, lambda: print(json.dumps(out, indent=2)))
    return 0


def cmd_install(a) -> int:
    try:
        buildmod.install(a.build_dir, _engines(a, True))
    except (buildmod.BuildFailed, project.CheckFailed, ValueError) as x:
        return _err("install FAILED: %s" % x)
    return 0


def _emit(a, result, default) -> None:
    """`default()` prints a result as the command always has; with `-q PATH`, the value at that path instead."""
    if getattr(a, "field", None) is not None:
        client.show(result, a.field)
    else:
        default()


def cmd_describe(a) -> int:
    command = [os.path.abspath(a.engine)]
    if not os.path.exists(a.engine) and context.looks_like_revision(a.engine):
        edir = _engines(a, False)                       # a revision prefix, among the engines directory's
        if not edir:
            return _err("no file %s, and no engines directory to find a revision in (--engines)" % a.engine)
        m = load_map(os.path.join(edir, "revisions.json"))
        command = m[context.resolve_revision(a.engine, m)]
    e = Engine(command)
    e.start()
    try:
        d = e.describe()
    finally:
        e.stop()
    _emit(a, d, lambda: print(json.dumps(d, indent=2, sort_keys=True)))
    return 0


DB_HELP = ("the database (local mode): sqlite:///abs/path.db or a path ending .db, or Postgres (the postgres extra) as "
           "a libpq connection string (postgresql://... or key=value; postgresql:// alone for libpq's own settings); "
           "default PROVENSTREAM_DATABASE_URL, else ~/.provenstream/streams.db")


def _engines(a, required: bool) -> Optional[str]:
    d = config.effective("local.engines", getattr(a, "engines", None))[0]
    if required and not d:
        raise client.ClientError(client.EXIT_PARAMS, "invalid params: %s needs --engines DIR (or PROVENSTREAM_ENGINES, "
                                 "or provenstream config set local.engines DIR)" % a.cmd)
    return d


def _store(target: Optional[str]):
    from .store import open_store
    return open_store(target if target is not None else mode.default_db())


def cmd_serve(a) -> int:
    from .host import Host, Operator, Token
    edir = _engines(a, True)
    engines = load_map(os.path.join(edir, "revisions.json"))
    if not engines:
        return _err("%s/revisions.json lists no engines (provenstream install)" % edir)
    if not a.stdio and (a.actor or a.token_file):
        raise client.ClientError(client.EXIT_PARAMS, "invalid params: --as and --token-file name a stdio session's "
                                                     "principal (serve --stdio); over HTTP each request's token does")
    if a.stdio and bool(a.actor) == bool(a.token_file):
        raise client.ClientError(client.EXIT_PARAMS, "invalid params: serve --stdio is one principal's session: name "
                                                     "it with --as PRINCIPAL or --token-file FILE (one of them)")
    auth = (Operator(a.actor) if a.actor else Token(client.token(a.token_file, None))) if a.stdio else None
    host = Host.open(a.R.db, engines, max_streams=a.max_streams, idle_timeout=a.idle_timeout)
    try:
        say = "serve: %d revisions (%s), engines started on demand, stopped after %ss idle" % (
            len(engines), " ".join(sorted(engines)), a.idle_timeout)
        if a.stdio:
            from . import stdio
            if a.actor and not host.store.known(a.actor):
                raise client.ClientError(client.EXIT_UNAUTHORIZED, "unauthorized: no such principal in this store: "
                                         "%s" % a.actor)
            out, sys.stdout = sys.stdout, sys.stderr      # stdout carries answers only: stray prints go to stderr
            try:
                print(say + "; stdio, one request per line", file=sys.stderr, flush=True)
                return stdio.serve(host, auth, sys.stdin.buffer, out.buffer)
            finally:
                sys.stdout = out
        import uvicorn
        from .api import make_app
        print(say, flush=True)
        uvicorn.run(make_app(host), host=a.host, port=a.port, log_level="warning")
        return 0
    finally:
        host.close()


def cmd_host_principal(a) -> int:
    """The operator's `principal.create` (local mode, no token): with --token-file the token goes to the file (0600)
    and only {principal_id} is printed; without it, {principal_id, token}."""
    params = {}
    if a.id is not None:
        params["principal_id"] = a.id
    cli_stream.token_file_free(a.token_out)
    with mode.Local(a.R.db, _engines(a, False), None) as t:
        got = t.handle("principal.create", params)
    if a.token_out:
        cli_stream.write_token_file(a.token_out, got.pop("token"))
    _emit(a, got, lambda: print(wire.dumps(got)))
    return 0


def cmd_token(a) -> int:
    with mode.Local(a.R.db, None, a.principal) as t:
        print(t.handle("token.rotate")["token"])
    return 0


def cmd_export(a) -> int:
    store = _store(a.R.db)
    try:
        n = store.export(a.file)
    finally:
        store.close()
    print("export: %d rows -> %s (tokens are not exported: issue them again where the file is imported)" % (n, a.file))
    return 0


def cmd_import(a) -> int:
    from .store import ImportRefused
    store = _store(a.R.db)
    try:
        got = store.import_export(a.file)
    except ImportRefused as x:
        return _err("import REFUSED, nothing stored: %s" % x)
    finally:
        store.close()
    print("import: %d streams, %d rows, every chain recomputed and matching the exported heads; tokens are not in an "
          "export: issue principals' tokens on this store (provenstream principal create)"
          % (len(got), sum(got.values())))
    return 0


def _held(specs: List[str], with_stream: bool):
    """Heads a client kept: `SEQ:HEX` (or `STREAM:SEQ:HEX` with `with_stream`), and for verify a bare `HEX` for the
    stream's last row. Answers ({seq: hex} or {stream: {seq: hex}}, last hex or None)."""
    held: dict = {}
    last = None
    for spec in specs or []:
        parts = spec.split(":")
        try:
            if with_stream and len(parts) == 3:
                held.setdefault(parts[0], {})[int(parts[1])] = parts[2]
            elif not with_stream and len(parts) == 2:
                held[int(parts[0])] = parts[1]
            elif not with_stream and len(parts) == 1:
                last = parts[0]
            else:
                raise ValueError
        except ValueError:
            raise SystemExit("provenstream: --head %r: expected %s" % (spec, "STREAM:SEQ:HEX" if with_stream
                                                                       else "SEQ:HEX or HEX"))
    return held, last


def cmd_replay(a) -> int:
    from .host import Host
    held, _ = _held(a.head, True)
    host = Host.open(a.R.db, _engines(a, True))      # the operator's replay reads the store itself, every stream
    try:
        r = host.service.check_all(held)
    finally:
        host.close()
    print("replay: %d streams, %d events, %d snapshots; does not replay: %s; other revisions (not replayed): %s"
          % (r["streams"], r["events"], r["snapshots"], " ".join(r["bad_streams"]) or "none",
             " ".join(r["other_revision"]) or "none"))
    for b in r["bad_chains"]:
        print("replay: stream %s: CHAIN BROKEN: %s" % (b["stream"], b["detail"]))
    if not r["bad_chains"]:
        print("replay: every stream's commitments and hash chain recompute from its rows")
    return 0 if not r["bad_streams"] and not r["bad_chains"] else 1


def _rows(a) -> List[chain.Row]:
    """A stream's stored rows, with their meta salts and chain heads, from a file, a host, or a database."""
    if a.rows:
        out, seen = [], set()
        for line in open(a.rows, encoding="utf-8"):
            if line.strip():
                r = wire.loads(line)
                if isinstance(r, dict) and "provenstream_export" in r:
                    continue                                    # an export's header (store.export)
                seen.add(r.get("stream_id"))
                if a.stream is None or r.get("stream_id") == a.stream:
                    # a row as `stream.rows` answers it (request and event as stored JSON text) or as objects
                    out.append(chain.row_from_json(r))
        if a.stream is None and len(seen) > 1:
            raise client.ClientError(client.EXIT_PARAMS, "invalid params: %s holds %d streams: name one with --stream"
                                     % (a.rows, len(seen)))
        return out
    if a.R.mode == "remote":
        with _target(a) as t:
            res = _pages(t, "stream.rows", {"stream_id": a.stream}, "rows")
        return [chain.row_from_json(r) for r in res["rows"]]
    store = _store(a.R.db)
    try:
        return [chain.Row(seq, wire.loads(req), wire.loads(ev), salt, ch)
                for seq, req, ev, salt, ch in store.read_chained(a.stream)]
    finally:
        store.close()


def cmd_verify(a) -> int:
    a.engines = a.engines or (None if a.engine or a.repo else config.effective("local.engines", None)[0])
    if not (a.engine or a.engines or a.repo):
        raise client.ClientError(client.EXIT_PARAMS, "invalid params: verify needs --engine, --engines (or "
                                 "PROVENSTREAM_ENGINES, or the configured local.engines) or --repo")
    a.stream = getattr(a, "stream_arg", None) or a.stream
    if a.rows:
        a.stream = context.resolve_stream(a.stream) if a.stream else None
    else:
        a.stream = context.stream_or_current(a.stream, "verify", how="--stream S, or --rows FILE")
    rows = _rows(a)
    if not rows:
        return _err("no rows")
    stream = rows[0].event.get("stream_id")
    revision = revision_of_url(rows[0].event.get("proof_revision_url"))
    if revision is None:
        return _err("row 0 is not an opening naming a revision")
    held, last = _held(a.head, False)
    rep = chain.verify(stream, rows, held, last)
    if not rep.ok:
        print("verify: stream %s: CHAIN BROKEN: %s" % (stream, rep.detail))
        return 1
    print("verify: stream %s: commitments and hash chain recompute from the rows: %s%s"
          % (stream, rep.detail, " (and match %d held heads)" % (len(held) + (last is not None)) if held or last else ""))
    if rep.erased:
        print("verify: stream %s: meta erased at seq %s: those rows' content can no longer be checked, and an engine "
              "cannot replay them; engine replay covers the rows before seq %d"
              % (stream, " ".join(str(x) for x in rep.erased), rep.erased[0]))
        rows = rows[:rep.erased[0]]
        if not rows:
            return 0
    engine_rows = [(r.seq, wire.dumps(r.request), wire.dumps(r.event)) for r in rows]
    tmp = None
    try:
        if a.engine:
            command = [os.path.abspath(a.engine)]
        elif a.engines:
            m = load_map(os.path.join(a.engines, "revisions.json"))
            if revision not in m:
                return _err("no engine of revision %s in %s" % (revision, a.engines))
            command = m[revision]
        else:
            tmp = tempfile.mkdtemp(prefix="provenstream-verify-")
            out = os.path.join(tmp, "build")
            commit, package = split_key(revision)
            if a.package is not None and buildmod.package_path(a.package) != package:
                return _err("--package %s: the stream names package %s" % (a.package, package or "(the root)"))
            buildmod.build_engine(a.repo, commit, out, package or ".", reuse_lake=a.reuse_lake)
            command = [os.path.join(out, "engine")]
        e = Engine(command)
        e.start()
        try:
            got = e.revision_key()
            if got != revision:
                return _err("the engine reports revision %s; the stream names %s" % (got, revision))
            ans = e.check(stream, engine_rows)
        except EngineRefusedLog as x:
            print("verify: stream %s DOES NOT REPLAY through revision %s: %s" % (stream, revision, x))
            return 1
        finally:
            e.stop()
        print("verify: stream %s: %d rows replay through the engine of revision %s (every stored request accepted, "
              "giving exactly its stored event)" % (stream, ans["length"], revision))
        return 0
    except (buildmod.BuildFailed, EngineFailure) as x:
        return _err("verify FAILED: %s" % x)
    finally:
        if tmp:
            shutil.rmtree(tmp, ignore_errors=True)


_target, _pages, _do = cli_stream.target, cli_stream.pages, cli_stream.do


def cmd_mode(a) -> int:
    r = a.R
    out = {"mode": r.mode, "decided_by": r.why}
    if r.mode == "remote":
        out["target"] = mode.redact(r.base_url)
        out["host_from"] = r.host_from
        try:
            c = auth.token_for(r.base_url, a.token_file, a.token, a.use_principal, warn=False)
            tok, out["token_source"] = c.token, c.source
            if c.principal:
                out["stored_principal"] = c.principal
        except auth.InsecureFile:
            raise
        except client.ClientError as x:
            tok, out["token_source"], out["token_error"] = None, "none", x.message
        out["token"] = "set" if tok else "not set"
        if tok:
            try:
                out["principal"] = client.Remote(r.base_url, tok).handle("whoami")
            except client.ClientError as x:
                out["principal"] = None
                out["principal_unknown"] = x.message
    else:
        from .store import is_sqlite
        out["store"] = "sqlite" if is_sqlite(r.db) else "postgres"
        out["target"] = (mode.redact(r.db) if r.db not in mode.LIBPQ_ENV
                         else "libpq's own environment (PG* variables, ~/.pgpass)")
        out["engines"] = _engines(a, False)
    if getattr(a, "field", None) is not None:
        client.show(out, a.field)
    elif a.json:
        print(json.dumps(out, sort_keys=True))
    else:
        for k in ("mode", "decided_by", "store", "target", "host_from", "token", "token_source", "stored_principal",
                  "token_error", "principal", "principal_unknown", "engines"):
            if k in out:
                v = out[k]
                print("%-17s %s" % (k.replace("_", " ") + ":", json.dumps(v) if isinstance(v, dict) else v))
    return 0




# The command tree, each with its flat alias (the command line before the tree, kept as it was), its mode (remote: a
# host; local: a database; either: whichever the mode resolves to; self: a throwaway host of its own, or the host it
# names; files: no host, no database), and what it does. `cmd` (the flat name) is what every leaf sets, so a tree
# command and its alias are one command: one mode, one function, one output.
COMMANDS = [
    ("stream open [PROOF_URL]", "open", "either", "open a stream (PROOF_URL, else configured, else git HEAD)"),
    ("stream close STREAM", "close", "either", "close a stream, finally, after a confirmation"),
    ("stream head [STREAM]", "head", "either", "a stream's length and chain head"),
    ("stream events [STREAM]", "events", "either", "a stream's events, each with its seq and chain head"),
    ("stream verify [STREAM]", "verify", "either", "recompute a stream's chain and replay its rows"),
    ("stream use STREAM", "", "files", "set the current stream; --view, --unset"),
    ("stream alias NAME STREAM", "", "files", "name a stream; --list, --remove NAME"),
    ("revision list", "revisions", "either", "the revisions served"),
    ("revision describe REV", "", "either", "a served revision's description (REV: 7+ hex digits)"),
    ("api METHOD [JSON]", "call", "either", "any method, its params as JSON and -f key=value; checked first"),
    ("principal create", "", "either", "a new principal; its token to --token-file or --save-as"),
    ("status", "mode", "either", "the resolved mode, what decided it, the target, the token"),
    ("auth login|logout|status|rotate", "login logout whoami", "remote", "store, forget, check, rotate tokens"),
    ("host serve", "serve", "local", "run the host: HTTP, or one session over stdio"),
    ("host principal create", "", "local", "the operator's: a principal and its first token"),
    ("host token rotate PRINCIPAL", "token rotate", "local", "rotate a principal's token"),
    ("host replay", "replay", "local", "recompute and replay every stream"),
    ("host export FILE", "export", "local", "every stream's rows, salts and heads to FILE (no tokens)"),
    ("host import FILE", "import", "local", "store an export's rows, every chain checked"),
    ("engine init NAME", "init", "files", "scaffold a layer project"),
    ("engine check [PROJECT]", "check", "files", "lake build, axioms, word scan, imports, audit, self-test"),
    ("engine build", "build", "files", "build an engine at a commit, with a provenance manifest"),
    ("engine install BUILD_DIR", "install", "files", "put a built engine into an engines directory"),
    ("engine describe ENGINE", "describe", "files", "an engine's description (a path, or a revision prefix)"),
    ("conform", "", "self", "the conformance suite, on a throwaway host or --base-url"),
    ("config get|set|unset|list", "", "files", "the settings in ~/.provenstream/config.json (no secrets)"),
    ("help", "", "files", "this list"),
]
MODE_OF = {"open": "either", "close": "either", "head": "either", "events": "either", "verify": "either",
           "call": "either", "revisions": "either", "revision": "either", "principal": "either",
           "mode": "either", "use": "files", "alias": "files", "auth": "remote", "login": "remote",
           "logout": "remote", "whoami": "remote", "serve": "local", "host-principal": "local", "token": "local",
           "replay": "local", "export": "local", "import": "local", "conform": "self", "init": "files",
           "check": "files", "build": "files", "install": "files", "describe": "files", "config": "files",
           "help": "files"}
CALLS = ("open", "close", "call", "events", "head", "revisions", "revision", "serve", "principal")   # take --as

EPILOG = ("commands, their flat aliases, and their modes (remote: a host over JSON-RPC; local: a database, in process; "
          "either: whichever the mode resolves to; self: a throwaway host of its own, or the host it names; files: no "
          "host, no database):\n" +
          "  %-32s %-19s %-7s %s\n" % ("command", "flat alias", "mode", "what") +
          "\n".join("  %-32s %-19s %-7s %s" % c for c in COMMANDS) +
          "\n\nmode: PROVENSTREAM_MODE (remote|local), else local if --db or PROVENSTREAM_DATABASE_URL, else local "
          "for a local command when no base URL is named (database: ~/.provenstream/streams.db), else remote. The "
          "host: --base-url, else PROVENSTREAM_BASE_URL, else the project file's host, else config default_host, "
          "else the local host, http://127.0.0.1:8080; the token: --token-file, else PROVENSTREAM_TOKEN, else the one "
          "provenstream login stored for that host."
          "\nthe current stream (head, events, verify): STREAM, else PROVENSTREAM_STREAM, else "
          ".provenstream/client.json (the nearest, walking up), else config stream. A STREAM is a UUID, an alias, "
          "or the last 8+ hex digits of a stream known here."
          "\n-q PATH (--field) prints one value of a JSON result: events.0.seq."
          "\na proof command (stream open, stream close, api) is checked against its revision's description before "
          "it is sent (method not found, invalid params: exit 5, nothing sent); provenstream -h --proof PROOF prints "
          "a proof's commands."
          "\nexit codes: 1 a check failed or a confirmation did not match, 2 usage, 3 unauthorized, 4 refused (the "
          "rule is printed), 5 method not found or invalid params, 6 unavailable (or no description to be had), 7 "
          "needs local mode, 8 mode misconfigured.")


def cmd_conform(a) -> int:
    from . import conform
    return conform.run(a)


def cmd_config(a) -> int:
    if a.action == "get":
        if a.key == config.ALIASES:
            print(json.dumps(config.aliases(), sort_keys=True))
            return 0
        name = config.alias_name(a.key)
        if name:
            v = config.aliases().get(name)
            if v is None:
                return _err("no alias %s in %s" % (name, config.path()))
            print(v)
            return 0
        config.known(a.key)
        v = config.get(a.key)
        if v is None:
            pr = context.load_project()
            val, src = config.effective(a.key, None, project=(pr.path, pr.data))
            return _err("%s is not set in %s (in effect: %s, from %s)" % (a.key, config.path(), val, src))
        print(v)
    elif a.action == "set":
        print("%s = %s" % (a.key, config.set_value(a.key, a.value)))
    elif a.action == "unset":
        if not config.unset(a.key):
            return _err("%s is not set in %s" % (a.key, config.path()))
    else:
        pr = context.load_project()
        flags = {"default_host": getattr(a, "base_url", None), "local.engines": getattr(a, "engines", None)}
        rows = []
        for k in sorted(config.KEYS):
            v, src = config.effective(k, flags.get(k), project=(pr.path, pr.data))
            env = config.KEYS[k].env
            rows.append((k, v if v is not None else "<not set>", src + (" (%s)" % env if src == "env" else "") +
                         (" (%s)" % pr.path if src == "project" else "")))
        for n, s, where in context.aliases():
            rows.append(("aliases." + n, s, where + (" (%s)" % pr.path if where == "project" else "")))
        w0, w1 = max(14, max(len(r[0]) for r in rows)), max(44, max(len(r[1]) for r in rows))
        print("%-*s %-*s %s" % (w0, "key", w1, "value", "source"))
        for r in rows:
            print("%-*s %-*s %s" % (w0, r[0], w1, r[1], r[2]))
        print("config file: %s" % config.path())
    return 0


def cmd_help(a) -> int:
    print(EPILOG)
    return 0


def _opts(p: argparse.ArgumentParser, top: bool, remote=False, local=False, actor=False, engines=False) -> None:
    d = None if top else argparse.SUPPRESS
    if remote or top:
        p.add_argument("--base-url", "--url", dest="base_url", default=d,
                       help="the host, remote mode (default: PROVENSTREAM_BASE_URL, else the project file's host, else "
                            "config default_host, else the local host, http://127.0.0.1:8080)")
        p.add_argument("--token-file", default=d, help="a file holding the token (default: PROVENSTREAM_TOKEN, else "
                                                       "the token provenstream login stored for the host)")
        p.add_argument("--token", default=d, help=argparse.SUPPRESS)       # visible in process lists: discouraged
        p.add_argument("--principal", dest="use_principal", default=d, metavar="P",
                       help="remote mode: send the token stored for principal P on the host, not the active one's")
    if local or top:
        p.add_argument("--db", default=d, help=DB_HELP)
    if actor or top:
        p.add_argument("--as", dest="actor", default=d, metavar="PRINCIPAL",
                       help="local mode: the principal a call acts as (it must be known to the store); its actor_id")
    if engines or top:
        p.add_argument("--engines", default=d, help="the engines directory (default: PROVENSTREAM_ENGINES)")


def _field(p: argparse.ArgumentParser) -> None:
    p.add_argument("-q", "--field", metavar="PATH", default=None,
                   help="print only the value at PATH of the JSON result (dotted, list indexes allowed: events.0.seq); "
                        "a string as it is, anything else as JSON; a missing path is exit 5")


AUTH = [("login", "check a token with whoami, then store it for the host (token on stdin, or --token-file)"),
        ("logout", "forget a host's stored token (the active principal's, --principal P's, or --all)"),
        ("status", "per host: the stored principals, the token that would be sent and where from, and whoami"),
        ("rotate", "a new token for a stored principal from the host, saved where the old one was")]


def _auth_action(s: argparse.ArgumentParser, action: str) -> None:
    """The arguments of one `auth` action, the same under `auth ACTION` and its top-level alias."""
    d = argparse.SUPPRESS
    s.add_argument("--base-url", "--url", dest="base_url", default=d,
                   help="the host (default: PROVENSTREAM_BASE_URL, else the project file's host, else config "
                        "default_host, else the local host, http://127.0.0.1:8080)")
    s.add_argument("--db", default=d, help=argparse.SUPPRESS)      # accepted only to be refused: a database is local
    if action == "login":
        s.add_argument("--token-file", default=d, help="a file holding the token (default: stdin; on a terminal, a "
                                                       "prompt that does not echo it)")
        s.add_argument("--storage", choices=["keyring", "file"], default=None,
                       help="where the token goes (default: the keychain if the keyring extra has a backend, else "
                            "credentials.json, 0600)")
        s.add_argument("--default", action="store_true", help="also make this host config default_host")
        s.set_defaults(f=auth.cmd_login)
        return
    s.add_argument("--principal", dest="use_principal", default=d, metavar="P",
                   help="a stored principal of the host (default: its active one)")
    if action == "logout":
        s.add_argument("--all", action="store_true", help="every principal stored for the host")
        s.set_defaults(f=auth.cmd_logout)
    elif action == "status":
        s.add_argument("--token-file", default=d, help=argparse.SUPPRESS)
        s.add_argument("--json", action="store_true", help="one JSON object, for scripts (exit 0 unless fatal)")
        _field(s)
        s.set_defaults(f=auth.cmd_status)
    else:
        s.set_defaults(f=auth.cmd_rotate)


# -- the arguments of each command, the same under its tree name and its flat alias ---------------------------------

BOTH = dict(remote=True, local=True)


def _a_call(s) -> None:
    s.add_argument("method"); s.add_argument("params", nargs="?", metavar="JSON_PARAMS")
    s.add_argument("-f", "--field-param", dest="fields", action="append", metavar="KEY=VALUE",
                   help="a param, merged into JSON_PARAMS (repeatable): VALUE as JSON when it parses (5, true, "
                        "null, {...}), else as a string")
    s.add_argument("--proof", metavar="PROOF", help="check a proof command against this proof's description (a "
                                                    "revision URL, 7+ hex digits of a served revision, an engine or a "
                                                    "build directory), not its stream's")
    _opts(s, False, actor=True, engines=True, **BOTH); _field(s); s.set_defaults(f=cli_stream.cmd_call, cmd="call")


def _a_open(s) -> None:
    s.add_argument("proof_url", nargs="?", metavar="PROOF_URL",
                   help="<repository>/commit/<hash>, or 7+ hex digits of a served revision (default: the project "
                        "file's or config's proof_revision_url, else HEAD of this git repository)")
    s.add_argument("--meta")
    s.add_argument("--no-use", action="store_true", help="do not make the new stream the current one")
    s.add_argument("--alias", metavar="NAME", help="also name the new stream NAME (where the current stream is kept)")
    s.add_argument("--from-git", action="store_true", help="the proof URL from git even when one is configured: "
                                                           "origin as https, /commit/, HEAD (clean, and pushed)")
    _opts(s, False, actor=True, engines=True, **BOTH); _field(s); s.set_defaults(f=cli_stream.cmd_open, cmd="open")


def _a_principal_create(s) -> None:
    g = s.add_mutually_exclusive_group()
    g.add_argument("--token-file", dest="token_out", metavar="PATH", default=None,
                   help="write the new principal's token to PATH (created 0600; never over an existing file)")
    g.add_argument("--save-as", metavar="NAME", default=None,
                   help="remote: store the token for the host under NAME (then --principal NAME sends it)")
    _opts(s, False, actor=True, engines=True, local=True)
    s.add_argument("--base-url", "--url", dest="base_url", default=argparse.SUPPRESS, help=argparse.SUPPRESS)
    s.add_argument("--principal", dest="use_principal", default=argparse.SUPPRESS, metavar="P",
                   help="remote mode: create it as the stored principal P")
    _field(s); s.set_defaults(f=cli_stream.cmd_principal_create, cmd="principal")


def _a_close(s) -> None:
    s.add_argument("stream", metavar="STREAM", help="required: close never acts on the current stream implicitly")
    s.add_argument("--yes", action="store_true", help="close without asking (for scripts)")
    s.add_argument("--confirm", metavar="STREAM", help="close without asking if STREAM names the same stream")
    s.add_argument("--dry-run", action="store_true", help="read the stream and the caller, report whether a close "
                                                          "would be accepted, and send nothing")
    s.add_argument("--meta", metavar="TEXT", help="the close's meta")
    _opts(s, False, actor=True, engines=True, **BOTH); _field(s); s.set_defaults(f=cli_stream.cmd_close, cmd="close")


def _a_events(s) -> None:
    s.add_argument("stream", nargs="?", metavar="STREAM", help="default: the current stream")
    s.add_argument("--from", dest="start", type=int, default=0)
    _opts(s, False, actor=True, engines=True, **BOTH); _field(s)
    s.set_defaults(f=cli_stream.cmd_events, cmd="events")


def _a_head(s) -> None:
    s.add_argument("stream", nargs="?", metavar="STREAM", help="default: the current stream")
    _opts(s, False, actor=True, engines=True, **BOTH); _field(s); s.set_defaults(f=cli_stream.cmd_head, cmd="head")


def _a_revisions(s) -> None:
    _opts(s, False, actor=True, engines=True, **BOTH); _field(s)
    s.set_defaults(f=cli_stream.cmd_revisions, cmd="revisions")


def _a_mode(s) -> None:
    s.add_argument("--json", action="store_true", help="one JSON object, for scripts")
    _opts(s, False, engines=True, **BOTH); _field(s); s.set_defaults(f=cmd_mode, cmd="mode")


def _a_verify(s, flat: bool) -> None:
    if not flat:
        s.add_argument("stream_arg", nargs="?", metavar="STREAM", help="default: --stream, else the current stream")
    s.add_argument("--rows")
    _opts(s, False, **BOTH)
    s.add_argument("--stream")
    h = s.add_mutually_exclusive_group()
    h.add_argument("--engine"); h.add_argument("--engines"); h.add_argument("--repo")
    s.add_argument("--package", default=None, help="--repo: the package to build (default: the one the stream's "
                                                   "revision names)")
    s.add_argument("--reuse-lake")
    s.add_argument("--head", action="append", help="SEQ:HEX, or HEX for the last row: a head a client kept (repeatable)")
    s.set_defaults(f=cmd_verify, cmd="verify")


def _a_serve(s) -> None:
    _opts(s, False, local=True, actor=True, engines=True)
    s.add_argument("--stdio", action="store_true", help="JSON-RPC 2.0 on stdin and stdout, one request per line, as "
                                                        "the one principal of --as or --token-file")
    s.add_argument("--token-file", default=argparse.SUPPRESS, help="--stdio: a file holding the session's token")
    s.add_argument("--host", default="127.0.0.1"); s.add_argument("--port", type=int, default=8080)
    s.add_argument("--idle-timeout", type=float, default=300.0); s.add_argument("--max-streams", type=int, default=10000)
    s.set_defaults(f=cmd_serve, cmd="serve")


def _a_host_principal(s) -> None:
    _opts(s, False, local=True, engines=True)
    s.add_argument("--id", help="an existing principal id this store holds no token for (as after import)")
    s.add_argument("--token-file", dest="token_out", metavar="PATH", default=None,
                   help="write the token to PATH (created 0600, never over an existing file) and print only "
                        "{principal_id}")
    _field(s); s.set_defaults(f=cmd_host_principal, cmd="host-principal")


def _a_token(s) -> None:
    s.add_argument("principal"); _opts(s, False, local=True)
    s.set_defaults(f=cmd_token, cmd="token")


def _a_replay(s) -> None:
    _opts(s, False, local=True, engines=True)
    s.add_argument("--head", action="append", help="STREAM:SEQ:HEX, a head a client kept (repeatable)")
    s.set_defaults(f=cmd_replay, cmd="replay")


def _a_file(s, name: str, f) -> None:
    s.add_argument("file"); _opts(s, False, local=True)
    s.set_defaults(f=f, cmd=name)


def _a_init(s) -> None:
    s.add_argument("name"); s.add_argument("--dir"); s.add_argument("--core")
    s.add_argument("--core-git"); s.add_argument("--core-rev")
    s.set_defaults(f=cmd_init, cmd="init")


def _a_check(s) -> None:
    s.add_argument("project", nargs="?", default=".")
    s.set_defaults(f=cmd_check, cmd="check")


def _a_build(s) -> None:
    s.add_argument("--repo", required=True); s.add_argument("--commit", required=True)
    s.add_argument("--out", required=True); s.add_argument("--package", default=".")
    s.add_argument("--repo-url"); s.add_argument("--reuse-lake")
    _field(s); s.set_defaults(f=cmd_build, cmd="build")


def _a_install(s) -> None:
    s.add_argument("build_dir"); _opts(s, False, engines=True)
    s.set_defaults(f=cmd_install, cmd="install")


def _a_describe(s) -> None:
    s.add_argument("engine", help="the engine's path, or 7+ hex digits of a revision in the engines directory")
    _opts(s, False, engines=True); _field(s)
    s.set_defaults(f=cmd_describe, cmd="describe")


def _a_use(s) -> None:
    s.add_argument("stream", nargs="?", metavar="STREAM", help="an id, an alias, or the last 8+ hex digits of one")
    s.add_argument("--unset", action="store_true", help="forget the current stream (where use would write it)")
    s.add_argument("--view", action="store_true", help="show the current stream and where it comes from")
    s.add_argument("--project", action="store_true", help="write to the project file, creating .provenstream/"
                                                          "client.json here if there is none")
    _field(s); s.set_defaults(f=cli_stream.cmd_use, cmd="use")


def _a_alias(s) -> None:
    s.add_argument("name", nargs="?", metavar="NAME"); s.add_argument("stream", nargs="?", metavar="STREAM")
    s.add_argument("--list", action="store_true", help="every alias in effect (the project's shadow the user's)")
    s.add_argument("--remove", metavar="NAME", help="remove an alias (the project's if it has one, else the user's)")
    s.add_argument("--project", action="store_true", help="write to the project file, creating .provenstream/"
                                                          "client.json here if there is none")
    _field(s); s.set_defaults(f=cli_stream.cmd_alias, cmd="alias")


def _a_revision_describe(s) -> None:
    s.add_argument("revision", metavar="REV", help="7 or more hex digits of a revision the host serves")
    _opts(s, False, actor=True, engines=True, **BOTH); _field(s)
    s.set_defaults(f=cli_stream.cmd_revision_describe, cmd="revision")


def _group(sub, name: str, h: str, dest: str):
    """A noun of the tree: a parser whose actions are its subcommands."""
    return sub.add_parser(name, help=h, description=h).add_subparsers(dest=dest, required=True, metavar="ACTION")


def parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(prog="provenstream", description="A stream is a proof.", epilog=EPILOG,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--version", action="version", version="provenstream " + __version__)
    _opts(p, True)
    sub = p.add_subparsers(dest="cmd", required=True, metavar="COMMAND")
    leaf = lambda parent, name, h: parent.add_parser(name, help=h, description=h)
    # the tree
    st = _group(sub, "stream", "open, close and read streams; the current stream and aliases", "action")
    _a_open(leaf(st, "open", "open a stream judged by a proof; it becomes the current stream"))
    _a_close(leaf(st, "close", "close a stream, finally, after a confirmation"))
    _a_head(leaf(st, "head", "a stream's length and chain head"))
    _a_events(leaf(st, "events", "a stream's events, each with its seq and chain head"))
    _a_verify(leaf(st, "verify", "recompute a stream's chain and replay its rows through an engine of its revision"),
              False)
    _a_use(leaf(st, "use", "set the current stream (the project file, else the user config)"))
    _a_alias(leaf(st, "alias", "name a stream, list the names, or remove one"))
    rv = _group(sub, "revision", "the proof revisions a host serves", "action")
    _a_revisions(leaf(rv, "list", "the revisions served"))
    _a_revision_describe(leaf(rv, "describe", "a served revision's description"))
    _a_call(leaf(sub, "api", "call a method (JSON-RPC, or in process), printing its result; a proof command is "
                             "checked against its proof's description first"))
    g = sub.add_parser("principal", help="a new principal and its token (saved, never printed)").add_subparsers(
        dest="sub_action", required=True, metavar="ACTION")
    _a_principal_create(leaf(g, "create", "ask the host for a new principal: prints its principal_id; its token to "
                                          "--token-file PATH or --save-as NAME, never printed"))
    _a_mode(leaf(sub, "status", "the resolved mode, what decided it, and the target"))
    ho = _group(sub, "host", "run a host and administer its database (local mode)", "action")
    _a_serve(leaf(ho, "serve", "run the host: HTTP, or one principal's session over stdio (--stdio)"))
    g = ho.add_parser("principal", help="issue principals").add_subparsers(dest="sub_action", required=True,
                                                                           metavar="ACTION")
    _a_host_principal(leaf(g, "create", "the operator's: issue a principal and its first token"))
    g = ho.add_parser("token", help="rotate tokens").add_subparsers(dest="sub_action", required=True, metavar="ACTION")
    _a_token(leaf(g, "rotate", "rotate a principal's token"))
    _a_replay(leaf(ho, "replay", "recompute every stream's chain and replay it through its revision's engine"))
    _a_file(leaf(ho, "export", "write every stream's rows, with their salts and chain heads, to FILE"), "export",
            cmd_export)
    _a_file(leaf(ho, "import", "store the rows of an export FILE, every chain checked first"), "import", cmd_import)
    en = _group(sub, "engine", "layer projects and engines: scaffold, check, build, install, describe", "action")
    _a_init(leaf(en, "init", "scaffold a layer project on the core interface"))
    _a_check(leaf(en, "check", "lake build, axioms, word scan, imports, audit, self-test"))
    _a_build(leaf(en, "build", "build an engine from a repository at a commit, with a provenance manifest"))
    _a_install(leaf(en, "install", "put a built engine into an engines directory (never replacing one)"))
    _a_describe(leaf(en, "describe", "print an engine's description"))
    s = sub.add_parser("auth", help="store, check, rotate and forget tokens for hosts")
    acts = s.add_subparsers(dest="action", required=True)
    for action, h in AUTH:
        _auth_action(acts.add_parser(action, help=h, description=h), action)
    s = sub.add_parser("config", help="the settings in config.json: get, set, unset, list")
    acts = s.add_subparsers(dest="action", required=True)
    c = acts.add_parser("get", help="a setting's configured value (aliases: the map; aliases.NAME: one)")
    c.add_argument("key")
    c = acts.add_parser("set", help="store a setting (aliases.NAME STREAM: an alias)")
    c.add_argument("key"); c.add_argument("value")
    c = acts.add_parser("unset", help="remove a setting"); c.add_argument("key")
    c = acts.add_parser("list", help="every setting, its value in effect, and where it came from")
    c.add_argument("--base-url", "--url", dest="base_url", default=argparse.SUPPRESS)
    c.add_argument("--engines", default=argparse.SUPPRESS)
    s.set_defaults(f=cmd_config)
    s = sub.add_parser("conform", help="run the conformance suite on a throwaway host, or on --base-url")
    from . import conform
    conform.add_arguments(s)
    s.set_defaults(f=cmd_conform)
    s = sub.add_parser("help", help="every command, its alias and its mode")
    s.set_defaults(f=cmd_help)
    # the flat aliases, as they were before the tree
    _a_call(leaf(sub, "call", "api: call a method, printing its result"))
    _a_open(leaf(sub, "open", "stream open: open a stream judged by the proof at PROOF_URL"))
    _a_close(leaf(sub, "close", "stream close: close a stream, finally"))
    _a_events(leaf(sub, "events", "stream events: a stream's events, each with its seq and chain head"))
    _a_head(leaf(sub, "head", "stream head: a stream's length and chain head"))
    _a_revisions(leaf(sub, "revisions", "revision list: the revisions served"))
    _a_mode(leaf(sub, "mode", "status: print the resolved mode, what decided it, and the target"))
    _a_verify(leaf(sub, "verify", "stream verify: recompute one stream's chain and replay its rows"), True)
    for alias, action in (("login", "login"), ("logout", "logout"), ("whoami", "status")):
        _auth_action(sub.add_parser(alias, help="auth %s: %s" % (action, dict(AUTH)[action])), action)
    _a_serve(leaf(sub, "serve", "host serve: run the host"))
    s = leaf(sub, "token", "host token rotate: rotate a principal's token")
    s.add_argument("action", choices=["rotate"]); _a_token(s)
    _a_replay(leaf(sub, "replay", "host replay: recompute and replay every stream"))
    _a_file(leaf(sub, "export", "host export: write every stream's rows to FILE"), "export", cmd_export)
    _a_file(leaf(sub, "import", "host import: store the rows of an export FILE"), "import", cmd_import)
    _a_init(leaf(sub, "init", "engine init: scaffold a layer project"))
    _a_check(leaf(sub, "check", "engine check: check a layer project"))
    _a_build(leaf(sub, "build", "engine build: build an engine with a provenance manifest"))
    _a_install(leaf(sub, "install", "engine install: put a built engine into an engines directory"))
    _a_describe(leaf(sub, "describe", "engine describe: print an engine's description"))
    return p


HELP = """\
usage: provenstream [-h [--proof PROOF]] [--version] [--base-url URL] [--token-file FILE] [--principal P]
                    [--db DB] [--as PRINCIPAL] [--engines DIR] COMMAND ...

A stream is a proof. Every stream has the core's two commands:

  stream open [PROOF_URL] [--meta TEXT] [--alias NAME] [--no-use] [--from-git]
      open a stream judged by the proof at PROOF_URL (a revision URL, or 7+ hex digits of a revision the
      host serves); you are its opener, and it becomes the current stream
  stream close STREAM (--yes | --confirm STREAM) [--meta TEXT] [--dry-run]
      close STREAM for good; only its opener can (only_opener_can_close). On a terminal it asks you to type
      the stream's alias or id; elsewhere it needs --yes, or --confirm STREAM naming the same stream (exit 2)

  provenstream stream open https://example.org/provenstream/commit/<commit> --alias ledger
  provenstream stream close ledger --yes

The rest of the command line:
  stream events|head|verify|use|alias   read any stream; the current stream and aliases
  revision list|describe                the proof revisions a host serves
  api METHOD [JSON] [-f KEY=VALUE]      any method, checked against the stream's proof before it is sent
  principal create                      a new principal and its token (saved, never printed)
  auth login|logout|status|rotate       tokens, stored per host (login, logout, whoami)
  config get|set|unset|list             settings without secrets
  host serve|replay|export|import|principal create|token rotate    run a host, on its database
  engine init|check|build|install|describe                         proof projects and engines
  status, conform, help

Exit codes: 0 done, 1 a check failed, 2 usage, 3 unauthorized, 4 refused (the rule is printed),
5 method not found or invalid params, 6 unavailable, 7 needs local mode, 8 mode misconfigured.

A stream's other commands come from its proof: provenstream -h --proof <proof> shows them.
"""

# The global options that take a value (before the command), so that `-h` is told apart from a command's own `-h`.
VALUED = ("--base-url", "--url", "--token-file", "--token", "--principal", "--db", "--as", "--engines", "--proof")


def top_help(argv: List[str]) -> Optional[dict]:
    """`provenstream -h [--proof PROOF]` (with global options around it, and no command): {"proof", "flags"}; None
    when argv names a command (its own -h is argparse's) or asks no help."""
    flags: dict = {}
    helped, i = False, 0
    while i < len(argv):
        t = argv[i]
        if t in ("-h", "--help"):
            helped = True
        elif "=" in t and t.split("=", 1)[0] in VALUED:
            flags[t.split("=", 1)[0]] = t.split("=", 1)[1]
        elif t in VALUED:
            if i + 1 >= len(argv):
                return None
            flags[t] = argv[i + 1]
            i += 1
        elif not t.startswith("-") or t == "--":
            return None                                   # a command: its own help, argparse's
        i += 1
    if not helped:
        return None
    return {"proof": flags.pop("--proof", None), "flags": flags}


def proof_help(proof: str, flags: dict) -> int:
    """`-h --proof PROOF`: the proof's description as Markdown, from a path, the cache, or the host the flags name."""
    def target():
        pr = context.load_project()
        dh, dfrom = ((pr.data["host"], "project host (%s)" % pr.path) if pr.data.get("host") else
                     (config.get("default_host"), "config default_host"))
        get = lambda *names: next((flags[n] for n in names if n in flags), None)
        r = mode.resolve(get("--base-url", "--url"), get("--db"), get("--as"), default_host=dh, default_from=dfrom,
                         principal=get("--principal"))
        ns = argparse.Namespace(R=r, base_url=get("--base-url", "--url"), db=get("--db"), actor=get("--as"),
                                engines=get("--engines"), token_file=get("--token-file"), token=get("--token"),
                                use_principal=get("--principal"), cmd="help")
        return cli_stream.target(ns)
    sys.stdout.write(proofs.markdown(proofs.resolve(proof, target)))
    return 0


def main(argv: Optional[List[str]] = None) -> int:
    argv = sys.argv[1:] if argv is None else list(argv)
    asked = top_help(argv)
    if asked is not None:
        try:
            if asked["proof"] is None:
                sys.stdout.write(HELP)
                return 0
            return proof_help(asked["proof"], asked["flags"])
        except client.ClientError as x:
            print("provenstream: %s" % x.message, file=sys.stderr)
            return x.exit_code
    a = parser().parse_args(argv)
    try:
        cls = MODE_OF[a.cmd]
        if cls not in ("files", "self") and not (a.cmd == "verify" and a.rows):
            pr = context.load_project()
            dh, dfrom = ((pr.data["host"], "project host (%s)" % pr.path) if pr.data.get("host") else
                         (config.get("default_host"), "config default_host"))
            a.R = mode.resolve(a.base_url, a.db, a.actor, local_only=cls == "local", default_host=dh,
                               default_from=dfrom, principal=a.use_principal)
            if cls == "local":
                mode.needs_local(a.cmd, a.R)
            if cls == "remote" and a.R.mode != "remote":
                raise client.ClientError(client.EXIT_MODE, "mode: %s stores tokens for a host, but the mode is local "
                                         "(decided by %s); rule: a database is local mode, which needs no token"
                                         % (a.cmd, a.R.why))
            if a.actor and a.cmd not in CALLS:
                raise client.ClientError(client.EXIT_PARAMS, "invalid params: --as names the principal a call acts "
                                                             "as; %s makes no call" % a.cmd)
        return a.f(a)
    except client.ClientError as x:
        print("provenstream: %s" % x.message, file=sys.stderr)
        return x.exit_code
    except RuntimeError as x:
        from .store import NoPostgres
        if not isinstance(x, NoPostgres):
            raise
        print("provenstream: %s" % x, file=sys.stderr)
        return client.EXIT_PARAMS


if __name__ == "__main__":
    sys.exit(main())
