# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""One mode per invocation: remote (a host, over JSON-RPC) or local (a database, in process).

Resolution (`resolve`), once per invocation:

1. `PROVENSTREAM_MODE`, if set: `remote` or `local`; any other value is an error.
2. Otherwise `--db` given, or `PROVENSTREAM_DATABASE_URL` set: local.
3. Otherwise, for a command that only works locally (`serve`, `principal`, `token`, `replay`, `export`, `import`) when
   no base URL is named either (`--base-url`, `PROVENSTREAM_BASE_URL`): local, with the default database. The
   configured `default_host` (`config.py`) and a project file's `host` (`context.py`) do not count as named: they
   say where remote mode goes, not whether to use it, so configuring a host never turns a local command into an
   error.
4. Otherwise: remote.

`PGHOST` and the other `PG*` variables never select a mode, and neither does `DATABASE_URL`, which is not read. In local
mode the database is `--db`, else `PROVENSTREAM_DATABASE_URL`, else the default: the SQLite file
~/.provenstream/streams.db (its directory created 0700 when first used), so `provenstream serve` works on a machine
with no database server. Any form `store.open_store` reads is accepted: `sqlite:///abs/path.db`, a path ending .db, a
Postgres URI or `key=value` string (the `postgres` extra). Postgres with libpq's own environment (PGHOST, ~/.pgpass, as
psql) is asked for explicitly, with `postgresql://` and nothing after it. In remote mode the host is `--base-url`, else
`PROVENSTREAM_BASE_URL`, else the project file's `host`, else the configured `default_host`, else the local host,
http://127.0.0.1:8080, where `provenstream serve` listens with no flags (`Resolved.host_from` says which).

Mixing the two is an error, never ignored (exit 8): a base URL (`--base-url` or `PROVENSTREAM_BASE_URL`) in local
mode; `--as` in remote mode; `--principal` (a stored token's principal) in local mode; `--db` with
`PROVENSTREAM_MODE=remote`.

Local mode is operator access: `--as PRINCIPAL` acts as any principal the store knows, without a token, which anyone
with access to the database could do anyway. The proofs still decide every write; reading is unrestricted, as on any
host.
"""
from __future__ import annotations
import os, re, urllib.parse
from dataclasses import dataclass
from typing import Any, Dict, Mapping, Optional

from . import client
from .client import ClientError, EXIT_MODE, EXIT_NEEDS_LOCAL, EXIT_UNAUTHORIZED
from .protocol import ANSWERS


@dataclass
class Resolved:
    mode: str                 # "remote" or "local"
    why: str                  # what decided it
    base_url: Optional[str]   # remote: the host
    db: Optional[str]         # local: the store's target (store.open_store)
    host_from: Optional[str] = None   # remote: what named the host (--base-url, PROVENSTREAM_BASE_URL, config, default)


LIBPQ_ENV = ("postgresql://", "postgres://", "")


def default_db() -> str:
    from .store_sqlite import default_target
    return default_target()


def resolve(base_url_flag: Optional[str], db_flag: Optional[str], actor: Optional[str],
            env: Mapping[str, str] = os.environ, local_only: bool = False, default_host: Optional[str] = None,
            principal: Optional[str] = None, default_from: str = "config default_host") -> Resolved:
    """The mode, by the rules above. `local_only`: the command works only in local mode (rule 3). `default_host`: the
    configured host (the project file's, else config's, as `default_from` says), remote mode's fallback before the
    local host (`client.DEFAULT_BASE_URL`), which never decides the mode. `principal`: `--principal`, which only remote
    mode has a use for."""
    m = env.get("PROVENSTREAM_MODE") or None
    db_env = env.get("PROVENSTREAM_DATABASE_URL") or None
    base_env = env.get("PROVENSTREAM_BASE_URL") or None
    if m is not None:
        if m not in ("remote", "local"):
            raise ClientError(EXIT_MODE, "mode: PROVENSTREAM_MODE must be remote or local, not %r" % m)
        mode, why = m, "PROVENSTREAM_MODE=%s" % m
        if m == "remote" and db_flag:
            raise ClientError(EXIT_MODE, "mode: --db cannot be used with PROVENSTREAM_MODE=remote (rule: a database "
                                         "is local mode)")
    elif db_flag:
        mode, why = "local", "--db"
    elif db_env:
        mode, why = "local", "PROVENSTREAM_DATABASE_URL"
    elif local_only and not (base_url_flag or base_env):
        mode, why = "local", "no database and no host named, and the command is local only: the default database"
    else:
        mode, why = "remote", "no database named (no --db, no PROVENSTREAM_DATABASE_URL)"
    if mode == "local":
        if base_url_flag or base_env:
            raise ClientError(EXIT_MODE, "mode: %s names a host, but the mode is local (decided by %s); rule: a base "
                                         "URL is remote mode, so unset one, or set PROVENSTREAM_MODE=remote"
                              % ("--base-url" if base_url_flag else "PROVENSTREAM_BASE_URL", why))
        if principal:
            raise ClientError(EXIT_MODE, "mode: --principal picks a token stored for a host, but the mode is local "
                                         "(decided by %s); rule: local mode acts as --as PRINCIPAL, without a token"
                              % why)
        return Resolved("local", why, None, db_flag or db_env or default_db())
    if actor:
        raise ClientError(EXIT_MODE, "mode: --as acts as a principal without a token, which only local mode can do "
                                     "(rule: --as needs a database); the mode is remote (decided by %s)" % why)
    url, src = next((u, n) for u, n in ((base_url_flag, "--base-url"), (base_env, "PROVENSTREAM_BASE_URL"),
                                         (default_host, default_from), (client.DEFAULT_BASE_URL, "default"))
                    if u)
    return Resolved("remote", why, url.rstrip("/"), None, src)


def needs_local(command: str, r: Resolved) -> None:
    if r.mode != "local":
        raise ClientError(EXIT_NEEDS_LOCAL, "%s needs a database: set PROVENSTREAM_DATABASE_URL or --db (local mode); "
                                            "the mode is remote (decided by %s)" % (command, r.why))


def redact(target: str) -> str:
    """A connection string or URL with its password hidden."""
    if "://" in target:
        u = urllib.parse.urlsplit(target)
        if u.password is not None:
            host = u.hostname or ""
            netloc = "%s:***@%s%s" % (u.username or "", host, ":%d" % u.port if u.port else "")
            u = u._replace(netloc=netloc)
        q = re.sub(r"(password=)[^&]*", r"\1***", u.query)
        return urllib.parse.urlunsplit(u._replace(query=q))
    return re.sub(r"(password\s*=\s*)('(?:[^'\\]|\\.)*'|\S+)", r"\1***", target)


class Local:
    """Local mode: the host in process (`Host.open` on the database), each call `Host.handle` as `Operator(--as)`, so
    it answers exactly as `serve` would; `handle` is `client.Remote.handle`'s twin, the same results and the same
    `ClientError`s. Writes go through the same compare-and-set append as `serve`, so they are safe alongside one.
    Without `--as` it is the operator as no principal: it reads and creates principals, and acts as no one."""

    def __init__(self, db: str, engines_dir: Optional[str], actor: Optional[str]):
        from .host import Host
        self.host = Host.open(db, engines_dir)
        self.actor = actor
        if actor is not None and not self.host.store.known(actor):
            self.close()
            raise ClientError(EXIT_UNAUTHORIZED, "unauthorized: no such principal in this store: %s" % actor)

    def handle(self, method: str, params: Optional[Dict[str, Any]] = None) -> Any:
        from .host import Operator
        ans = self.host.handle({"jsonrpc": "2.0", "id": 1, "method": method, "params": params or {}},
                               Operator(self.actor))
        if ans.ok:
            return ans.result
        if ans.code == "unauthorized" and self.actor is None:
            raise ClientError(EXIT_UNAUTHORIZED, "unauthorized: in local mode a call acts as --as PRINCIPAL")
        k = ANSWERS[ans.code]
        raise client.error_of(k.rpc, k.message, ans.data)

    def close(self) -> None:
        self.host.close()

    def __enter__(self) -> "Local":
        return self

    def __exit__(self, *exc: Any) -> None:
        self.close()
