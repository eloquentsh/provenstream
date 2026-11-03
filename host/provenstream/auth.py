# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""Stored tokens: `provenstream auth login|logout|status|rotate` (and `login`, `logout`, `whoami`), and which token a
remote command sends (`token_for`).

A token is a bearer secret the host shows once, so the command line keeps it for the user instead of asking them to
manage files: under the host it was issued by (`config.normalize_host`) and the principal it names, which a `whoami`
with it told us at login. Several principals may be stored for one host (a person and the agents they run); one of
them is the host's active principal, the one a command uses unless `--principal P` names another. Logging in makes
that principal active.

Where a token lives. The map of hosts and principals is credentials.json in the config directory (`config.py`):

    {"<host>": {"active": "<principal>", "principals": {"<principal>": {"storage": "keyring", "name": "agent"}}}}

An entry may carry a `name` (`provenstream principal create --save-as NAME`): `--principal` takes a principal's id or
its name.

With the optional `keyring` library (`pip install 'provenstream[keyring]'`) and a working backend, the token itself is
in the system keychain, service `provenstream:<host>`, account `<principal>`; otherwise it is in the map as `token`,
`"storage": "file"`, and login says so once. The file is 0600 in a 0700 directory, and a credentials file that group
or others can read is refused outright, as libpq refuses a loose ~/.pgpass: a token that others could have read is
not one to keep sending. The keychain is only ever reached through the library, never by running a program with the
token in its arguments.

Which token a remote command sends (`token_for`): `--token-file`, else `PROVENSTREAM_TOKEN`, else the stored token of
the resolved host's `--principal` or active principal, else `--token` (visible in process lists: warned). A stored
token is looked up by the host the command is about to call, so it is only ever sent to the host it was issued by;
`client.Remote` also never follows a redirect, which would carry the header elsewhere. `--principal` picks among
stored tokens, so it is an error beside a token named another way.

`auth rotate` asks the host for a new token as the stored principal and saves it where the old one was before it says
anything: the host revoked the old one when it answered, so a token not saved is a principal locked out until the
operator rotates it (`provenstream token rotate PRINCIPAL`, on the host's database). It checks it can write first.
"""
from __future__ import annotations
import getpass, json, os, stat, sys
from dataclasses import dataclass
from typing import Any, Dict, List, Mapping, Optional, Tuple

from . import client, config
from .client import ClientError, EXIT_PARAMS, EXIT_UNAUTHORIZED, EXIT_UNAVAILABLE

KEYRING_SERVICE = "provenstream:%s"


class InsecureFile(ClientError):
    """A credentials file others can read: refused, whatever the command (fatal even for `auth status --json`)."""


def credentials_path(env: Mapping[str, str] = os.environ) -> str:
    return os.path.join(config.directory(env), "credentials.json")


def load(env: Mapping[str, str] = os.environ) -> Dict[str, Any]:
    p = credentials_path(env)
    try:
        st = os.stat(p)
    except FileNotFoundError:
        return {}
    if st.st_mode & (stat.S_IRWXG | stat.S_IRWXO):
        raise InsecureFile(EXIT_UNAUTHORIZED, "unauthorized: %s is readable by others (mode %03o): its tokens may "
                           "have been seen; rotate them, and chmod 600 %s" % (p, stat.S_IMODE(st.st_mode), p))
    return config.read_json(p)


def save(creds: Dict[str, Any], env: Mapping[str, str] = os.environ) -> None:
    config.ensure_directory(env)
    config.write_atomic(credentials_path(env), creds)


# -- the keychain ---------------------------------------------------------------------------------------------------

def keyring_backend():
    """The keyring module if it is importable and has a backend that stores something (not the fail or null backend,
    and not an empty chain), else None."""
    try:
        import keyring
        import keyring.backends.fail, keyring.backends.null
    except Exception:
        return None
    try:
        kr = keyring.get_keyring()
        if isinstance(kr, (keyring.backends.fail.Keyring, keyring.backends.null.Keyring)):
            return None
        if getattr(kr, "backends", None) == []:                       # a chainer with nothing in it
            return None
        if float(getattr(kr, "priority", 1)) <= 0:
            return None
    except Exception:
        return None
    return keyring


def _kr_get(host: str, principal: str) -> Optional[str]:
    kr = keyring_backend()
    if kr is None:
        raise ClientError(EXIT_UNAUTHORIZED, "unauthorized: the token of %s on %s is in the keychain, and no keychain "
                          "is available here (pip install 'provenstream[keyring]'); log in again" % (principal, host))
    return kr.get_password(KEYRING_SERVICE % host, principal)


def _kr_set(host: str, principal: str, token: str) -> None:
    kr = keyring_backend()
    if kr is None:
        raise OSError("no keychain is available")
    kr.set_password(KEYRING_SERVICE % host, principal, token)


def _kr_delete(host: str, principal: str) -> None:
    kr = keyring_backend()
    if kr is None:
        return
    try:
        kr.delete_password(KEYRING_SERVICE % host, principal)
    except Exception:
        pass                                                          # already gone


def describe_storage(storage: str, host: str, principal: str, env: Mapping[str, str] = os.environ) -> str:
    if storage == "keyring":
        return "the keychain (service %s, account %s)" % (KEYRING_SERVICE % host, principal)
    return credentials_path(env)


# -- stored tokens --------------------------------------------------------------------------------------------------

def stored(creds: Dict[str, Any], host: str, principal: Optional[str]) -> Tuple[Optional[str], Optional[Dict[str, Any]]]:
    """The principal meant for `host` (`principal`, an id or a stored name, else the host's active one) and its stored
    entry, or None."""
    h = creds.get(host) or {}
    entries = h.get("principals") or {}
    p = principal or h.get("active")
    if p and p not in entries:
        named = [q for q, e in entries.items() if isinstance(e, dict) and e.get("name") == p]
        if len(named) == 1:
            p = named[0]
    return p, (entries.get(p) if p else None)


NAME_CHARS = set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789._-")


def check_name(name: str) -> str:
    """A name a stored principal can go by: 1 to 64 of [A-Za-z0-9._-], not a principal id."""
    from . import ids
    if not (1 <= len(name) <= 64 and set(name) <= NAME_CHARS) or ids.CANONICAL_ID.fullmatch(name):
        raise ClientError(EXIT_PARAMS, "invalid params: --save-as %r: a name is 1 to 64 of A-Z a-z 0-9 . _ - (not a "
                                       "principal id)" % name)
    return name


def stored_token(host: str, principal: str, entry: Dict[str, Any]) -> Optional[str]:
    if entry.get("storage") == "keyring":
        return _kr_get(host, principal)
    t = entry.get("token")
    return t if isinstance(t, str) and t else None


def put(host: str, principal: str, token: str, storage: str, env: Mapping[str, str] = os.environ,
        make_active: bool = True, name: Optional[str] = None) -> None:
    """Store `token` for (`host`, `principal`), under `name` too when one is given (a name moves to it from any other
    principal): the keychain first, then the map, so the map never names a keychain entry that is not there."""
    if storage == "keyring":
        _kr_set(host, principal, token)
    creds = load(env)
    h = creds.setdefault(host, {"principals": {}})
    h.setdefault("principals", {})
    old = h["principals"].get(principal) or {}
    entry: Dict[str, Any] = {"storage": storage}
    name = name or old.get("name")
    if name:
        entry["name"] = name
        for q, e in h["principals"].items():
            if q != principal and isinstance(e, dict) and e.get("name") == name:
                e.pop("name", None)
    if storage == "file":
        entry["token"] = token
    h["principals"][principal] = entry
    if make_active or not h.get("active"):
        h["active"] = principal
    save(creds, env)
    if old.get("storage") == "keyring" and storage == "file":
        _kr_delete(host, principal)


@dataclass
class Chosen:
    token: Optional[str]
    source: str                   # "flag" (--token-file), "env", "keyring", "file", "flag (--token)", or "none"
    principal: Optional[str]      # the stored principal, when the token is a stored one
    host: str                     # the normalized host


def token_for(base_url: str, token_file: Optional[str], token_flag: Optional[str], principal: Optional[str],
              env: Mapping[str, str] = os.environ, warn: bool = True) -> Chosen:
    """The token a remote command sends to `base_url`, by the precedence above, and where it came from. No token at
    all is `Chosen(None, "none", ...)`; the caller decides whether that is an error."""
    host = config.normalize_host(base_url)
    named = "--token-file" if token_file else "PROVENSTREAM_TOKEN" if env.get("PROVENSTREAM_TOKEN") else \
        "--token" if token_flag else None
    if principal and named:
        raise ClientError(EXIT_PARAMS, "invalid params: --principal picks a stored token, and %s names a token "
                                       "already; use one of them" % named)
    if token_file:
        return Chosen(client.token(token_file, None), "flag", None, host)
    if env.get("PROVENSTREAM_TOKEN"):
        return Chosen(env["PROVENSTREAM_TOKEN"].strip(), "env", None, host)
    p, entry = stored(load(env), host, principal)
    if entry is not None:
        t = stored_token(host, p, entry)
        if t:
            return Chosen(t, entry.get("storage", "file"), p, host)
    if principal:
        raise ClientError(EXIT_UNAUTHORIZED, "unauthorized: no stored token for %s on %s (provenstream login "
                                             "--base-url %s)" % (principal, host, host))
    if token_flag:
        if warn:
            print("provenstream: warning: --token is visible in process lists; prefer provenstream login, "
                  "PROVENSTREAM_TOKEN or --token-file", file=sys.stderr)
        return Chosen(token_flag, "flag (--token)", None, host)
    return Chosen(None, "none", None, host)


def remote_choice(a, env: Mapping[str, str] = os.environ) -> Chosen:
    """The token of a remote command and where it came from, or `unauthorized` when there is none."""
    c = token_for(a.R.base_url, getattr(a, "token_file", None), getattr(a, "token", None),
                  getattr(a, "use_principal", None), env)
    if c.token is None:
        raise ClientError(EXIT_UNAUTHORIZED, "unauthorized: no token for %s (provenstream login, or set "
                                             "PROVENSTREAM_TOKEN, or pass --token-file)" % c.host)
    return c


def remote_token(a, env: Mapping[str, str] = os.environ) -> str:
    """The token of a remote command, or `unauthorized` when there is none."""
    return remote_choice(a, env).token


# -- the commands ---------------------------------------------------------------------------------------------------

def _read_login_token(token_file: Optional[str]) -> str:
    if token_file:
        return client.token(token_file, None)
    if sys.stdin is not None and sys.stdin.isatty():
        t = getpass.getpass("token (it is not echoed): ")
    else:
        t = sys.stdin.read() if sys.stdin is not None else ""
    t = t.strip()
    if not t:
        raise ClientError(EXIT_UNAUTHORIZED, "unauthorized: no token given on stdin (or pass --token-file FILE)")
    return t


def default_storage() -> str:
    """Where a new token goes when nothing asks: the keychain if there is one, else credentials.json."""
    return "keyring" if keyring_backend() is not None else "file"


def _storage(asked: Optional[str]) -> str:
    if asked == "file":
        return "file"
    if keyring_backend() is not None:
        return "keyring"
    if asked == "keyring":
        raise ClientError(1, "no keychain is available: install the keyring extra (pip install "
                             "'provenstream[keyring]') with a working backend, or use --storage file")
    return "file"


def cmd_login(a) -> int:
    host = config.normalize_host(a.R.base_url)
    storage = _storage(a.storage)                 # before the token is asked for, so a refusal costs nothing
    tok = _read_login_token(a.token_file)
    who = client.Remote(a.R.base_url, tok).handle("whoami")      # unauthorized: exit 3, nothing stored
    principal = who.get("principal_id")
    if not isinstance(principal, str) or not principal:
        raise ClientError(EXIT_UNAVAILABLE, "unavailable: the host's whoami named no principal")
    if storage == "file" and a.storage != "file":
        print("provenstream: warning: no keychain available (pip install 'provenstream[keyring]'): the token is "
              "stored in %s, readable by you only" % credentials_path(), file=sys.stderr)
    put(host, principal, tok, storage)
    if a.default:
        config.set_value("default_host", host)
    print("logged in to %s as %s; token in %s; it cannot be shown again (provenstream auth rotate issues a new "
          "one)%s" % (host, principal, describe_storage(storage, host, principal),
                      "; %s is now the default host" % host if a.default else ""))
    if os.environ.get("PROVENSTREAM_TOKEN"):
        print("provenstream: warning: PROVENSTREAM_TOKEN is set, and wins over the stored token until it is unset",
              file=sys.stderr)
    return 0


def cmd_logout(a) -> int:
    if a.all and a.use_principal:
        raise ClientError(EXIT_PARAMS, "invalid params: --principal names one principal, --all every one; use one")
    host = config.normalize_host(a.R.base_url)
    creds = load()
    h = creds.get(host)
    if not h or not h.get("principals"):
        raise ClientError(1, "not logged in to %s" % host)
    names = sorted(h["principals"]) if a.all else [stored(creds, host, a.use_principal)[0]]
    for p in names:
        if p not in h["principals"]:
            raise ClientError(1, "no stored token for %s on %s (stored: %s)" % (p, host, ", ".join(sorted(
                h["principals"]))))
    for p in names:
        if h["principals"][p].get("storage") == "keyring":
            _kr_delete(host, p)
        del h["principals"][p]
    left = sorted(h["principals"])
    if not left:
        del creds[host]
    elif h.get("active") not in left:
        h["active"] = left[0]
    save(creds)
    print("logged out of %s: %s; %s still valid on the host until rotated (provenstream auth rotate before logging "
          "out, or ask the operator)%s" % (host, ", ".join(names), "that token is" if len(names) == 1 else
                                           "those tokens are",
                                           "; active now: %s" % h["active"] if left else ""))
    if os.environ.get("PROVENSTREAM_TOKEN"):
        print("provenstream: warning: PROVENSTREAM_TOKEN is set and is not affected: commands still send it",
              file=sys.stderr)
    return 0


def _status_of(base_url: str, host: str, creds: Dict[str, Any], a, resolved: bool) -> Dict[str, Any]:
    h = creds.get(host) or {}
    if resolved:
        c = token_for(base_url, a.token_file, a.token, a.use_principal, warn=False)
    else:
        p, entry = stored(creds, host, None)
        t = stored_token(host, p, entry) if entry else None
        c = Chosen(t, entry.get("storage", "file") if entry and t else "none", p if t else None, host)
    p = c.principal or (a.use_principal if resolved else None) or h.get("active")
    entry = (h.get("principals") or {}).get(p) if p else None
    out: Dict[str, Any] = {"host": host, "active": h.get("active"), "principals": sorted(h.get("principals") or {}),
                           "token_source": c.source}
    if c.principal:
        out["principal"] = c.principal
        if (entry or {}).get("name"):
            out["name"] = entry["name"]
        out["storage"] = describe_storage(c.source, host, c.principal)
    if c.token is None:
        out["ok"] = False
        out["error"] = "no token (provenstream login --base-url %s)" % host
        out["exit"] = EXIT_UNAUTHORIZED
        return out
    try:
        who = client.Remote(base_url, c.token).handle("whoami")
        out["whoami"] = who
        out["ok"] = True
    except ClientError as x:
        out["ok"], out["error"], out["exit"] = False, x.message, x.exit_code
    return out


def cmd_status(a) -> int:
    creds = load()
    resolved = config.normalize_host(a.R.base_url)
    hosts = [resolved] if a.base_url else [resolved] + sorted(h for h in creds if h != resolved)
    rows = [_status_of(a.R.base_url if h == resolved else h, h, creds, a, h == resolved) for h in hosts]
    bad = [r for r in rows if not r["ok"] and (r["host"] == resolved or r["token_source"] != "none")]
    if a.json or getattr(a, "field", None) is not None:
        out = {"hosts": [{k: v for k, v in r.items() if k != "exit"} for r in rows], "resolved": resolved,
               "credentials": credentials_path()}
        if getattr(a, "field", None) is not None:
            client.show(out, a.field)                    # -q: one value of the --json object
        else:
            print(json.dumps(out, sort_keys=True))
        return 0
    for r in rows:
        print("%s%s" % (r["host"], "  (the resolved host)" if r["host"] == resolved and len(rows) > 1 else ""))
        if r.get("whoami"):
            w = r["whoami"]
            print("  logged in as %s%s, token from %s%s" % (w.get("principal_id"), " (%s)" % r["name"] if r.get("name")
                                                           else "", r["token_source"],
                                                           ": " + r["storage"] if r.get("storage") else ""))
        else:
            print("  %s%s" % ("token from %s: " % r["token_source"] if r["token_source"] != "none" else "",
                               r.get("error")))
        if r["principals"]:
            names = {p: (e or {}).get("name") for p, e in ((creds.get(r["host"]) or {}).get("principals") or {}).items()}
            print("  stored: %s (active: %s)" % (", ".join(p + (" (%s)" % names[p] if names.get(p) else "")
                                                         for p in r["principals"]), r["active"]))
    if any(r["host"] == resolved and r["token_source"] == "env" for r in rows):
        print("note: PROVENSTREAM_TOKEN is set, and wins over a stored token")
    if bad:
        return EXIT_UNAUTHORIZED if any(r["exit"] == EXIT_UNAUTHORIZED for r in bad) else bad[0]["exit"]
    return 0


def cmd_rotate(a) -> int:
    if a.token_file or a.token:
        raise ClientError(EXIT_PARAMS, "invalid params: auth rotate rotates a stored token, and saves the new one "
                                       "where the old one was; to rotate %s's token, use it with call token.rotate"
                          % ("--token-file" if a.token_file else "--token"))
    host = config.normalize_host(a.R.base_url)
    creds = load()
    p, entry = stored(creds, host, a.use_principal)
    if entry is None:
        raise ClientError(EXIT_UNAUTHORIZED, "unauthorized: no stored token %son %s (provenstream login --base-url "
                                             "%s)" % ("for %s " % p if p else "", host, host))
    old = stored_token(host, p, entry)
    if not old:
        raise ClientError(EXIT_UNAUTHORIZED, "unauthorized: the stored token of %s on %s is missing; log in again"
                          % (p, host))
    storage = entry.get("storage", "file")
    try:
        put(host, p, old, storage, make_active=False)      # can it be written? before revoking
    except OSError as x:
        raise ClientError(1, "rotate: cannot write %s (%s); nothing rotated"
                          % (describe_storage(storage, host, p), x))
    new = client.Remote(a.R.base_url, old).handle("token.rotate")["token"]
    try:
        put(host, p, new, storage, make_active=False)
    except Exception as x:
        print("provenstream: rotate FAILED after the host rotated: the new token could not be saved to %s (%s). The "
              "old token is already revoked, so %s cannot sign in to %s: ask the host's operator to rotate it "
              "(provenstream token rotate %s), then provenstream login"
              % (describe_storage(storage, host, p), type(x).__name__, p, host, p), file=sys.stderr)
        return 1
    print("rotated the token of %s on %s; the old one is revoked; the new one is in %s"
          % (p, host, describe_storage(storage, host, p)))
    if os.environ.get("PROVENSTREAM_TOKEN"):
        print("provenstream: warning: PROVENSTREAM_TOKEN is set and was not rotated; commands still send it",
              file=sys.stderr)
    return 0
