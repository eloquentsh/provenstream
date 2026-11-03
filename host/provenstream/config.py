# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The command line's own files: config.json (settings, no secrets) and credentials.json (`auth.py`), in one directory.

The directory is `PROVENSTREAM_CONFIG_DIR`, else ~/.provenstream (the default database's directory too, which stays
there whatever this names). It is created 0700, and every file in it is written 0600 and atomically (a temporary file
in the same directory, then a rename), so a reader never sees half a file and an interrupted write leaves the old one.

Settings (`KEYS`), each with its environment variable and its default, resolve flag > env > config > default
everywhere (`provenstream config list` shows which won):

- `default_host`: the host of remote mode when neither `--base-url` nor `PROVENSTREAM_BASE_URL` names one, else
  the local host, http://127.0.0.1:8080 (`client.DEFAULT_BASE_URL`). It is a default and not a choice: it never
  selects remote mode (`mode.py`, rule 3), so a configured host does not turn `serve` on a laptop into an error.
- `local.engines`: the engines directory when neither `--engines` nor `PROVENSTREAM_ENGINES` names one.
- `stream`: the current stream outside a project (`provenstream stream use`), below `PROVENSTREAM_STREAM` and a
  project file's (`context.py`).
- `proof_revision_url`: what `stream open` opens with no PROOF_URL outside a project.
- `aliases.NAME`: a stream's alias, a full UUID (`provenstream stream alias`); `aliases` alone is the whole map.

A project file's `host`, `stream` and `proof_revision_url` rank between the environment and this file, and `config
list` says when one won. Only these keys are accepted, so a typo is refused instead of stored and silently ignored.
"""
from __future__ import annotations
import json, os, tempfile, urllib.parse
from typing import Any, Callable, Dict, Mapping, NamedTuple, Optional, Tuple

from . import client
from .client import ClientError, EXIT_PARAMS


def directory(env: Mapping[str, str] = os.environ) -> str:
    return os.path.abspath(os.path.expanduser(env.get("PROVENSTREAM_CONFIG_DIR") or os.path.join("~", ".provenstream")))


def ensure_directory(env: Mapping[str, str] = os.environ) -> str:
    d = directory(env)
    if not os.path.isdir(d):
        os.makedirs(d, mode=0o700)
        os.chmod(d, 0o700)            # makedirs' mode is masked by the umask
    return d


def write_atomic(path: str, data: Any, mode: int = 0o600) -> None:
    """`data` as JSON at `path`, 0600 (or `mode`), by a rename: the old file or the new one, never a torn one."""
    d = os.path.dirname(path)
    fd, tmp = tempfile.mkstemp(prefix=".tmp-", dir=d)      # mkstemp creates it 0600
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2, sort_keys=True)
            f.write("\n")
            f.flush()
            os.fsync(f.fileno())
        os.chmod(tmp, mode)
        os.replace(tmp, path)
    except BaseException:
        try:
            os.unlink(tmp)
        except OSError:
            pass
        raise


def read_json(path: str) -> Dict[str, Any]:
    """A file's JSON object, or {} when there is no file."""
    try:
        with open(path, encoding="utf-8") as f:
            got = json.load(f)
    except FileNotFoundError:
        return {}
    except (OSError, ValueError) as x:
        raise ClientError(EXIT_PARAMS, "invalid params: cannot read %s: %s" % (path, x))
    if not isinstance(got, dict):
        raise ClientError(EXIT_PARAMS, "invalid params: %s is not a JSON object" % path)
    return got


def normalize_host(url: str) -> str:
    """A host's name as credentials are keyed under it: scheme, lowercase host, the port unless it is the scheme's
    default, the path, and no trailing slash, so `HTTPS://Streams.Example:443/` and `https://streams.example` are one
    host. Userinfo, query and fragment are dropped."""
    u = urllib.parse.urlsplit(url.strip())
    scheme = u.scheme.lower()
    if scheme not in ("http", "https") or not u.hostname:
        raise ClientError(EXIT_PARAMS, "invalid params: %r is not an http(s) URL with a host" % url)
    host = u.hostname.lower()
    if ":" in host:
        host = "[%s]" % host                       # an IPv6 literal
    try:
        port = u.port
    except ValueError:
        raise ClientError(EXIT_PARAMS, "invalid params: %r has an invalid port" % url)
    if port is not None and port != {"http": 80, "https": 443}[scheme]:
        host += ":%d" % port
    return "%s://%s%s" % (scheme, host, u.path.rstrip("/"))


def _engines_dir(value: str) -> str:
    return os.path.abspath(os.path.expanduser(value))


def _stream_id(value: str) -> str:
    from .context import canonical
    s = canonical(value)
    if s is None:
        raise ClientError(EXIT_PARAMS, "invalid params: %r is not a stream id (a UUID; provenstream stream use takes "
                                       "an alias or a suffix too)" % value)
    return s


def _proof_url(value: str) -> str:
    from .revisions import split_url
    if split_url(value) is None:
        raise ClientError(EXIT_PARAMS, "invalid params: %r is not a proof revision URL (<repository>/commit/<hash>)"
                          % value)
    return value


class Key(NamedTuple):
    env: Optional[str]
    default: Optional[str]
    check: Callable[[str], str]      # the value as stored, or ClientError
    meaning: str


KEYS: Dict[str, Key] = {
    "default_host": Key("PROVENSTREAM_BASE_URL", client.DEFAULT_BASE_URL, normalize_host,
                        "the host of remote mode when none is named (it never selects remote mode)"),
    "local.engines": Key("PROVENSTREAM_ENGINES", None, _engines_dir, "the engines directory when none is named"),
    "stream": Key("PROVENSTREAM_STREAM", None, _stream_id, "the current stream outside a project"),
    "proof_revision_url": Key(None, None, _proof_url, "what stream open opens with no PROOF_URL"),
}
ALIASES = "aliases"
PROJECT_NAME = {"default_host": "host", "stream": "stream", "proof_revision_url": "proof_revision_url"}


def path(env: Mapping[str, str] = os.environ) -> str:
    return os.path.join(directory(env), "config.json")


def load(env: Mapping[str, str] = os.environ) -> Dict[str, Any]:
    return read_json(path(env))


def get(key: str, env: Mapping[str, str] = os.environ) -> Optional[str]:
    """The configured value of `key` (the file only: no flag, no env, no default)."""
    v = load(env).get(key)
    return v if isinstance(v, str) else None


def aliases(env: Mapping[str, str] = os.environ) -> Dict[str, str]:
    m = load(env).get(ALIASES)
    return {n: s for n, s in m.items() if isinstance(s, str)} if isinstance(m, dict) else {}


def alias_name(key: str) -> Optional[str]:
    """NAME of `aliases.NAME`, checked; None for any other key."""
    if not key.startswith(ALIASES + "."):
        return None
    from .context import check_alias
    return check_alias(key[len(ALIASES) + 1:])


def known(key: str) -> Key:
    if key not in KEYS:
        raise ClientError(EXIT_PARAMS, "invalid params: no setting %r (known: %s, aliases.NAME)"
                          % (key, ", ".join(sorted(KEYS))))
    return KEYS[key]


def _write(c: Dict[str, Any], env: Mapping[str, str]) -> None:
    write_atomic(os.path.join(ensure_directory(env), "config.json"), c)


def set_value(key: str, value: str, env: Mapping[str, str] = os.environ) -> str:
    name = alias_name(key)
    stored = _stream_id(value) if name else known(key).check(value)
    c = load(env)
    if name:
        c[ALIASES] = dict(aliases(env), **{name: stored})
    else:
        c[key] = stored
    _write(c, env)
    return stored


def unset(key: str, env: Mapping[str, str] = os.environ) -> bool:
    name = alias_name(key)
    c = load(env)
    if name:
        m = aliases(env)
        if name not in m:
            return False
        del m[name]
        c[ALIASES] = m
        if not m:
            del c[ALIASES]
    else:
        known(key)
        if key not in c:
            return False
        del c[key]
    _write(c, env)
    return True


def effective(key: str, flag: Optional[str], env: Mapping[str, str] = os.environ,
              project: Optional[Tuple[Optional[str], Mapping[str, Any]]] = None) -> Tuple[Optional[str], str]:
    """`key`'s value and where it came from: flag > env > project file (`project`: its path and data) > config >
    default."""
    k = known(key)
    if flag:
        return flag, "flag"
    if k.env and env.get(k.env):
        return env[k.env], "env"
    if project and project[0] and key in PROJECT_NAME and project[1].get(PROJECT_NAME[key]):
        return project[1][PROJECT_NAME[key]], "project"
    v = get(key, env)
    if v is not None:
        return v, "config"
    return k.default, "default"
