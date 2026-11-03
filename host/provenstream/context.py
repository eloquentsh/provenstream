# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""Where a command is: the project file, the current stream, aliases, short ids, and a proof URL from git.

The project file is `.provenstream/client.json`, the nearest one found walking up from the current directory (never
above $HOME's parent, nor past the filesystem root; the user config directory, ~/.provenstream by default, is never
taken for a project's). It holds no secret, so it is safe to commit:

    {"host": "https://streams.example", "proof_revision_url": "<repo>/commit/<hash>", "stream": "<uuid>",
     "aliases": {"ledger": "<uuid>"}}

Every key is optional. Outside a project the user config (`config.py`: `stream`, `proof_revision_url`, `aliases`)
stands in for it. Precedence everywhere: flag > env (`PROVENSTREAM_STREAM`, `PROVENSTREAM_BASE_URL`) > project file >
user config. The project's `host` is a default like config `default_host`, below `--base-url` and
`PROVENSTREAM_BASE_URL`, and like it never selects remote mode (`mode.py`, rule 3).

Stream arguments (`resolve_stream`) are a full UUID; an alias, the project's before the user's; or a unique suffix of
8 or more hex digits (dashes optional) of a stream known here: an alias's, a current stream, or one of the last
`RECENT` streams opened or used (recent.json in the config directory). Stream ids are UUIDv7, whose leading digits are
a timestamp, so streams opened together share a prefix and a prefix is never accepted. Ambiguous or unknown is
invalid params (exit 5), naming the candidates. Revisions (`resolve_revision`) take a short revision, a unique prefix
of 7 or more hex digits of a commit and optionally `/<package>` (bare hex is the root package), among the revisions
served (`revisions.list`) or an engines directory's.

A proof URL from git (`proof_url_from_git`): in a git repository with a `provenstream.json` (a layer project, or this
repository), `<origin as https, no .git>/commit/<HEAD>`, or `/tree/<HEAD>/<package>` when the nearest
`provenstream.json` is in a package below the repository's top, refused when tracked files have changes (untracked files do
not count, as for `git describe --dirty`) or when no remote branch contains HEAD: a host builds the engine from a
commit it can fetch.
"""
from __future__ import annotations
import os, re, subprocess, sys, urllib.parse
from dataclasses import dataclass
from typing import Any, Dict, Iterable, List, Mapping, Optional, Tuple

from . import config, ids
from .client import ClientError, EXIT_PARAMS

PROJECT_DIR, PROJECT_FILE = ".provenstream", "client.json"
PROJECT_KEYS = ("host", "proof_revision_url", "stream", "aliases")
RECENT = 50
ALIAS = re.compile(r"[A-Za-z][A-Za-z0-9._-]{0,63}")
HEX = re.compile(r"[0-9a-f]+")


# -- the project file -----------------------------------------------------------------------------------------------

def find_project(cwd: Optional[str] = None, env: Mapping[str, str] = os.environ) -> Optional[str]:
    """The path of the nearest project file at or above `cwd`, or None."""
    try:
        d = os.path.realpath(cwd or os.getcwd())
    except OSError:                                       # the current directory is gone: no project
        return None
    home = os.path.realpath(env.get("HOME") or os.path.expanduser("~"))
    stop = os.path.dirname(home) if home != os.path.dirname(home) else None
    skip = {os.path.realpath(config.directory(env)), os.path.join(home, PROJECT_DIR)}
    while d != stop:
        cand = os.path.join(d, PROJECT_DIR)
        if os.path.realpath(cand) not in skip and os.path.isfile(os.path.join(cand, PROJECT_FILE)):
            return os.path.join(cand, PROJECT_FILE)
        up = os.path.dirname(d)
        if up == d:
            return None
        d = up
    return None


@dataclass
class Project:
    path: Optional[str]           # the project file, or None outside a project
    data: Dict[str, Any]


def load_project(env: Mapping[str, str] = os.environ, cwd: Optional[str] = None) -> Project:
    p = find_project(cwd, env)
    if p is None:
        return Project(None, {})
    data = config.read_json(p)
    bad = sorted(set(data) - set(PROJECT_KEYS))
    if bad:
        raise ClientError(EXIT_PARAMS, "invalid params: %s: unknown keys %s (known: %s)"
                          % (p, ", ".join(bad), ", ".join(PROJECT_KEYS)))
    for k in ("host", "proof_revision_url", "stream"):
        if k in data and not isinstance(data[k], str):
            raise ClientError(EXIT_PARAMS, "invalid params: %s: %s must be a string" % (p, k))
    if not isinstance(data.get("aliases", {}), dict):
        raise ClientError(EXIT_PARAMS, "invalid params: %s: aliases must be an object" % p)
    return Project(p, data)


def save_project(path: str, data: Dict[str, Any]) -> None:
    os.makedirs(os.path.dirname(path), exist_ok=True)
    config.write_atomic(path, data, mode=0o644)          # no secrets: meant to be committed


def project_host(env: Mapping[str, str] = os.environ) -> Optional[str]:
    return load_project(env).data.get("host") or None


class Place:
    """Where `stream use` and `stream alias` write: the project file if there is one (or `--project`, creating one in
    the current directory), else the user config."""

    def __init__(self, project_flag: bool = False, env: Mapping[str, str] = os.environ):
        self.env = env
        pr = load_project(env)
        if pr.path is None and project_flag:
            pr = Project(os.path.join(os.getcwd(), PROJECT_DIR, PROJECT_FILE), {})
        self.project = pr

    @property
    def name(self) -> str:
        return self.project.path or config.path(self.env)

    def read(self) -> Dict[str, Any]:
        return dict(self.project.data) if self.project.path else config.load(self.env)

    def write(self, data: Dict[str, Any]) -> None:
        if self.project.path:
            save_project(self.project.path, data)
            self.project.data = data
        else:
            config.write_atomic(os.path.join(config.ensure_directory(self.env), "config.json"), data)


# -- aliases and the current stream ---------------------------------------------------------------------------------

def check_alias(name: str) -> str:
    if not ALIAS.fullmatch(name) or HEX.fullmatch(name.replace("-", "").lower()):
        raise ClientError(EXIT_PARAMS, "invalid params: alias %r: a letter, then letters, digits, '.', '_' or '-' (at "
                                       "most 64), and not all hex digits, which would read as an id's suffix" % name)
    return name


def aliases(env: Mapping[str, str] = os.environ) -> List[Tuple[str, str, str]]:
    """Every alias as (name, stream, where): the project's first, then the user's not shadowed by one."""
    out, seen = [], set()
    pr = load_project(env)
    for where, m in (("project", pr.data.get("aliases") or {}), ("config", config.aliases(env))):
        for n, s in sorted(m.items()):
            if n not in seen and isinstance(s, str):
                seen.add(n)
                out.append((n, s.lower(), where))
    return out


def alias_of(stream: str, env: Mapping[str, str] = os.environ) -> Optional[str]:
    return next((n for n, s, _ in aliases(env) if s == stream), None)


def label(stream: str, env: Mapping[str, str] = os.environ) -> str:
    """`<alias or last 8> (<uuid>)`, as commands name a stream they resolved."""
    return "%s (%s)" % (alias_of(stream, env) or stream[-8:], stream)


def current(env: Mapping[str, str] = os.environ) -> Tuple[Optional[str], str]:
    """The current stream as given (an id, alias or suffix, unresolved) and where it came from."""
    if env.get("PROVENSTREAM_STREAM"):
        return env["PROVENSTREAM_STREAM"], "env (PROVENSTREAM_STREAM)"
    pr = load_project(env)
    if pr.data.get("stream"):
        return pr.data["stream"], "project (%s)" % pr.path
    v = config.get("stream", env)
    if v:
        return v, "config (%s)" % config.path(env)
    return None, "none"


def recent(env: Mapping[str, str] = os.environ) -> List[str]:
    got = config.read_json(os.path.join(config.directory(env), "recent.json")).get("streams")
    return [s for s in got if isinstance(s, str)] if isinstance(got, list) else []


def remember(stream: str, env: Mapping[str, str] = os.environ) -> None:
    """Put `stream` first in the recent list (at most `RECENT`)."""
    rest = [s for s in recent(env) if s != stream]
    config.write_atomic(os.path.join(config.ensure_directory(env), "recent.json"),
                        {"streams": ([stream] + rest)[:RECENT]})


def _known(env: Mapping[str, str]) -> List[str]:
    out: List[str] = []
    cands: List[Optional[str]] = [s for _, s, _ in aliases(env)]
    pr = load_project(env)
    cands += [env.get("PROVENSTREAM_STREAM"), pr.data.get("stream"), config.get("stream", env)] + recent(env)
    for s in cands:
        if s and ids.CANONICAL_ID.fullmatch(s.lower()) and s.lower() not in out:
            out.append(s.lower())
    return out


def canonical(arg: str) -> Optional[str]:
    """`arg` as a canonical UUID if it is one (any case, dashes optional), else None."""
    h = arg.strip().lower().replace("-", "")
    if len(h) == 32 and HEX.fullmatch(h):
        s = "%s-%s-%s-%s-%s" % (h[:8], h[8:12], h[12:16], h[16:20], h[20:])
        return s if ids.CANONICAL_ID.fullmatch(s) else None
    return None


def resolve_stream(arg: str, env: Mapping[str, str] = os.environ) -> str:
    """A stream argument as a full UUID, by the rules above, or invalid params naming the candidates."""
    full = canonical(arg)
    if full:
        return full
    al = {n: s for n, s, _ in aliases(env)}                   # a project alias shadows a user one
    if arg in al:
        return al[arg]
    h = arg.strip().lower().replace("-", "")
    known = _known(env)
    if HEX.fullmatch(h or "x") and len(h) >= 8:
        hits = [s for s in known if s.replace("-", "").endswith(h)]
        if len(hits) == 1:
            return hits[0]
        if hits:
            raise ClientError(EXIT_PARAMS, "invalid params: %r is the suffix of %d streams known here: %s; give more "
                                           "digits" % (arg, len(hits), ", ".join(hits)))
        pre = [s for s in known if s.replace("-", "").startswith(h)]
        if pre:
            raise ClientError(EXIT_PARAMS, "invalid params: %r is a prefix (of %s); stream ids are UUIDv7, whose "
                                           "leading digits are a timestamp, so give the id's last digits (8 or more) "
                                           "instead" % (arg, ", ".join(pre)))
        why = "no stream known here (aliases, the current stream, the recent ones) ends in %r" % arg
    elif HEX.fullmatch(h or "x"):
        why = "a suffix needs 8 or more hex digits"
    else:
        why = "not a UUID, an alias (known: %s), or a hex suffix" % (", ".join(sorted(al)) or "none")
    raise ClientError(EXIT_PARAMS, "invalid params: stream %r: %s" % (arg, why))


def stream_or_current(arg: Optional[str], command: str, env: Mapping[str, str] = os.environ,
                      say: bool = True, how: str = "STREAM") -> str:
    """The stream a command acts on: `arg`, else the current stream; on a terminal (stderr) it says which, unless
    `arg` was a full UUID already."""
    given = arg or current(env)[0]
    if not given:
        raise ClientError(EXIT_PARAMS, "invalid params: %s needs a stream: name one (%s), or set the current stream "
                                       "with provenstream stream use STREAM (or PROVENSTREAM_STREAM)" % (command, how))
    s = resolve_stream(given, env)
    if say and given != s and sys.stderr is not None and sys.stderr.isatty():
        print("stream: %s" % label(s, env), file=sys.stderr)
    return s


def use(stream: str, place: Place) -> None:
    data = place.read()
    data["stream"] = stream
    place.write(data)


# -- revisions ------------------------------------------------------------------------------------------------------

def split_short(arg: str) -> Tuple[str, str]:
    """`(hex, package)` of a short revision: 7 or more hex digits, then optionally `/<package>`."""
    a = arg.strip()
    h, _, pkg = a.partition("/")
    return h.lower(), pkg


def resolve_revision(arg: str, revisions: Iterable[str]) -> str:
    """A short revision (7+ hex digits, optionally `/<package>`; bare hex is the root package) as the one revision of
    `revisions` it names, or invalid params."""
    from .revisions import split_key
    h, pkg = split_short(arg)
    revs = sorted(set(revisions))
    if not looks_like_revision(arg):
        raise ClientError(EXIT_PARAMS, "invalid params: revision %r: 7 or more hex digits, optionally /<package>" % arg)
    hits = [r for r in revs if split_key(r)[0].startswith(h) and split_key(r)[1] == pkg]
    if len(hits) == 1:
        return hits[0]
    raise ClientError(EXIT_PARAMS, "invalid params: revision %r: %s" % (
        arg, "names %d revisions: %s" % (len(hits), ", ".join(hits)) if hits else
        "no revision served is it (served: %s)" % (", ".join(revs) or "none")))


def looks_like_revision(arg: str) -> bool:
    """7 or more hex digits (at most 64), optionally followed by `/<package>`."""
    from .revisions import valid_package
    h, pkg = split_short(arg)
    return 7 <= len(h) <= 64 and bool(HEX.fullmatch(h)) and (not pkg or valid_package(pkg)) and \
        not arg.strip().endswith("/")


# -- a proof URL from git -------------------------------------------------------------------------------------------

def https_of(remote: str) -> Optional[str]:
    """A git remote URL as the https URL of the repository (no userinfo, no .git, no trailing slash), or None for a
    local path or a scheme without a host."""
    r = remote.strip()
    m = re.fullmatch(r"(?:[^@/]+@)?([^:/]+):(?!//)(.+)", r)            # scp-like: git@host:owner/repo.git
    if m and "://" not in r:
        host, path = m.group(1), m.group(2)
        port = ""
    else:
        u = urllib.parse.urlsplit(r)
        if u.scheme not in ("https", "http", "ssh", "git", "git+ssh", "ssh+git") or not u.hostname:
            return None
        host, path = u.hostname, u.path
        port = ":%d" % u.port if u.port and u.scheme in ("https", "http") and u.port not in (80, 443) else ""
    path = path.strip("/")
    if path.endswith(".git"):
        path = path[:-4]
    path = path.rstrip("/")
    if not path:
        return None
    return "https://%s%s/%s" % (host.lower(), port, path)


def _git(cwd: str, *args: str) -> Tuple[int, str]:
    try:
        p = subprocess.run(["git", "-C", cwd] + list(args), capture_output=True, text=True)
    except OSError:
        return 127, ""
    return p.returncode, p.stdout.strip()


def proof_url_from_git(cwd: Optional[str] = None) -> str:
    """The proof URL of the repository at `cwd`'s HEAD, by the rules above, or ClientError (exit 1) saying why not."""
    cwd = os.path.realpath(cwd or os.getcwd())
    fail = lambda why: ClientError(1, "no proof URL from git: %s" % why)
    code, top = _git(cwd, "rev-parse", "--show-toplevel")
    if code != 0:
        raise fail("%s is not in a git repository (give PROOF_URL)" % cwd)
    d, top = cwd, os.path.realpath(top)
    while not os.path.isfile(os.path.join(d, "provenstream.json")):
        if d == top or os.path.dirname(d) == d:
            raise fail("no provenstream.json between %s and the repository's top, %s: not a proof project" % (cwd, top))
        d = os.path.dirname(d)
    code, head = _git(cwd, "rev-parse", "HEAD")
    if code != 0 or not head:
        raise fail("the repository has no commit yet")
    code, dirty = _git(cwd, "status", "--porcelain", "--untracked-files=no")
    if code != 0 or dirty:
        raise fail("the working tree has uncommitted changes to tracked files; commit (and push) them, so the "
                   "stream names the code you have")
    code, origin = _git(cwd, "remote", "get-url", "origin")
    if code != 0 or not origin:
        raise fail("the repository has no remote named origin")
    url = https_of(origin)
    if url is None:
        raise fail("origin (%s) is not a URL a host could fetch from" % origin)
    code, on = _git(cwd, "branch", "-r", "--contains", "HEAD")
    if code != 0 or not on:
        raise fail("HEAD (%s) is on no remote branch: push it first, since a host can only build an engine from a "
                   "commit it can fetch" % head[:12])
    from .revisions import revision_url
    rel = os.path.relpath(d, top)
    return revision_url(url, head, "" if rel == "." else rel.replace(os.sep, "/"))
