# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""One revision per stream: which engine judges which stream.

A stream is bound for life to the revision its `stream.open` names in `proof_revision_url` (no event changes it:
`proof_revision_fixed`, `proof_revision_unique`, `Layer.ValidX.proof_revision_unique`). The host keeps that promise in
operation by serving each stream only with the engine built from that revision, and never another.

A revision is a commit (40 or 64 lowercase hex digits) and a package path, so one commit serves all the proofs of its
repository side by side (the core, examples/log, examples/principals, examples/tasks, examples/work,
examples/solochangecontrol, examples/email, examples/emailtriage, examples/email-triage-and-reply, tests/tower). Its
URL, read as the core's rule reads it (`validRevisionUrl`, Event.lean):

- `<repo>/commit/<commit>`, `<repo>#<commit>` or `<repo>@<commit>`: the repository's root package;
- `<repo>/tree/<commit>/<package>`: another package of that commit, `<package>` one or more `/`-separated segments
  of `[A-Za-z0-9._-]`, none empty, `.` or `..`.

Its key (`revision_key`), in the revision map and everywhere the host names it, is `<commit>` for the root package and
`<commit>/<package>` for another. The repository part must name the repository the engine was built from
(`stamped_repo`, compared by `same_repository`), or `stream.open` is refused with the host's
`repository_must_match_the_engine`: a commit hash says nothing of where it lives, and a stream should not claim a
repository its engine was not built from. Only `stream.open` checks it; a stream already open is served by its
revision's engine whatever its URL says.

The revision map is a JSON file in an engines directory (`provenstream install` writes it, never replacing an entry):

    {"engines": {"<commit>": "<commit>/_root/engine", "<commit>/examples/tasks": "<commit>/examples/tasks/engine"}}

A relative path is relative to the file. Beside each engine, `PROVENANCE.json` (written by `provenstream build`) says how
it was built. Each engine must report, when started, exactly the revision it is listed under: its commit and its
package.
"""
from __future__ import annotations
import json, os, re, tempfile
from typing import Dict, List, NamedTuple, Optional, Tuple

HEX_REVISION = re.compile(r"(?:[0-9a-f]{40}|[0-9a-f]{64})")
SEGMENT = r"[A-Za-z0-9._-]+"
PACKAGE = re.compile(r"%s(?:/%s)*" % (SEGMENT, SEGMENT))
REVISION_KEY = re.compile(r"(?:[0-9a-f]{40}|[0-9a-f]{64})(?:/%s)*" % SEGMENT)
SEPARATORS = ("/commit/", "#", "@")
ROOT_DIR = "_root"                    # the directory of the root package's engine, and of its cached description


class RevisionMapError(ValueError):
    pass


class Revision(NamedTuple):
    """A revision URL read: the repository, the commit, the package ("" for the repository's root)."""
    repo: str
    commit: str
    package: str

    @property
    def key(self) -> str:
        return revision_key(self.commit, self.package)


def valid_package(p: object) -> bool:
    """A package path as the core reads it (`validPackage`): segments of [A-Za-z0-9._-], none empty, `.` or `..`."""
    return isinstance(p, str) and PACKAGE.fullmatch(p) is not None and all(s not in (".", "..") for s in p.split("/"))


def revision_key(commit: str, package: str = "") -> str:
    """The key of a revision: the commit, then `/` and the package when it is not the root."""
    return commit + "/" + package if package else commit


def split_key(key: str) -> Tuple[str, str]:
    """`(commit, package)` of a revision key."""
    commit, _, package = key.partition("/")
    return commit, package


def valid_key(key: object) -> bool:
    if not (isinstance(key, str) and REVISION_KEY.fullmatch(key)):
        return False
    return not split_key(key)[1] or valid_package(split_key(key)[1])


def revision_url(repo: str, commit: str, package: str = "") -> str:
    """The canonical URL of a revision: `/commit/` for the root package, `/tree/<commit>/<package>` for another."""
    repo = repo.rstrip("/")
    return "%s/tree/%s/%s" % (repo, commit, package) if package else "%s/commit/%s" % (repo, commit)


def short(key: str) -> str:
    """A revision as people write it: its commit's first 7 hex digits, and its package."""
    commit, package = split_key(key)
    return commit[:7] + ("/" + package if package else "")


def _repo_ok(repo: str) -> bool:
    parts = repo.split("://")
    if len(parts) != 2:
        return False
    scheme, rest = parts
    segments = rest.split("/")
    return bool(scheme) and all((c.isascii() and c.isalnum()) or c in "+-." for c in scheme) and \
        len(segments) >= 2 and all(segments)


def parse_url(url: object) -> Optional[Revision]:
    """The revision a proof revision URL names, read as the core's rule reads it; None when the rule would refuse
    it."""
    if not isinstance(url, str):
        return None
    if len(url) > 2048 or not all(32 < ord(c) and ord(c) != 127 for c in url):
        return None
    for sep in SEPARATORS:
        parts = url.split(sep)
        if len(parts) == 2 and _repo_ok(parts[0]) and HEX_REVISION.fullmatch(parts[1]):
            return Revision(parts[0], parts[1], "")
    parts = url.split("/tree/")
    if len(parts) == 2 and _repo_ok(parts[0]):
        commit, _, package = parts[1].partition("/")
        if HEX_REVISION.fullmatch(commit) and package and valid_package(package):
            return Revision(parts[0], commit, package)
    return None


def split_url(url: object) -> Optional[Tuple[str, str]]:
    """`(repository, revision key)` of a proof revision URL; None when the core's rule would refuse it."""
    got = parse_url(url)
    return (got.repo, got.key) if got else None


def revision_of_url(url: object) -> Optional[str]:
    """The revision key a proof revision URL names; None when the core's rule would refuse it."""
    got = parse_url(url)
    return got.key if got else None


SCP_LIKE = re.compile(r"(?:[A-Za-z0-9._-]+@)?([A-Za-z0-9.-]+):(?!//)(.+)")


def normal_repo(repo: str) -> str:
    """A repository URL in one spelling, so that the ways git and people write the same repository compare equal: the
    scheme `https` for `http`, `https`, `ssh` and `git` and for git's `user@host:path` form; no user, no default port;
    the host in lowercase; no trailing `/` and no `.git`; on github.com, whose names ignore case, the path in
    lowercase too. Other schemes (`file://`) keep their path as it is. This is the host's reading, not the base rule's:
    the proofs see the URL as written."""
    r = repo.strip()
    m = SCP_LIKE.fullmatch(r) if "://" not in r else None
    if m:
        r = "ssh://%s/%s" % (m.group(1), m.group(2).lstrip("/"))
    scheme, sep, rest = r.partition("://")
    if not sep:
        return r.rstrip("/")
    scheme = scheme.lower()
    host, _, path = rest.partition("/")
    if scheme in ("http", "https", "ssh", "git", "git+ssh", "ssh+git"):
        host = host.rsplit("@", 1)[-1].lower()
        for default in (":80", ":443", ":22", ":9418"):
            if host.endswith(default):
                host = host[:-len(default)]
        scheme = "https"
    path = path.rstrip("/")
    if path.endswith(".git"):
        path = path[:-4].rstrip("/")
    if host == "github.com" or host == "www.github.com":
        host, path = "github.com", path.lower()
    return "%s://%s/%s" % (scheme, host, path) if host or path else "%s://" % scheme


def same_repository(a: str, b: str) -> bool:
    """`a` and `b` name the same repository (`normal_repo`)."""
    return normal_repo(a) == normal_repo(b)


def stamped_repo(describe: Optional[dict], command: List[str]) -> Optional[str]:
    """The repository an engine was built from: what it reports (`repo` in its description), else the `repo_url` of the
    `PROVENANCE.json` beside it (an installed engine has one); None when neither says."""
    repo = (describe or {}).get("repo")
    if isinstance(repo, str) and repo and repo != "unknown":
        return repo
    if command:
        try:
            with open(os.path.join(os.path.dirname(command[0]), "PROVENANCE.json"), encoding="utf-8") as f:
                repo = json.load(f).get("repo_url")
        except (OSError, ValueError, AttributeError):
            return None
        if isinstance(repo, str) and repo:
            return repo
    return None


def load_map(path: str) -> Dict[str, List[str]]:
    """The revision map: {revision key: engine command}. A missing file is an empty map."""
    if not os.path.exists(path):
        return {}
    try:
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, ValueError) as x:
        raise RevisionMapError("%s: %s" % (path, x)) from x
    if not isinstance(data, dict) or set(data) != {"engines"} or not isinstance(data["engines"], dict):
        raise RevisionMapError("%s: expected {\"engines\": {revision: path}}" % path)
    base = os.path.dirname(os.path.abspath(path))
    out = {}
    for r, p in data["engines"].items():
        if not valid_key(r):
            raise RevisionMapError("%s: %r is not a revision (a full commit hash, and /<package> for a package other "
                                   "than the root)" % (path, r))
        if not (isinstance(p, str) and p):
            raise RevisionMapError("%s: engine of %s: expected a path" % (path, r))
        out[r] = [os.path.join(base, p)]
    return out


def engine_dir(key: str) -> str:
    """Where an engines directory keeps a revision's engine, relative to it: `<commit>/<package or _root>`."""
    commit, package = split_key(key)
    return os.path.join(commit, package or ROOT_DIR)


def add_engine(path: str, revision: str, engine_rel: str) -> None:
    """Add `revision` to the map at `path`; refuse to replace an entry. Written atomically."""
    if not valid_key(revision):
        raise RevisionMapError("%r is not a revision (a full commit hash, and /<package>)" % revision)
    data = {"engines": {}}
    if os.path.exists(path):
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
    if revision in data["engines"]:
        raise RevisionMapError("revision %s is already installed: an engine is never replaced" % revision)
    data["engines"][revision] = engine_rel
    fd, tmp = tempfile.mkstemp(dir=os.path.dirname(os.path.abspath(path)), prefix=".revisions-")
    with os.fdopen(fd, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, sort_keys=True)
        f.write("\n")
    os.chmod(tmp, 0o644)                  # readable by a host running as another user (the engines are mounted)
    os.replace(tmp, path)
