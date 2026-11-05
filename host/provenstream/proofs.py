# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""A proof's description on the command line: where it comes from, the check before sending, and `-h --proof`.

A stream's commands are its proof's, so the command line knows only the core's two by heart. For any other, and for
those two too, it reads the revision's **description** (what its engine says of itself: commands, params and their
kinds, minted fields, who may send each, its event and fields, its rules), never a build: nothing here compiles Lean.

Where a description comes from (`description_of`), for a revision (a commit and a package):

1. the cache, `~/.provenstream/proofs/<commit>/<package or _root>/description.json` (the config directory's `proofs`),
   written the first time a revision's description is had from a host, and only when it describes exactly that
   revision (an engine's description never changes, so a cached one is never stale);
2. else the host's `revision.describe` (remote: the host the command talks to; local: the in-process host over the
   engines directory).

A proof named on the command line (`--proof PROOF`, `-h --proof PROOF`; `resolve`) is a full revision URL, a short
revision (7+ hex digits, optionally `/<package>`) of a revision the host serves, or the path of an engine (its
`--describe`) or of a build directory with its `PROVENANCE.json` (its engine's `--describe`, else the manifest's
schema). With no description to be had, the command fails clearly (`Unavailable`, exit 6).

The check before sending (`check`): a proof command's method must be one of the description's commands
(`method_not_found`, exit 5) and its params must be the command's (`invalid_params`, exit 5): no unknown key, every
required one present, each of its kind (`uuid` a canonical lowercase UUID, `uuid?` one or null, `meta` text of at most
4096 bytes with no control character or null, `ref` a natural number or null, any other kind ending in `?` a string with
no U+0000 or null, any other kind such a string), besides `actor_id` (a UUID) and `idempotency_key` (1 to 200 chars).
Nothing is sent when it fails. The rules stay the host's.

`markdown` renders a description as `-h --proof` prints it: stable Markdown for people and agents, the same bytes for
the same description.
"""
from __future__ import annotations
import json, os, re, tempfile, textwrap
from typing import Any, Dict, List, Optional, Tuple

from . import config, ids, wire
from .client import ClientError, EXIT_PARAMS, EXIT_UNAVAILABLE
from .revisions import (ROOT_DIR, parse_url, revision_key, revision_url, short, split_key, valid_key)
from .schema import CommandSpec, SchemaError, commands_of

OPTIONAL_KINDS = ("uuid?", "meta", "ref")
EVERY_COMMAND = ("actor_id", "idempotency_key")


def optional(kind: str) -> bool:
    """Whether a field of `kind` may be absent or null: `uuid?`, `meta`, `ref`, and any text kind ending in `?`."""
    return kind in OPTIONAL_KINDS or kind.endswith("?")


class Unavailable(ClientError):
    """No description of a proof to be had (exit 6)."""

    def __init__(self, message: str):
        super().__init__(EXIT_UNAVAILABLE, message)


# -- the cache ------------------------------------------------------------------------------------------------------

def cache_path(key: str, env=os.environ) -> str:
    commit, package = split_key(key)
    return os.path.join(config.directory(env), "proofs", commit, *(package.split("/") if package else [ROOT_DIR]),
                        "description.json")


def key_of(desc: Any) -> Optional[str]:
    """The revision a description says it is (its commit and package), or None when it says none."""
    if not isinstance(desc, dict) or not isinstance(desc.get("revision"), str):
        return None
    k = revision_key(desc["revision"], desc.get("package") or "")
    return k if valid_key(k) else None


def cached(key: str, env=os.environ) -> Optional[dict]:
    try:
        with open(cache_path(key, env), encoding="utf-8") as f:
            d = wire.loads(f.read())
    except (OSError, wire.BadJson):
        return None
    return d if key_of(d) == key else None


def remember(key: str, desc: dict, env=os.environ) -> None:
    """Keep `desc` for `key`, if it describes exactly that revision (else it is not cached)."""
    if key_of(desc) != key:
        return
    path = cache_path(key, env)
    try:
        config.ensure_directory(env)
        os.makedirs(os.path.dirname(path), mode=0o700, exist_ok=True)
        fd, tmp = tempfile.mkstemp(dir=os.path.dirname(path), prefix=".description-")
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            f.write(json.dumps(desc, indent=2, sort_keys=True) + "\n")
        os.replace(tmp, path)
    except OSError:
        pass                                   # a cache: failing to keep one costs only another revision.describe


def description_of(key: str, target=None, env=os.environ) -> dict:
    """The description of revision `key`: cached, else the host's `revision.describe` (on `target`, a carrier with
    `handle`), then cached. Raises the host's answer (`refused: revision_must_be_installed`, `unavailable: ...`), which
    `resolve` and the check before sending turn into a clear `Unavailable`."""
    got = cached(key, env)
    if got is not None:
        return got
    if target is None:
        raise Unavailable("unavailable: no description of revision %s to be had: it is not in the cache (%s) and no "
                          "host was asked; nothing sent" % (short(key), os.path.dirname(cache_path(key, env))))
    desc = target.handle("revision.describe", {"revision": key})     # the host's answer, as it is: callers say why
    remember(key, desc, env)
    return desc


# -- naming a proof -------------------------------------------------------------------------------------------------

def from_path(path: str) -> dict:
    """The description of an engine at `path`, or of the engine of a build directory (its PROVENANCE.json)."""
    from .engine import Engine, EngineFailure
    manifest = None
    engine = path
    if os.path.isdir(path):
        try:
            with open(os.path.join(path, "PROVENANCE.json"), encoding="utf-8") as f:
                manifest = json.load(f)
        except (OSError, ValueError) as x:
            raise Unavailable("unavailable: %s is a directory without a readable PROVENANCE.json (%s): not a build "
                              "directory" % (path, getattr(x, "strerror", None) or x))
        engine = os.path.join(path, (manifest.get("engine") or {}).get("file") or "engine")
    e = Engine([os.path.abspath(engine)])
    try:
        e.start()
        return e.describe()
    except EngineFailure as x:
        if manifest and isinstance(manifest.get("schema"), dict):     # an engine of another platform: its manifest
            commit = manifest.get("commit") or split_key(manifest.get("revision") or "")[0]
            return {"revision": commit, "repo": manifest.get("repo_url") or "", "protocol": 2,
                    "package": manifest.get("package") or "", "schema": manifest["schema"]}
        raise Unavailable("unavailable: %s does not describe itself as an engine: %s" % (path, x))
    finally:
        e.stop()


def served(target) -> List[str]:
    return [r["revision"] for r in target.handle("revisions.list", {})["revisions"]]


def cached_short(proof: str, env=os.environ) -> Optional[dict]:
    """The cached description of a short revision (7+ hex digits, optionally /<package>), when exactly one cached
    commit begins with those digits."""
    from . import context
    h, pkg = context.split_short(proof)
    root = os.path.join(config.directory(env), "proofs")
    try:
        commits = [c for c in os.listdir(root) if c.startswith(h)]
    except OSError:
        return None
    hits = [d for d in (cached(revision_key(c, pkg), env) for c in commits) if d is not None]
    return hits[0] if len(hits) == 1 else None


def unreachable(subject: str, why: str, env=os.environ) -> "Unavailable":
    """No description of `subject` ("proof P", "stream S's revision") to be had, and why: exit 6."""
    return Unavailable("unavailable: no description of %s could be had: it is not cached under %s, it is not a path "
                       "to an engine or a build directory, and the host could not be asked: %s"
                       % (subject, os.path.join(config.directory(env), "proofs"), why))


def resolve(proof: str, target_factory) -> dict:
    """The description `proof` names: a path (an engine, or a build directory), a full revision URL, or a short
    revision of one the host serves; from the cache when it holds it. `target_factory()` gives a carrier (a context
    manager) when a host is needed. Anything else, a host that cannot be asked or does not serve it included, is
    `Unavailable` (exit 6), saying why."""
    from . import context
    if os.path.exists(proof):
        return from_path(proof)
    named = parse_url(proof)
    if named is None and not context.looks_like_revision(proof):
        raise Unavailable("unavailable: no description of proof %s could be had: it is not a path to an engine or a "
                          "build directory, not a revision URL (<repo>/commit/<commit> or "
                          "<repo>/tree/<commit>/<package>), and not 7+ hex digits of a revision" % proof)
    got = cached(named.key) if named is not None else cached_short(proof)
    if got is not None:
        return got
    try:
        with target_factory() as t:
            key = named.key if named is not None else context.resolve_revision(proof, served(t))
            return description_of(key, t)
    except ClientError as x:                      # unauthorized, unreachable, not served: no description, exit 6
        raise unreachable("proof " + proof, x.message)


# -- the check before sending ---------------------------------------------------------------------------------------

def _kind_ok(kind: str, v: Any) -> Optional[str]:
    if kind == "uuid":
        return None if isinstance(v, str) and ids.CANONICAL_ID.fullmatch(v) else "expected a canonical lowercase UUID"
    if kind == "uuid?":
        if v is None or (isinstance(v, str) and ids.CANONICAL_ID.fullmatch(v)):
            return None
        return "expected a canonical lowercase UUID or null"
    if kind == "meta":
        if v is None:
            return None
        if not isinstance(v, str):
            return "expected a string or null"
        if len(v.encode("utf-8", "surrogatepass")) > 4096 or any(ord(c) < 32 or ord(c) == 127 for c in v):
            return "expected at most 4096 bytes of text without a control character"
        return None
    if kind == "ref":
        if v is None or (isinstance(v, int) and not isinstance(v, bool) and v >= 0):
            return None
        return "expected a natural number (the seq of an earlier event of this stream) or null"
    if kind.endswith("?"):
        if v is None or (isinstance(v, str) and "\x00" not in v):
            return None
        return "expected a string (%s) or null" % kind[:-1]
    if not isinstance(v, str) or "\x00" in v:
        return "expected a string (%s)" % kind
    return None


def problem(spec: CommandSpec, params: Dict[str, Any]) -> Optional[str]:
    """Why `params` are not `spec`'s (the detail of invalid_params), or None."""
    names = list(spec.field_names) + list(EVERY_COMMAND)
    for k in params:
        if k not in names:
            return "%s: unknown param %s (expected {%s})" % (spec.name, k, ", ".join(
                f + ("?" if (optional(dict(spec.params).get(f, "")) or f in EVERY_COMMAND) else "")
                for f in names))
    for f, kind in spec.params:
        if not optional(kind) and f not in params:
            return "%s: %s: required" % (spec.name, f)
    for f, kind in spec.params:
        if f in params:
            why = _kind_ok(kind, params[f])
            if why:
                return "%s: %s: %s" % (spec.name, f, why)
    if "actor_id" in params and _kind_ok("uuid", params["actor_id"]):
        return "%s: actor_id: expected the caller's principal_id (a canonical lowercase UUID)" % spec.name
    k = params.get("idempotency_key")
    if "idempotency_key" in params and not (isinstance(k, str) and 1 <= len(k) <= 200):
        return "%s: idempotency_key: expected a string of 1 to 200 characters" % spec.name
    return None


def check(desc: dict, method: str, params: Dict[str, Any]) -> None:
    """Raise method_not_found or invalid_params (exit 5) unless `method` is a command of `desc` and `params` its."""
    try:
        specs = commands_of(desc)
    except SchemaError as x:
        raise Unavailable("unavailable: the description of %s is not one this command line reads: %s"
                          % (label(desc), x))
    spec = specs.get(method)
    if spec is None:
        raise ClientError(EXIT_PARAMS, "method not found: %s is not a command of %s (its description; nothing sent)"
                          % (method, label(desc)))
    why = problem(spec, params)
    if why:
        raise ClientError(EXIT_PARAMS, "invalid params: %s (the description of %s; nothing sent)" % (why, label(desc)))


def label(desc: dict) -> str:
    """A description's revision as people write it: `4f1c2a9`, `4f1c2a9/examples/tasks`."""
    commit, package = str(desc.get("revision") or "?"), str(desc.get("package") or "")
    return commit[:7] + ("/" + package if package else "")


# -- -h --proof -----------------------------------------------------------------------------------------------------

NOTES = {"uuid": "", "uuid?": "or null", "meta": "opaque text, at most 4096 bytes; committed to by the chain, erasable",
         "ref": "the seq of an earlier event of this stream (ref_must_name_an_earlier_event), or null"}
TYPE = {"uuid": "uuid", "uuid?": "uuid", "meta": "meta", "ref": "ref (integer)"}


def _placeholder(param: str) -> str:
    return "<%s>" % (param[:-3] if param.endswith("_id") else param)


def _repo(desc: dict) -> str:
    r = desc.get("repo") or ""
    r = r.rstrip("/")
    return r[:-4] if r.endswith(".git") else r


def markdown(desc: dict) -> str:
    specs = list(commands_of(desc).values())
    commit, package = str(desc.get("revision") or "?"), str(desc.get("package") or "")
    repo = _repo(desc)
    wrap = lambda t: textwrap.fill(t, width=116, break_long_words=False, break_on_hyphens=False)
    out = ["# Proof %s" % (commit[:7] + ("/" + package if package else "")), "",
           "- repository: %s" % (repo or "(not said)"),
           "- commit: %s" % commit,
           "- package: %s" % (package or "(the root)"),
           "- revision URL: %s" % (revision_url(repo, commit, package) if repo else "(no repository said)"),
           "- protocol: %s" % desc.get("protocol"),
           "- commands: %s" % ", ".join(s.name for s in specs), "",
           "Every command also takes `actor_id` (optional: the caller, filled in from the token; any other is refused",
           "actor_id_must_match_the_token) and `idempotency_key` (optional: 1 to 200 chars; a retry with the same key "
           "answers",
           "the first answer).", ""]
    for s in specs:
        out += ["## %s" % s.name, "", wrap("Who may send it: %s." % (s.who or "(the description does not say)")), "",
                "| param | type | required | notes |", "|---|---|---|---|"]
        for f, kind in s.params:
            note = NOTES.get(kind, "text, its form checked by the proof's rules" if f == "proof_revision_url"
                             else ("text, or null" if optional(kind) else "text"))
            row = "| %s | %s | %s | %s |" % (f, TYPE.get(kind, kind.rstrip("?")), "optional" if optional(kind)
                                              else "required", note)
            out.append(row.replace("|  |", "| |"))
        out += ["", "Minted by the host: %s." % (", ".join("`%s`" % m for m in s.minted) or "none"), "",
                "Event `%s`: `{%s}`" % (s.event, ", ".join(s.event_fields)), "", "Call it:", "", "```sh"]
        args = " ".join("-f %s=%s" % (f, _placeholder(f)) for f, kind in s.params if not optional(kind))
        out.append(("provenstream api %s %s" % (s.name, args)).rstrip())
        if s.name == "stream.open":
            out.append("provenstream stream open <proof_revision_url>")
        elif s.name == "stream.close":
            out.append("provenstream stream close <stream> --yes")
        out += ["```", "", wrap("Rules, in order: %s." % (", ".join(s.rules) or "none")), ""]
    out += ["## Answers", "", "| answer | exit | what |", "|---|---|---|",
            "| accepted | 0 | `{seq, event, chain}`: the event's position, the event, the chain head after it |",
            "| refused | 4 | `refused: <rule>`: one of the rules below; nothing stored |",
            "| method_not_found | 5 | not a command of this proof; checked before sending |",
            "| invalid_params | 5 | params not as above; checked before sending |", "",
            "## Rules", "", "| rule | commands |", "|---|---|"]
    order: List[str] = []
    by: Dict[str, List[str]] = {}
    for s in specs:
        for r in s.rules:
            if r not in by:
                order.append(r)
                by[r] = []
            if s.name not in by[r]:
                by[r].append(s.name)
    names = [s.name for s in specs]
    for r in order:
        cmds = by[r]
        rest = [n for n in names if n not in cmds]
        what = ("every command but %s" % ", ".join(rest)) if len(rest) == 1 and len(cmds) > 1 else ", ".join(cmds)
        out.append("| %s | %s |" % (r, what))
    return "\n".join(out) + "\n"
