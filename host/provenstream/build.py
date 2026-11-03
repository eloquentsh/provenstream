# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""Build an engine from a proof repository at a commit, with a provenance manifest (`provenstream build`).

The pipeline, all local (remote build on demand is phase 2: docs/phase2.md):

1. resolve the commit and its tree in the repository; take the committed files only (`git archive`), never the
   working tree;
2. in a fresh directory, stamp the revision module with the commit and the package (`scripts/stamp_revision`,
   PROVENSTREAM_REVISION, PROVENSTREAM_PACKAGE), so the engine reports exactly that revision;
3. `lake build` with the toolchain the commit's `lean-toolchain` names (elan selects it); the proof inherits from the
   core's (`project.inherits`: the engine serves a layer on the core's base); then the engine's `--self-test` and
   `--describe`, which must report the commit and the package, and the stream interface (`interface.py`): an engine
   whose proof is valid but does not implement it is refused;
4. copy the engine out with `PROVENANCE.json`: the revision (its key: the commit, and `/<package>` for a package other
   than the root), the repository URL and the proof URL (`/commit/` or `/tree/<commit>/<package>`), the source commit
   and tree and package directory, the toolchain and `lean --version`, the builder's platform, the engine's sha256 and size, the
   schema it advertises, and the build time; and with `THIRD_PARTY_NOTICES` and `LICENSE`, which travel with every
   engine (the engine contains the Lean runtime, GMP, mimalloc and libuv): the package's, else the repository's, else
   those of the provenstream dependency Lake fetched (a layer in another repository).

The engine of a proof repository at a commit is the package `--package` names (default: the repository's root), whose
`provenstream.json` names the engine. `--reuse-lake DIR` copies Lake's build directories from a checkout first, which
only saves time: Lake rebuilds whatever their traces do not match.
"""
from __future__ import annotations
import datetime, hashlib, json, os, platform, shutil, subprocess, tempfile, time
from typing import Dict, Optional

from . import interface, project
from .revisions import engine_dir, revision_key, revision_url, valid_package


class BuildFailed(Exception):
    pass


def git(repo: str, *args: str) -> str:
    p = subprocess.run(["git", "-C", repo] + list(args), capture_output=True, text=True)
    if p.returncode != 0:
        raise BuildFailed("git %s: %s" % (" ".join(args), p.stderr.strip()))
    return p.stdout.strip()


def sha256(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def copy_lake(src_root: str, dst_root: str) -> int:
    """Copy every `.lake/build` under `src_root` to the same place under `dst_root` (a time saving only)."""
    n = 0
    for root, dirs, files in os.walk(src_root):
        if ".lake" in dirs:
            src = os.path.join(root, ".lake", "build")
            rel = os.path.relpath(root, src_root)
            dst_pkg = os.path.join(dst_root, rel)
            if os.path.isdir(src) and os.path.isdir(dst_pkg):
                shutil.copytree(src, os.path.join(dst_pkg, ".lake", "build"), symlinks=True)
                n += 1
        dirs[:] = [d for d in dirs if d not in (".lake", ".git")]
    return n


def package_path(package: str) -> str:
    """A package directory as a package path: "" for the root (`.`), else its `/`-separated segments."""
    p = os.path.normpath(package or ".").replace(os.sep, "/")
    if p == ".":
        return ""
    if os.path.isabs(p) or not valid_package(p):
        raise BuildFailed("--package %s: not a package path inside the repository" % package)
    return p


NOTICES = ("THIRD_PARTY_NOTICES", "LICENSE")


def notices_dir(work: str, pdir: str) -> str:
    """The directory whose THIRD_PARTY_NOTICES and LICENSE travel with the engine of the package at `pdir` in the
    archived repository `work`: the package, else the repository's root, else the provenstream dependency Lake fetched
    (a layer in another repository)."""
    for d in (pdir, work, os.path.join(pdir, ".lake", "packages", "provenstream")):
        if all(os.path.isfile(os.path.join(d, n)) for n in NOTICES):
            return d
    raise BuildFailed("THIRD_PARTY_NOTICES and LICENSE: not in the package, the repository's root or "
                      ".lake/packages/provenstream")


def carry_notices(src_dir: str, dst_dir: str) -> None:
    """Copy THIRD_PARTY_NOTICES and LICENSE from `src_dir` to `dst_dir`, read-only."""
    for n in NOTICES:
        dst = os.path.join(dst_dir, n)
        shutil.copy2(os.path.join(src_dir, n), dst)
        os.chmod(dst, 0o444)


def build_engine(repo: str, commit: str, out_dir: str, package: str = ".", repo_url: Optional[str] = None,
                 reuse_lake: Optional[str] = None, say=print, keep: bool = False) -> Dict:
    """Build the engine of `repo` at `commit` (package directory `package`) into `out_dir` (which must not exist);
    answer the provenance manifest."""
    t0 = time.time()
    repo = os.path.abspath(repo)
    pkg = package_path(package)
    full = git(repo, "rev-parse", "--verify", commit + "^{commit}")
    tree = git(repo, "rev-parse", full + "^{tree}")
    if repo_url is None:
        try:
            repo_url = git(repo, "remote", "get-url", "origin")
        except BuildFailed:
            repo_url = "file://" + repo
    if os.path.exists(out_dir):
        raise BuildFailed("%s exists: a build never replaces one" % out_dir)
    work = tempfile.mkdtemp(prefix="provenstream-build-")
    try:
        say("build: %s at %s (tree %s), package %s" % (repo, full, tree, package))
        archive = subprocess.run(["git", "-C", repo, "archive", "--format=tar", full], capture_output=True)
        if archive.returncode != 0:
            raise BuildFailed("git archive: %s" % archive.stderr.decode(errors="replace"))
        subprocess.run(["tar", "-x", "-C", work], input=archive.stdout, check=True)
        if reuse_lake:
            say("build: reused %d Lake build directories from %s" % (copy_lake(os.path.abspath(reuse_lake), work),
                                                                      reuse_lake))
        pdir = os.path.normpath(os.path.join(work, package))
        cfg = project.load(pdir)
        env = dict(os.environ, PROVENSTREAM_REVISION=full, PROVENSTREAM_REPO_URL=repo_url, PROVENSTREAM_PACKAGE=pkg)
        say(project.stamp(pdir, cfg, env))
        toolchain = open(os.path.join(pdir, "lean-toolchain"), encoding="utf-8").read().strip()
        lean_version = project.run(["lean", "--version"], pdir).strip()
        out = project.run([project.lake(), "build"], pdir, env)
        say(out.strip().splitlines()[-1])
        say(project.inherits(pdir, cfg))
        engine = os.path.join(pdir, ".lake", "build", "bin", cfg["engine"])
        say(project.run([engine, "--self-test"], pdir).strip())
        desc = json.loads(project.run([engine, "--describe"], pdir))
        if desc.get("revision") != full or desc.get("package") != pkg:
            raise BuildFailed("the engine reports revision %r, package %r, not %s, %r"
                              % (desc.get("revision"), desc.get("package"), full, pkg))
        try:
            say(interface.summary(interface.check_engine(engine)))
        except interface.InterfaceMismatch as x:
            raise BuildFailed("the engine does not implement the stream interface (interface.py): %s" % x)
        notices = notices_dir(work, pdir)
        os.makedirs(out_dir)
        dst = os.path.join(out_dir, "engine")
        shutil.copy2(engine, dst)
        os.chmod(dst, 0o555)
        carry_notices(notices, out_dir)
        manifest = {
            "revision": revision_key(full, pkg),
            "commit": full,
            "package": pkg,
            "repo_url": repo_url,
            "proof_url": revision_url(repo_url, full, pkg),
            "source": {"commit": full, "tree": tree, "package": package, "project": cfg["name"]},
            "toolchain": {"name": toolchain, "lean_version": lean_version},
            "builder": {"platform": platform.platform(), "machine": platform.machine(),
                        "python": platform.python_version()},
            "engine": {"name": cfg["engine"], "file": "engine", "sha256": sha256(dst), "bytes": os.path.getsize(dst)},
            "schema": desc["schema"],
            "built_at": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "build_seconds": round(time.time() - t0, 1),
        }
        with open(os.path.join(out_dir, "PROVENANCE.json"), "w", encoding="utf-8") as f:
            json.dump(manifest, f, indent=2, sort_keys=True)
            f.write("\n")
        say("build: %s -> %s (sha256 %s)" % (cfg["engine"], out_dir, manifest["engine"]["sha256"]))
        return manifest
    except project.CheckFailed as x:
        raise BuildFailed(str(x)) from x
    finally:
        if keep:
            say("build: kept %s" % work)
        else:
            shutil.rmtree(work, ignore_errors=True)


def install(build_dir: str, engines_dir: str, say=print) -> str:
    """Put a built engine into a host's engines directory and its revision map, never replacing one: check the
    engine's sha256 against its manifest, run its self-test, check that it reports the manifest's revision and
    schema, and that it implements the stream interface (`interface.py`). Answers the revision (its key). The engine
    goes to `<commit>/<package or _root>/` (`revisions.engine_dir`), so one commit's packages sit side by side, with
    its PROVENANCE.json and, when the build carried them, THIRD_PARTY_NOTICES and LICENSE."""
    from .revisions import add_engine, load_map
    with open(os.path.join(build_dir, "PROVENANCE.json"), encoding="utf-8") as f:
        manifest = json.load(f)
    rev = manifest["revision"]
    src = os.path.join(build_dir, manifest["engine"]["file"])
    if sha256(src) != manifest["engine"]["sha256"]:
        raise BuildFailed("the engine's sha256 is not its manifest's")
    project.run([src, "--self-test"], build_dir)
    desc = json.loads(project.run([src, "--describe"], build_dir))
    if revision_key(desc.get("revision") or "", desc.get("package") or "") != rev or \
            desc.get("schema") != manifest["schema"]:
        raise BuildFailed("the engine does not describe itself as its manifest says")
    try:
        say(interface.summary(interface.check_engine(src)))
    except interface.InterfaceMismatch as x:
        raise BuildFailed("the engine does not implement the stream interface (interface.py): %s" % x)
    os.makedirs(engines_dir, exist_ok=True)
    rmap = os.path.join(engines_dir, "revisions.json")
    rel = engine_dir(rev)
    if rev in load_map(rmap) or os.path.exists(os.path.join(engines_dir, rel)):
        raise BuildFailed("revision %s is already installed: an engine is never replaced" % rev)
    staging = os.path.join(engines_dir, ".staging-" + rev.replace("/", "--"))
    shutil.rmtree(staging, ignore_errors=True)
    os.makedirs(staging)
    shutil.copy2(src, os.path.join(staging, "engine"))
    shutil.copy2(os.path.join(build_dir, "PROVENANCE.json"), os.path.join(staging, "PROVENANCE.json"))
    os.chmod(os.path.join(staging, "engine"), 0o555)
    os.chmod(os.path.join(staging, "PROVENANCE.json"), 0o444)
    if all(os.path.isfile(os.path.join(build_dir, n)) for n in NOTICES):
        carry_notices(build_dir, staging)
    os.makedirs(os.path.dirname(os.path.join(engines_dir, rel)), exist_ok=True)
    os.rename(staging, os.path.join(engines_dir, rel))
    add_engine(rmap, rev, rel.replace(os.sep, "/") + "/engine")
    say("install: %s -> %s" % (rev, os.path.join(engines_dir, rel)))
    return rev
