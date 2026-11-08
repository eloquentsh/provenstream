#!/usr/bin/env python3
# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""Run the recorded sequences (cases/solochangecontrol.jsonl, written by `SOLO_RECORD=1 pytest test_sequences.py`)
through the conformance runner (host/provenstream/conform.py) against a throwaway host.

The runner's table of proofs with conformance sequences (`conform.PROOFS`) does not hold the solo proof yet, and
conformance/make_cases.py has no theme for it, so this script adds the proof to that table in this process only and
reads the cases from this directory. The runner's own engine build takes the committed tree (`git archive HEAD`); the
layer under test may be uncommitted, so the two engines a run needs (the core's, the solo proof's) are built here from
a copy of the working tree, stamped with HEAD's commit so that their revision keys are well formed. Nothing in the
checkout is written.

    PYTHONPATH=host python3 examples/solochangecontrol/tests/conform_solo.py [--target inprocess|stdio|http]
                                                                              [--engines DIR] [--verbose] [--keep]

Exit 0 only when every case passes (skips count as passes, as in the runner).
"""
from __future__ import annotations
import argparse, json, logging, os, shutil, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(REPO, "host"))

from provenstream import build, conform, project  # noqa: E402

PACKAGE = "examples/solochangecontrol"
EXCLUDE = (".git", ".lake", ".hypothesis", "artifacts", "node_modules", "__pycache__", ".venv")


def say(*a):
    print("conform_solo:", *a, flush=True)


def build_engines(work: str) -> str:
    """Copy the working tree to `work`, reuse its Lake build directories, stamp both packages with HEAD's commit, build
    their engines, and write an engines directory for them. Answers that directory."""
    commit = subprocess.run(["git", "-C", REPO, "rev-parse", "HEAD"], capture_output=True, text=True, check=True).stdout.strip()
    repo_url = subprocess.run(["git", "-C", REPO, "remote", "get-url", "origin"], capture_output=True, text=True).stdout.strip() \
        or "file://" + REPO
    tree = os.path.join(work, "tree")
    say("copying the working tree to", tree)
    shutil.copytree(REPO, tree, symlinks=True, ignore=lambda d, names: [n for n in names if n in EXCLUDE])
    say("reused %d Lake build directories" % build.copy_lake(REPO, tree))
    engines = {}
    for package in ("", PACKAGE):
        pdir = os.path.normpath(os.path.join(tree, package)) if package else tree
        cfg = project.load(pdir)
        env = dict(os.environ, PROVENSTREAM_REVISION=commit, PROVENSTREAM_REPO_URL=repo_url, PROVENSTREAM_PACKAGE=package)
        say(project.stamp(pdir, cfg, env).strip())
        t0 = time.time()
        out = project.run([project.lake(), "build"], pdir, env)
        say("%s: %s (%.0fs)" % (package or "the core", out.strip().splitlines()[-1], time.time() - t0))
        engine = os.path.join(pdir, ".lake", "build", "bin", cfg["engine"])
        desc = json.loads(project.run([engine, "--describe"], pdir))
        key = commit + ("/" + package if package else "")
        if desc.get("revision") != commit or desc.get("package", "") != package:
            raise SystemExit("the engine reports revision %r, package %r, not %s" % (desc.get("revision"), desc.get("package"), key))
        engines[key] = engine
    edir = os.path.join(work, "engines")
    os.makedirs(edir)
    with open(os.path.join(edir, "revisions.json"), "w", encoding="utf-8") as f:
        json.dump({"engines": engines}, f, indent=2)
    return edir


def main(argv=None) -> int:
    a = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    a.add_argument("--target", choices=sorted(conform.LOCAL_TARGETS), default="inprocess")
    a.add_argument("--engines", help="an engines directory already holding the core's and the solo proof's engines of one commit")
    a.add_argument("--cases", default=os.path.join(HERE, "cases"))
    a.add_argument("--verbose", action="store_true")
    a.add_argument("--keep", action="store_true", help="keep the scratch directory")
    args = a.parse_args(argv)

    conform.PROOFS.clear()
    conform.PROOFS.update({"core": "", "solochangecontrol": PACKAGE})
    work = tempfile.mkdtemp(prefix="solo-conform-")
    try:
        edir = args.engines or build_engines(work)
        themes = conform.load_cases(args.cases)
        fx = conform.Fixture(edir, None, say=say)
        try:
            logger = logging.getLogger("provenstream")
            logger.addHandler(logging.FileHandler(os.path.join(fx.tmp, "host.log")))
            logger.propagate = False
            say("commit %s, proofs %s, target %s" % (fx.commit[:12], " ".join(sorted(fx.revisions)), args.target))
            target = conform.LOCAL_TARGETS[args.target](fx)
            t0 = time.time()
            try:
                results = conform.run_cases(target, themes, conform.local_run(fx))
            finally:
                target.close()
            conform._report(results, args.verbose)
            return conform.summary(results, "%s (solo cases)" % args.target, {args.target: time.time() - t0})
        finally:
            fx.close()
    except (conform.SetupError, conform.CaseError, project.CheckFailed, subprocess.CalledProcessError) as x:
        say("could not run:", x)
        return 2
    finally:
        if args.keep:
            say("kept", work)
        else:
            shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
