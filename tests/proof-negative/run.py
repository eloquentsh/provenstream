#!/usr/bin/env python3
# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""Run the negative proof tests (`cases.py`). For each case: copy the case's layer's sources (examples/tasks unless the
case names another `layer` and `lib`) to a fresh directory whose lakefile requires this checkout of provenstream by
absolute path; build the target unchanged (it must succeed: the
positive control); apply the case's edits; build again, which must fail, with every error inside the declaration the
case names (and one on the marked line, when it names one). Exit 0 only if every case behaves so.

    python3 tests/proof-negative/run.py [--keep]
"""
import os, re, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
LAYER = os.path.join(ROOT, "examples", "tasks")     # the default layer; a case may name another (`layer`, `lib`)
sys.path.insert(0, HERE)
from cases import CASES  # noqa: E402

LAKE = os.environ.get("LAKE") or shutil.which("lake") or os.path.expanduser("~/.elan/bin/lake")
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|def|abbrev|lemma|structure|inductive)\s+([^\s(:{\[]+)")


def copy_project(dst, layer=LAYER, lib="Tasks"):
    os.makedirs(os.path.join(dst, lib))
    for f in ("lean-toolchain", lib + ".lean"):
        shutil.copy(os.path.join(layer, f), dst)
    for f in os.listdir(os.path.join(layer, lib)):
        shutil.copy(os.path.join(layer, lib, f), os.path.join(dst, lib, f))
    with open(os.path.join(dst, "lakefile.toml"), "w") as f:
        f.write('name = "%s_negative"\nversion = "0.1.0"\n\n[[require]]\nname = "provenstream"\npath = %s\n\n'
                '[[lean_lib]]\nname = "%s"\n' % (lib.lower(), '"' + ROOT.replace("\\", "\\\\") + '"', lib))


def build(dst, target):
    p = subprocess.run([LAKE, "build", target], cwd=dst, capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr


def enclosing_decl(path, line):
    name = None
    with open(path, encoding="utf-8") as f:
        for i, l in enumerate(f, 1):
            if i > line:
                break
            m = DECL.match(l)
            if m:
                name = m.group(1)
    return name


def run_case(case, keep):
    d = tempfile.mkdtemp(prefix="provenstream-neg-")
    try:
        copy_project(d, os.path.join(ROOT, case["layer"]) if "layer" in case else LAYER, case.get("lib", "Tasks"))
        code, out = build(d, case["target"])
        if code != 0:
            return False, "the unchanged copy does not build (positive control):\n" + out[-3000:]
        for rel, old, new in case["edits"]:
            p = os.path.join(d, rel)
            src = open(p, encoding="utf-8").read()
            n = src.count(old)
            if n != 1:
                return False, "edit to %s: the old text occurs %d times, not once" % (rel, n)
            open(p, "w", encoding="utf-8").write(src.replace(old, new))
        code, out = build(d, case["target"])
        if code == 0:
            return False, "the variant BUILT: the theorem did not fail"
        errors = re.findall(r"error: ([^\s:]+\.lean):(\d+):(\d+): ([^\n]*)", out)
        if not errors:
            return False, "the build failed without a Lean error:\n" + out[-3000:]
        where = []
        for rel, line, col, msg in errors:
            decl = enclosing_decl(os.path.join(d, rel), int(line))
            where.append((rel, int(line), decl, msg))
            if decl != case["fails_in"]:
                return False, "an error outside %s: %s:%s in %s: %s" % (case["fails_in"], rel, line, decl, msg)
        if case.get("fails_at"):
            marked = False
            for rel, line, decl, msg in where:
                text = open(os.path.join(d, rel), encoding="utf-8").read().split("\n")
                if case["fails_at"] in text[line - 1]:
                    marked = True
            if not marked:
                return False, "no error on the marked line (%s): %r" % (case["fails_at"], where)
        return True, "; ".join("%s:%d in %s: %s" % w for w in where)
    finally:
        if keep:
            print("  kept", d)
        else:
            shutil.rmtree(d, ignore_errors=True)


def main():
    keep = "--keep" in sys.argv
    ok = True
    for case in CASES:
        good, detail = run_case(case, keep)
        print("%s %s: %s" % ("PASS" if good else "FAIL", case["name"], case["what"]))
        print("  " + detail.replace("\n", "\n  ")[:2000])
        ok = ok and good
    print("proof-negative: %s" % ("all cases failed to build as they must" if ok else "FAILED"))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
