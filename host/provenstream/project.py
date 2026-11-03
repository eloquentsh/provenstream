# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""A layer project, and its checks (`provenstream check`).

A project is a Lake package whose `provenstream.json` says:

    {"name": "tasks", "engine": "tasks-engine", "namespaces": ["Tasks"],
     "layer_modules": ["Tasks/Layer.lean", ...], "audit_roots": ["Tasks.tasks"],
     "revision_module": "TasksRevision.lean", "revision_def": "Tasks.built"}

and, for a layer on a layer, `"below": ["Tasks"]`: the namespaces of the layers under it, whose modules its layer modules
may import besides `Provenstream.Interface`.

The checks, in order, each stopping the run when it fails:
  1. stamp the revision module, `lake build`: no warning, no `sorry`;
  2. axioms: every declaration under the namespaces depends on propext, Quot.sound, Classical.choice at most;
  3. forbidden words in the project's Lean sources (comments and strings stripped): no sorry, admit, axiom, partial,
     unsafe, implemented_by, extern, native_decide; and every layer module imports `Provenstream.Interface` and the
     project's own modules (and the layers' below it) only;
  4. the dependency audit of the layer's service (`ProvenstreamCheck.audit`);
  5. the proof inherits from the core's (`inherits`): the engine serves a layer on the core's base, or on a layer on it;
  6. the engine's self-test, its description (`--describe`), and the stream interface (`interface.py`).
"""
from __future__ import annotations
import json, os, re, shutil, subprocess, sys, tempfile
from typing import Dict, List, Optional

FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|partial|unsafe|implemented_by|extern|native_decide)\b")
TOOLCHAIN = "leanprover/lean4:v4.35.0"


def _find_repo() -> Optional[str]:
    """The provenstream checkout: $PROVENSTREAM_HOME, or the one this package runs from (None when installed)."""
    for d in (os.environ.get("PROVENSTREAM_HOME"),
              os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))):
        if d and os.path.exists(os.path.join(d, "Provenstream", "Interface.lean")):
            return os.path.abspath(d)
    return None


REPO = _find_repo()


class CheckFailed(Exception):
    pass


def lake() -> str:
    return os.environ.get("LAKE") or shutil.which("lake") or os.path.expanduser("~/.elan/bin/lake")


CONFIG_KEYS = ("name", "engine", "namespaces", "layer_modules", "audit_roots", "revision_module", "revision_def")


def config_path(project: str) -> str:
    """The project's config: `provenstream.json`, or, in a tree from before that name (a revision is rebuilt from its own
    tree, whatever it called things), the one JSON object at the package root that has every config key."""
    path = os.path.join(project, "provenstream.json")
    if os.path.exists(path):
        return path
    found = []
    for f in sorted(os.listdir(project)):
        if f.endswith(".json") and f != "lake-manifest.json":
            try:
                with open(os.path.join(project, f), encoding="utf-8") as h:
                    d = json.load(h)
            except (OSError, ValueError):
                continue
            if isinstance(d, dict) and all(k in d for k in CONFIG_KEYS):
                found.append(os.path.join(project, f))
    return found[0] if len(found) == 1 else path


def load(project: str) -> Dict:
    path = config_path(project)
    try:
        with open(path, encoding="utf-8") as f:
            cfg = json.load(f)
    except (OSError, ValueError) as x:
        raise CheckFailed("%s: %s" % (path, x))
    for k in CONFIG_KEYS:
        if k not in cfg:
            raise CheckFailed("%s: missing %s" % (path, k))
    return cfg


def strip_lean(src: str) -> str:
    """The Lean source with comments and string literals blanked (scripts/strip_lean_comments.py)."""
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j
        elif src.startswith("/-", i):
            depth += 1; out.append("  "); i += 2
        elif depth > 0 and src.startswith("-/", i):
            depth -= 1; out.append("  "); i += 2
        elif depth > 0:
            out.append("\n" if src[i] == "\n" else " "); i += 1
        elif src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append('""' + "".join("\n" for c in src[i + 1:j] if c == "\n")); i = j + 1
        else:
            out.append(src[i]); i += 1
    return "".join(out)


def lean_sources(project: str, cfg: Dict) -> List[str]:
    out = []
    for root, dirs, files in os.walk(project):
        dirs[:] = [d for d in dirs if d not in (".lake", "scripts", "tests")]
        for f in files:
            if f.endswith(".lean") and os.path.join(root, f) != os.path.join(project, cfg["revision_module"]):
                out.append(os.path.join(root, f))
    return sorted(out)


def word_scan(paths: List[str]) -> List[str]:
    hits = []
    for p in paths:
        for k, line in enumerate(strip_lean(open(p, encoding="utf-8").read()).split("\n"), 1):
            if FORBIDDEN.search(line):
                hits.append("%s:%d: %s" % (p, k, line.strip()))
    return hits


def import_scan(project: str, cfg: Dict) -> List[str]:
    own = {ns.split(".")[0] for ns in cfg["namespaces"] + cfg.get("below", [])}
    bad = []
    for rel in cfg["layer_modules"]:
        for line in open(os.path.join(project, rel), encoding="utf-8"):
            m = re.match(r"import\s+(\S+)", line)
            if m and m.group(1) != "Provenstream.Interface" and m.group(1).split(".")[0] not in own:
                bad.append("%s imports %s" % (rel, m.group(1)))
    return bad


def run(cmd: List[str], cwd: str, env: Optional[Dict] = None) -> str:
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, env=env)
    if p.returncode != 0:
        raise CheckFailed("%s failed:\n%s" % (" ".join(cmd), (p.stdout + p.stderr)[-6000:]))
    return p.stdout + p.stderr


def core_namespace(project: str, cfg: Dict) -> str:
    """The core's namespace as the package's own sources import it (`import <Core>.Engine.Step` in its engine's main),
    so a revision from before a rename stamps with the names of its own tree; `Provenstream` when none says."""
    for p in lean_sources(project, cfg):
        m = re.search(r"^import\s+(\w+)\.Engine\.Step\b", open(p, encoding="utf-8").read(), re.M)
        if m:
            return m.group(1)
    return "Provenstream"


PACKAGE = re.compile(r"[A-Za-z0-9._-]+(/[A-Za-z0-9._-]+)*")


def package_of(project: str, env: Dict, git_dir: str) -> str:
    """The package path of the project in its repository (as scripts/stamp_revision writes it): $PROVENSTREAM_PACKAGE
    if set, else the project's directory relative to the top of its git work tree, else "" (the root package)."""
    pkg = env.get("PROVENSTREAM_PACKAGE")
    if pkg is None:
        p = subprocess.run(["git", "-C", git_dir, "rev-parse", "--show-toplevel"], capture_output=True, text=True)
        if p.returncode != 0 or not p.stdout.strip():
            return ""
        rel = os.path.relpath(os.path.realpath(project), os.path.realpath(p.stdout.strip()))
        pkg = "" if rel == "." else rel.replace(os.sep, "/")
    if pkg and (not PACKAGE.fullmatch(pkg) or any(seg in (".", "..") for seg in pkg.split("/"))):
        raise CheckFailed("not a package path: %s" % pkg)
    return pkg


def stamp(project: str, cfg: Dict, env: Optional[Dict] = None, git_dir: Optional[str] = None) -> str:
    """Write the revision module (as scripts/stamp_revision does): the commit from PROVENSTREAM_REVISION, else git's
    HEAD of the project (with -dirty for a changed tree), else unknown; the repository; and the package path
    (`package_of`); rewritten only when it changes."""
    env = env if env is not None else dict(os.environ)
    gd = git_dir or project
    commit = env.get("PROVENSTREAM_REVISION")
    if commit:
        if not re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", commit):
            raise CheckFailed("PROVENSTREAM_REVISION is not a full commit hash: %s" % commit)
    else:
        p = subprocess.run(["git", "-C", gd, "rev-parse", "HEAD"], capture_output=True, text=True)
        if p.returncode == 0:
            commit = p.stdout.strip()
            st = subprocess.run(["git", "-C", gd, "status", "--porcelain"], capture_output=True, text=True).stdout
            if st.strip():
                commit += "-dirty"
        else:
            commit = "unknown"
    repo = env.get("PROVENSTREAM_REPO_URL")
    if not repo:
        p = subprocess.run(["git", "-C", gd, "remote", "get-url", "origin"], capture_output=True, text=True)
        repo = p.stdout.strip() if p.returncode == 0 and p.stdout.strip() else "unknown"
    package = package_of(project, env, gd)
    q = lambda x: '"' + x.replace("\\", "\\\\").replace('"', '\\"') + '"'
    core = core_namespace(project, cfg)
    new = ("import %s.Engine.Step\n\n/-! Written by provenstream (stamp); not in git. The revision this engine is "
           "built from. -/\n\ndef %s : %s.Engine.Revision :=\n  ⟨%s, %s, %s⟩\n"
           % (core, cfg["revision_def"], core, q(commit), q(repo), q(package)))
    out = os.path.join(project, cfg["revision_module"])
    old = open(out, encoding="utf-8").read() if os.path.exists(out) else None
    if old != new:
        with open(out, "w", encoding="utf-8") as f:
            f.write(new)
    return "stamp: %s (%s%s) -> %s" % (commit, repo, ", " + package if package else "", out)


def lean_eval(project: str, body: str) -> str:
    fd, path = tempfile.mkstemp(suffix=".lean", dir=project, prefix=".provenstream-check-")
    with os.fdopen(fd, "w") as f:
        f.write(body)
    try:
        return run([lake(), "env", "lean", path], project)
    finally:
        os.unlink(path)


# Every proof inherits from the core's: its engine's `main` is `Engine.Layered.mainAt L ...` (or `Layered.main`) of one
# of the project's audit roots `L`, a `Layer B` whose base `B` is the core's (`coreBase`), or `Layer.toBase L'` of a
# layer `L'` that inherits from it in turn; or, for the core itself, `main` serves `coreService`. Written here, not in
# the proof's tree, so the same check runs on every revision (the core's namespace is the tree's own: `C`).
INHERITS = """import Lean
import %(main_module)s
open Lean Meta

namespace ProvenstreamInherits

mutual
/-- Why the base `B` is not the core's, or none; `named` is the last name it was reached by. -/
partial def baseWhy (B : Expr) (named : Option Name := none) : MetaM (Option String) := do
  let B ← instantiateMVars B
  if B.isConstOf `%(C)s.coreBase then return none
  if B.getAppFn.isConstOf `%(C)s.Layer.toBase && B.getAppNumArgs == 2 then return ← layerWhy B.appArg!
  let named := if B.getAppFn.isConst then some B.getAppFn.constName! else named
  match ← unfoldDefinition? B with
  | some B' => baseWhy B'.headBeta named
  | none =>
    let what := match named with | some n => toString n | none => "a base defined in place"
    return some s!"its base is {what}, which is not the core's (coreBase, or Layer.toBase of a layer on it)"

/-- Why `L` is not a layer that inherits from the core's proof, or none. -/
partial def layerWhy (L : Expr) : MetaM (Option String) := do
  let t ← whnf (← inferType L)
  if t.getAppFn.isConstOf `%(C)s.Layer && t.getAppNumArgs == 1 then
    match ← baseWhy t.appArg! with
    | none => return none
    | some why => return some s!"{← ppExpr L}: {why}"
  return some s!"{← ppExpr L} is not a Layer (its type is {← ppExpr t})"
end

def mainWhy (roots : List Name) : MetaM (Option String) := do
  let some ci := (← getEnv).find? `main | return some "the engine's module %(main_module)s has no main"
  let some v := ci.value? | return some "main has no definition"
  lambdaTelescope v fun _ body => do
    let f := body.getAppFn
    if f.isConstOf `%(C)s.Engine.Layered.mainAt || f.isConstOf `%(C)s.Engine.Layered.main then
      let L := body.getAppArgs[1]!
      unless L.isConst && roots.contains L.constName! do
        return some s!"main serves {← ppExpr L}, which is not one of the project's audit roots {roots}"
      return ← layerWhy L
    if roots == [`%(C)s.coreService] then
      let serves := body.find? fun e => e.getAppFn.isConstOf `%(C)s.Engine.serveStdioAt
      match serves with
      | some e => if e.getAppArgs[0]!.isConstOf `%(C)s.coreService then return none
                  else return some s!"main serves {← ppExpr e.getAppArgs[0]!}, not coreService"
      | none => return some "main does not serve coreService"
    return some s!"main is not %(C)s.Engine.Layered.mainAt of a layer: it is {← ppExpr f}"

def run (roots : List Name) : MetaM Unit := do
  match ← mainWhy roots with
  | none => IO.println s!"inherits: main serves {roots}, on the core's proof"
  | some why => IO.println s!"inherits: FAIL {why}"; throwError why

end ProvenstreamInherits

#eval ProvenstreamInherits.run [%(roots)s]
"""


def engine_root(project: str, cfg: Dict) -> str:
    """The root module of the project's engine (`[[lean_exe]]` named `cfg["engine"]` in lakefile.toml; Lake's default
    root is the executable's name)."""
    path = os.path.join(project, "lakefile.toml")
    try:
        text = open(path, encoding="utf-8").read()
    except OSError as x:
        raise CheckFailed("%s: %s (the engine's root module is read from a lakefile.toml)" % (path, x.strerror))
    for block in re.split(r"^\[\[", text, flags=re.M)[1:]:
        if not block.startswith("lean_exe]]"):
            continue
        name = re.search(r'^name\s*=\s*"([^"]+)"', block, re.M)
        if name and name.group(1) == cfg["engine"]:
            root = re.search(r'^root\s*=\s*"([^"]+)"', block, re.M)
            return root.group(1) if root else name.group(1)
    raise CheckFailed("%s: no [[lean_exe]] named %s" % (path, cfg["engine"]))


def inherits(project: str, cfg: Dict) -> str:
    """Check that the project's engine serves a layer that inherits from the core's proof (`INHERITS`); answers what
    it found, or raises `CheckFailed` with why not. Needs the project built (`lake build`)."""
    body = INHERITS % {"main_module": engine_root(project, cfg), "C": core_namespace(project, cfg),
                       "roots": ", ".join("`" + r for r in cfg["audit_roots"])}
    try:
        out = lean_eval(project, body)
    except CheckFailed as x:
        why = re.search(r"inherits: FAIL (.*)", str(x))
        raise CheckFailed("the engine does not inherit from the core's proof: %s" % why.group(1) if why else str(x))
    return "\n".join(l for l in out.splitlines() if l.startswith("inherits:"))


def check(project: str, say=print, env: Optional[Dict] = None) -> Dict:
    """Run the checks on `project`; raises `CheckFailed` at the first failure. Answers what was found."""
    project = os.path.abspath(project)
    cfg = load(project)
    result: Dict = {"project": project}
    say("== 1. stamp and lake build")
    say(stamp(project, cfg, env))
    out = run([lake(), "build"], project, env)
    if re.search(r"warning: \S+\.lean:|declaration uses 'sorry'", out):
        raise CheckFailed("the build has a Lean warning or a sorry:\n" + "\n".join(
            l for l in out.splitlines() if ".lean:" in l or "sorry" in l))
    say(out.strip().splitlines()[-1])
    imports = "".join("import %s\n" % ns.split(".")[0] for ns in cfg["namespaces"])
    say("== 2. axioms (allowed: propext, Quot.sound, Classical.choice)")
    out = lean_eval(project, "import ProvenstreamCheck\n%s\nopen Lean in\n#eval ProvenstreamCheck.axioms [%s]\n"
                    % (imports, ", ".join("`" + ns for ns in cfg["namespaces"])))
    say(out.strip())
    say("== 3. forbidden words, and the layer's imports")
    srcs = lean_sources(project, cfg)
    hits = word_scan(srcs)
    if hits:
        raise CheckFailed("forbidden words:\n" + "\n".join(hits))
    bad = import_scan(project, cfg)
    if bad:
        raise CheckFailed("a layer module imports more of the core than its interface:\n" + "\n".join(bad))
    say("%d files: none; the layer modules import Provenstream.Interface (and the layers below) only" % len(srcs))
    say("== 4. audit of the layer service's dependency tree")
    roots = ", ".join("``" + r for r in cfg["audit_roots"])
    out = lean_eval(project, "import ProvenstreamCheck\nimport Provenstream.Engine.Step\n%s\nopen Lean in\n#eval ProvenstreamCheck.audit [%s, "
                    "``Provenstream.Layer.service] [%s]\n" % (imports, roots,
                                                             ", ".join("`" + ns for ns in cfg["namespaces"])))
    say("\n".join(l for l in out.splitlines() if l.startswith("audit")))
    say("== 5. the proof inherits from the core's")
    say(inherits(project, cfg))
    say("== 6. the engine's self-test, description and stream interface")
    engine = os.path.join(project, ".lake", "build", "bin", cfg["engine"])
    say(run([engine, "--self-test"], project).strip())
    desc = json.loads(run([engine, "--describe"], project))
    result["describe"] = desc
    say("describes %d commands: %s" % (len(desc["schema"]["commands"]),
                                       " ".join(c["name"] for c in desc["schema"]["commands"])))
    from . import interface
    try:
        say(interface.summary(interface.check_engine(engine)))
    except interface.InterfaceMismatch as x:
        raise CheckFailed("the engine does not implement the stream interface (interface.py): %s" % x)
    result["engine"] = engine
    return result


if __name__ == "__main__":
    try:
        check(sys.argv[1] if len(sys.argv) > 1 else ".")
        print("check: all passed")
    except CheckFailed as x:
        print("check: FAILED: %s" % x, file=sys.stderr)
        sys.exit(1)
