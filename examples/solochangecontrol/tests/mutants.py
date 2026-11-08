#!/usr/bin/env python3
# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""Engine mutants: does the state machine (test_sequences.py) notice when the layer is wrong?

Following tests/proof-negative, each mutant is a copy of SoloChangeControl/Layer.lean with one edit, built as an
engine in a scratch package that requires this checkout's core by path and imports nothing of the real package:

- a rule mutant, one per rule: the rule's `holds` replaced by `fun _ _ _ => true`, so the rule never refuses;
- an order mutant, one per pair of rules that share a command: the two swapped in the layer's list, so that a request
  both would refuse gets the other's reason (and every rule between them that shares a command changes its place
  relative to each).

The state machine then runs against the mutant engine with the real model as its oracle. A mutant is killed when the
run fails; the sequence that killed it (shrunk by Hypothesis) is in the report. An order mutant whose every reordered
pair is a pair of rules no reachable request fails together is equivalent to the real engine: no test can kill it. Those
pairs, with the theorem that makes each impossible, are listed in IMPOSSIBLE, and the run must agree exactly: every
other mutant dies, and the equivalent ones survive.

    python3 examples/solochangecontrol/tests/mutants.py [--only NAME ...] [--jobs N] [--examples N] [--keep]
    PYTHONPATH=host python3 -m pytest examples/solochangecontrol/tests --mutants -q      (the same, as a test)

Exit 0 only when the run agrees with IMPOSSIBLE. The report is written to MUTANTS.md beside this script.
"""
from __future__ import annotations
import argparse, concurrent.futures, hashlib, os, re, shutil, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
PACKAGE = os.path.join(REPO, "examples", "solochangecontrol")
LAYER = os.path.join(PACKAGE, "SoloChangeControl", "Layer.lean")
sys.path.insert(0, os.path.join(REPO, "host"))
sys.path.insert(0, HERE)

import solo_model as M  # noqa: E402

LAKE = os.environ.get("LAKE") or shutil.which("lake") or os.path.expanduser("~/.elan/bin/lake")
REPORT = os.path.join(HERE, "MUTANTS.md")

# Pairs of rules no reachable request fails together, with the theorem (Theorems.lean) that says so. An order mutant
# that only reorders such pairs is equivalent to the real engine.
NEEDS_A_NOTE = ("revisions_must_be_unique", "developer_is_branched_once", "developer_must_not_be_a_reviewer",
                "change_must_not_be_pulled", "only_branched_developers_can_push", "change_is_pulled_once",
                "reviewer_must_not_be_a_developer", "change_is_decided_once", "change_must_be_undecided")
IMPOSSIBLE = {frozenset(("change_must_exist", r)): "a note on a change exists only once the change is created "
                                                    "(every_event_names_a_created_change), so %s cannot fail where "
                                                    "change_must_exist fails" % r for r in NEEDS_A_NOTE}
IMPOSSIBLE.update({
    frozenset(("developer_is_branched_once", "developer_must_not_be_a_reviewer")):
        "nobody is both a developer and a reviewer of a change (roles_are_disjoint)",
    frozenset(("reviewer_must_not_be_a_developer", "reviewer_must_not_be_the_opener")):
        "the opener is never a developer (no_developer_is_the_opener)",
    frozenset(("developer_must_not_be_the_opener", "developer_is_branched_once")):
        "the opener is never a developer (no_developer_is_the_opener)",
    frozenset(("developer_must_not_be_the_opener", "developer_must_not_be_a_reviewer")):
        "the opener is never a reviewer (no_reviewer_is_the_opener)",
})


# -- the layer's rules, parsed from the Lean ---------------------------------------------------------------------------

class Rule:
    def __init__(self, text: str):
        self.text = text
        self.name = re.match(r"\s*⟨\"(\w+)\"", text).group(1)
        self.commands = re.findall(r"\"(change\.\w+)\"", text.split("fun", 1)[0])


def parse_rules(source: str):
    """`(before, rules, after)`: the text before the rules list, each rule's text (`⟨...⟩`), and the text after."""
    start = source.index("rules := [")
    i = start + len("rules := [")
    rules, depth, buf = [], 0, ""
    while True:
        c = source[i]
        if c == "⟨":
            depth += 1
        if depth > 0:
            buf += c
        if c == "⟩":
            depth -= 1
            if depth == 0:
                rules.append(Rule(buf))
                buf = ""
        elif depth == 0 and c == "]":
            break
        i += 1
    return source[:start + len("rules := [")], rules, source[i:]


def render(before: str, rules, after: str) -> str:
    return before + ",\n            ".join(r.text.strip() for r in rules) + after


def always_true(rule: Rule) -> Rule:
    head = rule.text.split("fun", 1)[0]
    return Rule(head + "fun _ _ _ => true⟩")


def mutants(rules):
    """`(name, what, rules')` for every rule mutant and every order mutant."""
    out = []
    for i, r in enumerate(rules):
        out.append(("rule-" + r.name, "%s never refuses" % r.name, rules[:i] + [always_true(r)] + rules[i + 1:]))
    for i in range(len(rules)):
        for j in range(i + 1, len(rules)):
            if set(rules[i].commands) & set(rules[j].commands):
                swapped = list(rules)
                swapped[i], swapped[j] = rules[j], rules[i]
                out.append(("swap-%s-%s" % (rules[i].name, rules[j].name),
                            "%s and %s swapped" % (rules[i].name, rules[j].name), swapped))
    return out


def flipped_pairs(rules, i: int, j: int):
    """The pairs of rules sharing a command whose relative order the swap of positions i and j changes."""
    share = lambda a, b: bool(set(a.commands) & set(b.commands))
    pairs = [(rules[i], rules[j])] if share(rules[i], rules[j]) else []
    for m in range(i + 1, j):
        if share(rules[i], rules[m]):
            pairs.append((rules[i], rules[m]))
        if share(rules[m], rules[j]):
            pairs.append((rules[m], rules[j]))
    return pairs


def predicted_equivalent(rules):
    """The order mutants IMPOSSIBLE says cannot be killed, with the reasons."""
    out = {}
    for i in range(len(rules)):
        for j in range(i + 1, len(rules)):
            if set(rules[i].commands) & set(rules[j].commands):
                pairs = flipped_pairs(rules, i, j)
                if all(frozenset((a.name, b.name)) in IMPOSSIBLE for a, b in pairs):
                    out["swap-%s-%s" % (rules[i].name, rules[j].name)] = \
                        ["%s / %s: %s" % (a.name, b.name, IMPOSSIBLE[frozenset((a.name, b.name))]) for a, b in pairs]
    return out


# -- building a mutant's engine ---------------------------------------------------------------------------------------

def write_package(dst: str, layer_source: str, name: str) -> None:
    """A scratch package: the mutated layer, a root importing only it (not the theorems, which the mutant breaks, nor
    the examples), the engine's main, and a lakefile requiring this checkout's core by path."""
    os.makedirs(os.path.join(dst, "SoloChangeControl"))
    with open(os.path.join(dst, "SoloChangeControl", "Layer.lean"), "w", encoding="utf-8") as f:
        f.write(layer_source)
    shutil.copy(os.path.join(PACKAGE, "lean-toolchain"), dst)
    with open(os.path.join(dst, "SoloChangeControl.lean"), "w", encoding="utf-8") as f:
        f.write("import SoloChangeControl.Layer\n")
    with open(os.path.join(dst, "SoloMutantMain.lean"), "w", encoding="utf-8") as f:
        f.write("import SoloChangeControl.Layer\nimport Provenstream.Engine.Step\nimport SoloMutantRevision\n\n"
                "def main (args : List String) : IO UInt32 :=\n"
                "  Provenstream.Engine.Layered.mainAt SoloChangeControl.solo \"solomutant-engine\" (pure true) "
                "SoloMutant.built args\n")
    with open(os.path.join(dst, "lakefile.toml"), "w", encoding="utf-8") as f:
        f.write('name = "solomutant"\nversion = "0.1.0"\ndefaultTargets = ["solomutant-engine"]\n\n'
                '[[require]]\nname = "provenstream"\npath = %s\n\n[[lean_lib]]\nname = "SoloChangeControl"\n\n'
                '[[lean_lib]]\nname = "SoloMutantRevision"\n\n[[lean_exe]]\nname = "solomutant-engine"\n'
                'root = "SoloMutantMain"\n' % ('"' + REPO.replace("\\", "\\\\") + '"'))
    env = dict(os.environ, PROVENSTREAM_REVISION=hashlib.sha1(name.encode()).hexdigest(),
               PROVENSTREAM_REPO_URL="https://example.org/mutant/" + name, PROVENSTREAM_PACKAGE="examples/solochangecontrol")
    subprocess.run(["sh", os.path.join(REPO, "scripts", "stamp_revision"), os.path.join(dst, "SoloMutantRevision.lean"),
                    "SoloMutant.built", REPO], check=True, env=env, capture_output=True)


def build(dst: str):
    p = subprocess.run([LAKE, "build"], cwd=dst, capture_output=True, text=True)
    engine = os.path.join(dst, ".lake", "build", "bin", "solomutant-engine")
    if p.returncode != 0 or not os.path.exists(engine):
        return None, p.stdout + p.stderr
    return engine, ""


# -- running the state machine against a mutant ------------------------------------------------------------------------

def hunt(engine: str, dump_dir: str, examples: int, steps: int):
    """Run the state machine against `engine`. Answers `(killed, why, trace)`."""
    import test_sequences as T
    import record
    from hypothesis import settings, Phase
    from hypothesis.stateful import run_state_machine_as_test
    T.ENGINE, T.DUMP_DIR = engine, dump_dir
    machine_settings = settings(max_examples=examples, stateful_step_count=steps, deadline=None, database=None,
                                derandomize=True, report_multiple_bugs=False,
                                phases=[Phase.explicit, Phase.generate, Phase.shrink],
                                suppress_health_check=[T.HealthCheck.too_slow, T.HealthCheck.filter_too_much,
                                                       T.HealthCheck.data_too_large])
    try:
        run_state_machine_as_test(T.SoloChangeControl, settings=machine_settings)
    except Exception as x:  # noqa: BLE001  (Hypothesis raises the machine's AssertionError, or its own)
        trace_path = os.path.join(dump_dir, "failing.trace.json")
        trace = []
        if os.path.exists(trace_path):
            import json
            with open(trace_path, encoding="utf-8") as f:
                trace = json.load(f)["steps"]
        return True, "%s: %s" % (type(x).__name__, str(x).split("\n")[0][:300]), record.describe(trace)
    return False, "", ""


def main(argv=None) -> int:
    a = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    a.add_argument("--only", nargs="*", help="run only these mutants (names, or 'rule' / 'swap' for a kind)")
    a.add_argument("--jobs", type=int, default=4, help="parallel lake builds (default 4)")
    a.add_argument("--examples", type=int, default=200, help="Hypothesis examples per mutant before it survives")
    a.add_argument("--steps", type=int, default=80)
    a.add_argument("--keep", action="store_true", help="keep the scratch packages")
    a.add_argument("--work", help="the scratch directory (default: a temporary one)")
    a.add_argument("--report", default=REPORT)
    args = a.parse_args(argv)

    source = open(LAYER, encoding="utf-8").read()
    before, rules, after = parse_rules(source)
    names = [r.name for r in rules]
    assert names == M.RULE_NAMES, "the Lean's rules are not the model's: %s" % (names,)
    assert render(before, rules, after) == source, "the parser does not render the layer back as it is"
    all_mutants = mutants(rules)
    equivalent = predicted_equivalent(rules)
    chosen = all_mutants
    if args.only:
        chosen = [m for m in all_mutants if m[0] in args.only or m[0].split("-")[0] in args.only]
    work = args.work or tempfile.mkdtemp(prefix="solo-mutants-")
    os.makedirs(work, exist_ok=True)
    print("mutants: %d rules; %d rule mutants, %d order mutants (%d predicted equivalent); building %d in %s"
          % (len(rules), sum(1 for m in all_mutants if m[0].startswith("rule-")),
             sum(1 for m in all_mutants if m[0].startswith("swap-")), len(equivalent), len(chosen), work), flush=True)

    t0 = time.time()

    def prepare(m):
        name, what, mutated = m
        dst = os.path.join(work, name)
        shutil.rmtree(dst, ignore_errors=True)
        write_package(dst, render(before, mutated, after), name)
        engine, err = build(dst)
        return name, engine, err

    built = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for name, engine, err in pool.map(prepare, chosen):
            built[name] = (engine, err)
            print("  built %s%s" % (name, "" if engine else ": FAILED TO BUILD"), flush=True)
    print("mutants: built in %.0fs" % (time.time() - t0), flush=True)

    results = []
    for name, what, _ in chosen:
        engine, err = built[name]
        if engine is None:
            results.append((name, what, None, "did not build: " + err[-500:], ""))
            continue
        t1 = time.time()
        killed, why, sequence = hunt(engine, os.path.join(work, name, "dump"), args.examples, args.steps)
        results.append((name, what, killed, why, sequence))
        print("  %-8s %s (%.0fs)" % ("KILLED" if killed else "SURVIVED", name, time.time() - t1), flush=True)

    ok = True
    lines = ["# Engine mutants of the solo change control layer", "",
             "Written by `tests/mutants.py` (%s). %d rule mutants and %d order mutants of `Layer.lean`, each built as "
             "an engine and run against the state machine of `test_sequences.py` with the real model as oracle."
             % (time.strftime("%Y-%m-%d"), sum(1 for m in chosen if m[0].startswith("rule-")),
                sum(1 for m in chosen if m[0].startswith("swap-"))), ""]
    for name, what, killed, why, sequence in results:
        expected_alive = name in equivalent
        if killed is None:
            verdict, ok = "DID NOT BUILD", False
        elif killed and expected_alive:
            verdict, ok = "KILLED, but predicted equivalent: IMPOSSIBLE is wrong", False
        elif killed:
            verdict = "killed"
        elif expected_alive:
            verdict = "survived, as predicted: equivalent"
        else:
            verdict, ok = "SURVIVED: the generator does not reach it", False
        lines.append("## %s" % name)
        lines.append("")
        lines.append("%s. **%s**." % (what, verdict))
        if expected_alive:
            lines.append("")
            lines.extend("- %s" % r for r in equivalent[name])
        if killed:
            lines.append("")
            lines.append("Killed by (`%s`):" % why)
            lines.append("")
            lines.append("```")
            lines.append(sequence or "(no trace was written)")
            lines.append("```")
        lines.append("")
    n_killed = sum(1 for r in results if r[2])
    summary = ("%d mutants: %d killed, %d survived (%d predicted equivalent), %d did not build; %s"
               % (len(results), n_killed, sum(1 for r in results if r[2] is False), len(equivalent),
                  sum(1 for r in results if r[2] is None), "as predicted" if ok else "NOT AS PREDICTED"))
    lines.insert(3, summary)
    lines.insert(4, "")
    with open(args.report, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))
    print("mutants: " + summary)
    print("mutants: report at " + args.report)
    if not args.keep and not args.work:
        shutil.rmtree(work, ignore_errors=True)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
