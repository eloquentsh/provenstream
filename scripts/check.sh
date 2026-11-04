#!/usr/bin/env bash
# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
# The checks of the Lean side. Every step must pass; the first failure stops the run. Needs elan's `lake` (on PATH or in
# ~/.elan/bin) and python3 (standard library). The host's tests are scripts/test_host.sh.
#
#   1. the core: stamp, lake build (the model, every theorem, the worked examples, the engine); no warning, no sorry
#   2. axioms: every declaration under Provenstream depends on propext, Quot.sound, Classical.choice at most
#   3. forbidden words in every Lean source of the core, the examples and the tower (comments and strings stripped):
#      no sorry, admit, axiom, partial, unsafe, implemented_by, extern or native_decide
#   4. audit of the decision functions' dependency tree (scripts/Audit.lean)
#   5. the core engine's self-test and description; it serves coreService (project.py inherits)
#   6. every gap stated in Provenstream/Theorems.lean has a row in docs/tcb.md, and every row a statement
#   7. the examples, each a layer on the core (examples/log, examples/principals, examples/tasks, examples/work,
#      examples/solochangecontrol): build, axioms,
#      words, imports, audit, inherits, self-test, description, interface (project.py)
#   8. the three-level tower (tests/tower: reviews on tasks on the core): the same checks, on a layer on a layer
#   8b. the proofs that do not inherit from the core's (tests/not-the-interface): each fails project.py's checks
#   9. the corpus replays byte for byte (corpus/replay)
#  10. the negative proof tests (tests/proof-negative/run.py)
#  11. HOST-PROTOCOL.md is what the code says (scripts/gen_host_protocol --check: the host's registry, the core
#      engine's description, the answer table)
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LAKE="${LAKE:-$(command -v lake || echo "$HOME/.elan/bin/lake")}"
export LAKE
PY="${PYTHON:-python3}"
cd "$ROOT"
step() { printf '\n== %s\n' "$*"; }

sources() {
  find Provenstream examples/log/Log examples/principals/Principals examples/tasks/Tasks examples/work/Work \
    examples/solochangecontrol/SoloChangeControl tests/tower/Tower -name '*.lean' | sort
  ls ./*.lean examples/log/*.lean examples/principals/*.lean examples/tasks/*.lean examples/work/*.lean \
    examples/solochangecontrol/*.lean tests/tower/*.lean \
    | grep -v 'Revision.lean$' | grep -v ProvenstreamCheck.lean
}

step "1. lake build (the core)"
scripts/stamp_revision CoreRevision.lean coreBuilt
out="$("$LAKE" build 2>&1)" || { echo "$out"; exit 1; }
if grep -qE "warning: [^ ]+\.lean:|declaration uses 'sorry'" <<<"$out"; then echo "$out" | grep -A3 -E "warning|sorry"; exit 1; fi
echo "$out" | tail -1

step "2. axioms (allowed: propext, Quot.sound, Classical.choice)"
"$LAKE" env lean scripts/Axioms.lean

step "3. forbidden words in the Lean sources (comments and strings stripped)"
files="$(sources)"
# shellcheck disable=SC2086
hits=$("$PY" scripts/strip_lean_comments.py $files \
  | grep -wE "sorry|admit|axiom|partial|unsafe|implemented_by|extern|native_decide" || true)
if [[ -n "$hits" ]]; then echo "$hits"; exit 1; fi
echo "$(wc -l <<<"$files" | tr -d ' ') files: none"

step "4. audit of the decision functions' dependency tree"
"$LAKE" env lean scripts/Audit.lean 2>&1 | grep -E "^audit" || { "$LAKE" env lean scripts/Audit.lean; exit 1; }

step "5. core engine self-test and description"
.lake/build/bin/core-engine --self-test
.lake/build/bin/core-engine --describe | "$PY" -c 'import json,sys; d=json.load(sys.stdin); print("describes", " ".join(c["name"] for c in d["schema"]["commands"]))'
PYTHONPATH=host "$PY" -c 'from provenstream import project as p; print(p.inherits(".", p.load(".")))'

step "6. every gap stated in Provenstream/Theorems.lean has a row in docs/tcb.md, and every row a statement"
gaps=$(grep -oE '^- \*\*gap_[a-z_]+\.' Provenstream/Theorems.lean | grep -oE 'gap_[a-z_]+')
for g in $gaps; do grep -qE "^\| $g \|" docs/tcb.md || { echo "$g: not in docs/tcb.md"; exit 1; }; done
for g in $(grep -oE '^\| gap_[a-z_]+ \|' docs/tcb.md | grep -oE 'gap_[a-z_]+'); do
  grep -qE "^- \*\*$g\." Provenstream/Theorems.lean || { echo "docs/tcb.md $g: not stated in Theorems.lean"; exit 1; }
done
echo "$(wc -w <<<"$gaps" | tr -d ' ') gaps, each stated in Theorems.lean and tabled in docs/tcb.md"

step "7. the examples"
for d in examples/log examples/principals examples/tasks examples/work examples/solochangecontrol; do
  printf -- '-- %s\n' "$d"
  PYTHONPATH=host "$PY" -m provenstream.project "$d"
done

step "8. the three-level tower"
PYTHONPATH=host "$PY" -m provenstream.project tests/tower

step "8b. the proofs that do not inherit from the core's fail the checks"
for d in tests/not-the-interface/*/; do
  if out="$(PYTHONPATH=host "$PY" -m provenstream.project "$d" 2>&1)"; then echo "$d: passed the checks"; exit 1; fi
  echo "$d: $(grep -oE "check: FAILED: .*" <<<"$out" | head -1)"
done

step "9. corpus replay"
corpus/replay

step "10. negative proof tests"
"$PY" tests/proof-negative/run.py

step "11. HOST-PROTOCOL.md is generated from the code"
PYTHON="$PY" scripts/gen_host_protocol --check

printf '\ncheck.sh: all passed\n'
