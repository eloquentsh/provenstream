# Testing the solo change control engine

What is here is one oracle and several ways of putting the compiled engine against it. The oracle is `solo_model.py`:
a Python restatement of the wire's decoding (what is `malformed`), the core's admission, the layer's seventeen rules in
the engine's order, the event an accepted request becomes and the notes it leaves. It is written from the Lean, not
imported from it, so a difference between the two is a finding, in one or the other.

Everything runs from the repository root with the engine built (`lake build` in `examples/solochangecontrol`):

```sh
PYTHONPATH=host python3 -m pytest examples/solochangecontrol/tests -q
```

That is the default run: about 30 seconds, 54 tests, and it fails unless the requirements below are met.

## The layers

### 1. Random sequences with required coverage (`test_sequences.py`)

A Hypothesis state machine sends 400 runs of up to 80 steps of commands to the engine, by six principals on two
streams and four changes, mostly valid and deliberately invalid in known ways. On every request the engine's answer
must be the model's: the reason of a refusal, the event and position of an acceptance, `malformed` for a request the
engine does not decode. After every step the theorems of `Theorems.lean` are checked over the accepted log as
invariants, and the engine's read of each stream must be the model's notes.

At the end, `test_coverage_is_complete` reads the engine's own description (`{"query": "describe"}`) and fails unless
the run observed, for every command: every (command, rule) refusal the description lists, at least one acceptance, and
at least one malformed request; plus a wrong number of fresh ids on `stream.open` and on a layer command, and the
acceptance theorem fired as a rule. The expected pairs come from the description, not from a list in the test, so a
rule added to the layer becomes a requirement here by itself. `test_description_is_the_model` checks the other
direction: the engine describes exactly the commands, fields, kinds and rule order the model restates.

The coverage is reached by construction, not by luck: besides the random rules, a rule (`aimed_refusal`) draws a
target (command, reason) and builds a request from the current state that the model will refuse for that reason, doing
one step of setup first when the state lacks what the target needs. A second such rule (`aimed_pair`) builds requests
that two rules of one command both refuse, so that the order in which the engine tries its rules is observed as well
as the rules themselves. In a 400 x 80 run the rarest pair is seen about 20 times and the common ones hundreds of
times; the counters are printed at the end of the run.

`SOLO_EXAMPLES` and `SOLO_STEPS` set the budget. `SOLO_ENGINE` names another engine binary.

### 2. Named deep states (`test_deep_states_are_reached`)

Seven predicates over the accepted log, each of which some run must reach: a merge after at least one review; a review
before the pull and a review after it; two distinct reviewers on one change; pushes by two developers on one change; a
change created from another change's merged revision; a close while a change is undecided; both streams open at once.
Four scenario rules (a second developer pushes, two reviews, pull then review, review then merge) perform a short valid
sequence on one change in one step, so that these states are reached in tens of runs out of 400 while the single-step
rules keep producing the invalid cases. The number of runs that reached each state is printed with the counters.

### 3. The acceptance theorem at every step (`the_creator_can_always_merge_everywhere`)

After every step, for every undecided change on an open stream: the engine's state is snapshotted (`snapshot`), the
opener's merge at a revision not yet named on the change is sent and must be accepted at the stream's current length,
and the snapshot is loaded back (`load`), after which the stream's read must be unchanged. This exercises
`the_creator_can_always_merge` from every state the run passes through, some 15,000 times per default run, at about
five seconds of the thirty. The theorem is also exercised as a rule (`the_creator_can_always_merge`), which merges for
real.

### 4. Engine mutants (`mutants.py`, opt-in)

```sh
PYTHONPATH=host python3 examples/solochangecontrol/tests/mutants.py          # or: pytest ... --mutants
```

Following `tests/proof-negative`: for each of the 17 rules, a copy of `Layer.lean` with that rule's `holds` replaced by
`fun _ _ _ => true` is written into a scratch package that requires this checkout's core by path and imports nothing
of the real package, stamped (`scripts/stamp_revision`) and built with `lake build`. For each pair of rules that share
a command (50 pairs), another copy with the two swapped in the rules list. Each mutant engine is run under the state
machine with the real model as oracle; a mutant is killed when the run fails, and the sequence that killed it, shrunk
by Hypothesis, goes into `MUTANTS.md` beside this file.

Five order mutants are equivalent to the real engine and no test can kill them: every pair whose relative order they
change is a pair of rules that no reachable request fails together, and the theorem that makes each such pair
impossible is named in `IMPOSSIBLE` in the script (a note on a change exists only once it is created; the roles are
disjoint; the opener is neither a developer nor a reviewer). The script fails unless the run agrees with that table
exactly: the other 62 mutants die and those five survive. Building the 67 engines takes under a minute with four
parallel `lake` jobs; the runs take about ten minutes, most of it Hypothesis shrinking each killing sequence. The run
of 2026-11-04 (`MUTANTS.md`): 62 killed, 5 survived, as predicted.

### 5. Model honesty (`test_story.py`)

The worked story of `SoloChangeControl/Examples.lean` is parsed from the Lean file (its names, revisions, every entry
of `story` with the answer it expects) and run through the model, which must give every answer the story expects, and
through the engine, which must give the model's answer at the model's position. A story that the Lean's `#guard`
holds at build time is thus held of the Python oracle too, and the test follows the file when it changes.

### 6. Field forms (`test_fields.py`)

Forty-eight requests at the boundaries the layer and the wire check: `meta` of exactly 4096 and 4097 UTF-8 bytes (as two-byte
and as one-byte characters), control characters and DEL and U+0000 in `meta`, a URL of exactly 2048 and 2049
characters, URLs with a space, DEL, non-ASCII text, two separators, no scheme, nothing after the scheme; ids not in
canonical lowercase form (change, stream, developer, actor, a fresh id), an unknown key, an old field name beside the
new, each required field missing, an unknown command, the optional `harness_revision_url` absent, null, well formed and
malformed, and a proof URL holding a tab (a `text` field: refused by the rule, not by the wire) or U+0000 (malformed).
For each, the model's prediction must be `malformed` exactly where the layer's definitions say so, and the engine's
answer must be the model's. Each case is sent from the same state, restored from the engine's snapshot between cases.

### 7. Recorded sequences (`record.py`, `cases/`, `conform_solo.py`)

`record.py` turns a trace the state machine ran into cases in the format of `conformance/cases` (see
`conformance/README.md`): one case per request by a role, the host's expected answer, and the streams read back at
the end with their chain checked. Requests no host could send are left out (a wrong number of fresh ids, an open of an
existing stream, a request malformed in its `actor_id` or `fresh`), and a trace with more than four principals is
refused since the runner has four roles.

```sh
SOLO_RECORD=1 PYTHONPATH=host python3 -m pytest examples/solochangecontrol/tests/test_sequences.py -q
```

restricts the run to four principals, derandomizes it, and writes the six best passing sequences (by deep states
reached and accepted events) to `cases/solochangecontrol.jsonl`. A failing sequence is always written, shrunk, to
`.hypothesis/failing.jsonl` (as cases, the last one expecting what the model wanted) and `.hypothesis/failing.trace.json`
(raw, with the engine's answers).

```sh
PYTHONPATH=host python3 examples/solochangecontrol/tests/conform_solo.py
```

runs the recorded cases through the conformance runner against a throwaway in-process host: at the time of writing, 394
cases from 6 sequences, all passing (`--target stdio` and `--target http` run the same cases over those carriers). Two
things the host does differently from a bare engine are encoded in `record.py`: the host finds the stream before it asks
the engine to decode, so a malformed command on a stream the host does not have is refused `stream_must_exist` rather
than `invalid_params`; and a stream's bindings (`$<run>_s1`, its chain heads) are per run of the theme, so each sequence
names its own. The runner's own table of
proofs (`conform.PROOFS`) and `make_cases.py` do not know the solo proof yet, so the script adds the proof to the table
in its own process only and reads the cases from here; and because the runner builds engines from the committed tree,
the script builds the core's and the solo proof's engines from a copy of the working tree, stamped with HEAD's commit.
Making the solo proof a theme of the suite proper means adding it to `conform.PROOFS` and a `Model` and sequences to
`conformance/make_cases.py`, which is a change to the shared suite and is not done here.

## What a pass means

The engine answers as the model does on every request of a run that provably exercised every refusal it describes,
every acceptance, malformed input on every command, the seven deep states, and the acceptance theorem from every state
reached; the model tells the Lean's own story; the field forms are where the Lean puts them; and, when the mutant layer
is run, no rule can be dropped and no killable reordering made without the run noticing.
