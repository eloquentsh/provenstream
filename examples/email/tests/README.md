# Testing the email engine

What is here is one oracle and several ways of putting the compiled engine against it. The oracle is `email_model.py`:
a Python restatement of the wire's decoding (what is `malformed`, the `.eml` ending included), the core's admission,
the layer's fifteen rules in the engine's order, the event an accepted request becomes and the notes it leaves. It is
written from the Lean, not imported from it, so a difference between the two is a finding, in one or the other.

Everything runs from the repository root with the engine built (`lake build` in `examples/email`):

```sh
PYTHONPATH=host python3 -m pytest examples/email/tests -q
```

The shape follows `examples/solochangecontrol/tests` (its README explains each layer at length); what differs here is
the vocabulary and the cutoff: the first composed draft ends drafting, where the change proof had a pull.

## The layers

1. **Random sequences with required coverage** (`test_sequences.py`). A Hypothesis state machine sends 400 runs of up
   to 80 steps by six principals on two streams and four emails, mostly valid and deliberately invalid in known ways.
   On every request the engine's answer must be the model's. After every step the theorems of `Theorems.lean` are
   checked over the accepted log as invariants, and the engine's read of each stream must be the model's notes. At
   the end `test_coverage_is_complete` reads the engine's own description and fails unless the run observed every
   (command, rule) refusal it lists, an acceptance and a malformed request per command, a wrong number of fresh ids,
   and the acceptance theorem fired as a rule. `aimed_refusal` builds requests for a drawn (command, rule) target;
   `aimed_pair` builds requests two rules of one command both refuse, so the engine's rule order is observed.
   `EMAIL_EXAMPLES` and `EMAIL_STEPS` set the budget; `EMAIL_ENGINE` names another engine binary.

2. **Named deep states** (`test_deep_states_are_reached`): a send after a composed draft; two composed drafts on one
   email (a revise round); two distinct composers; drafts by two drafters; an email created in reply to a message,
   and in reply to another email's sent message; a send with no draft and no composed draft; a close while an email
   is undecided; both streams open at once. Four scenario rules perform short valid sequences so these are reached.

3. **The acceptance theorem at every step** (`the_creator_can_always_send_everywhere`): after every step, for every
   undecided email on an open stream, the engine's state is snapshotted, the opener's send at an `.eml` not yet named
   is sent and must be accepted, and the snapshot is loaded back.

4. **Model honesty** (`test_story.py`): the worked story of `Email/Examples.lean` is parsed from the Lean file and run
   through the model and the engine, which must both give every answer the story expects.

5. **Field forms** (`test_fields.py`): requests at the boundaries the layer and the wire check: `meta` at 4096 and 4097
   bytes, control characters, an `.eml` URL at 2048 and 2049 characters, a URL without the `.eml` ending, `.EML`, a
   fragment after `.eml` (malformed) and a fragment ending in `.eml` (decoded: the blob convention), the optional
   `in_reply_to_url` absent, null, well formed and malformed, ids not in canonical form, unknown keys, missing fields.

Not ported from the change proof's tests: the engine mutants (`mutants.py`) and the recorded conformance cases
(`record.py`, `conform_solo.py`).

## What a pass means

The engine answers as the model does on every request of a run that provably exercised every refusal it describes,
every acceptance, malformed input on every command, the nine deep states, and the acceptance theorem from every state
reached; the model tells the Lean's own story; and the field forms are where the Lean puts them.
