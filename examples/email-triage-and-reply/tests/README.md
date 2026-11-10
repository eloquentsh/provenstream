# Testing the email triage and reply engine

The oracle is `mailbox_model.py`. It restates the wire's decoding, the core's admission and the layer's forty rules in
the engine's order. It also gives the event an accepted request becomes and the notes it leaves. It is written from
the Lean, not imported from it. A difference between the two is a finding, in one or the other.

Everything runs from the repository root with the engine built (`lake build` in `examples/email-triage-and-reply`):

```sh
PYTHONPATH=host python3 -m pytest examples/email-triage-and-reply/tests -q
```

The layers follow `examples/email/tests`, whose README explains them at length.

- `test_sequences.py` is a Hypothesis state machine: 300 runs of up to 60 steps by eight principals on three streams.
  It builds requests by search. It lists candidate requests from the current state and lets the model judge them.
  Then it sends one the model accepts, or one the model refuses for a drawn rule. Every answer must be the model's.
  After every step the theorems hold over the accepted log, the read is the model's notes, and the acceptance
  theorems are probed from that state. At the end every (command, rule) refusal the engine describes must have been
  seen, and every named deep state reached.
- `test_story.py` parses the story from `EmailTriageAndReply/Examples.lean`. It runs the story through the model and
  through the engine, which must both give every answer the story expects.
- `test_fields.py` sends requests at the edges of the field forms. Examples are `meta` at 4096 and 4097 bytes, an
  `_eml_url` at 2048 and 2049 characters, a URL without the `.eml` ending, the four verdicts and their near misses, and
  `principal.revoke`, which is not a command.

`MAILBOX_EXAMPLES`, `MAILBOX_STEPS` and `MAILBOX_ENGINE` set the budget and name another engine. Not ported: engine
mutants and recorded conformance cases.
