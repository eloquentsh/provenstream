# Testing the inbound email triage engine

One oracle, `triage_model.py` (a Python restatement of the wire's decoding, the core's admission, the layer's fifteen
rules in the engine's order, the event an accepted request becomes and the notes it leaves), and the same layers as
`examples/email/tests` (whose README explains them): a Hypothesis state machine with required coverage and named deep
states (`test_sequences.py`), the acceptance theorem `the_creator_can_always_ignore` probed at every step, the Lean
story parsed and replayed (`test_story.py`), and the field forms at the boundaries (`test_fields.py`), the `verdict`
kind among them: exactly `reply` or `ignore`, and nothing else.

```sh
PYTHONPATH=host python3 -m pytest examples/emailtriage/tests -q
```

`TRIAGE_EXAMPLES`, `TRIAGE_STEPS` and `TRIAGE_ENGINE` as the email tests' `EMAIL_*`. Not ported: engine mutants,
recorded conformance cases.
