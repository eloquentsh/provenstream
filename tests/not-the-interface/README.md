# Proofs that do not inherit from the core's

Three Lean packages that are valid proofs (they build, with no `sorry`, and prove their theorems) and whose engines pass
their own self-test and describe themselves, but which do not inherit from the core's proof. Every proof must: its
engine's `main` is `Provenstream.Engine.Layered.mainAt` of a `Layer` on the core's base (`coreBase`), or on a layer on
it (`project.inherits`, run by `provenstream build` and `provenstream check`). An engine must also implement the stream
interface, answering the core's recorded sessions as the core does (`host/provenstream/interface.py`, run by `build`,
`install`, `check` and a host's `stream.open`).

- `norules`: describes the core's two commands, but its `main` is a loop of its own that accepts every request. Both
  checks find it: the source check (its `main` is not `mainAt` of a layer) and the interface check (the first line of
  `core-rules`, a close of a stream never opened, which the core refuses `stream_must_exist`, it accepts).
- `counter`: a command and event stream of its own (`counter.add`), with neither of the core's commands. Both checks
  find it: the source check, and the interface check at the engine's description (it does not describe the core's
  `stream.open`).
- `otherbase`: the tasks layer (`examples/tasks`), served by the convention, on `looseBase`: a copy of the core's base
  with the rule `only_opener_can_close` taken out, so anyone closes any open stream (its self-test shows a close by
  someone other than the opener accepted). Both checks find it: the source check (its base is not the core's), and the
  interface check, first at the engine's description (its `stream.close` does not list `only_opener_can_close`) and,
  were the description to list it, at `core-rules` line 24, a close by someone other than the opener, which the core
  refuses `only_opener_can_close` and `otherbase` accepts (also `core-cache`'s sync and check of such a close).

`host/tests/test_interface.py` builds each; `scripts/check.sh` step 8b runs `provenstream check` on each and expects it
to fail. None is in check.sh's sources: they are test inputs, not part of the core.
