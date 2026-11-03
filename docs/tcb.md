# What is trusted, not proved

The proofs are about Lean functions (`respond`, `run`, `check`, `toEvent`, `entryRequest`, `entrySync`, the
codecs) and the values they take. Everything between those values and a running service is trusted. Each gap is
stated in full at the end of `Provenstream/Theorems.lean`; `scripts/check.sh` fails if this table and those statements
disagree.

| gap | what is trusted | what is proved or checked instead |
|---|---|---|
| gap_wire_bytes | our JSON parser and printer (`Provenstream/Engine/Json.lean`), the host's encoder | decode inverts encode for requests, events, rows, states; whatever decodes is well formed |
| gap_token_is_caller | the request's `actor_id` is whoever holds the bearer token (the host refuses any other, `actor_id_must_match_the_token`) | every event's actor is the request's `actor_id` (`toEvent_actor`), so `close_by_opener` is about that id |
| gap_principal_issuance | principal ids belong to whom the host says (a principal is an id and its tokens; `principal.create` issues them) | nothing: the model has no principals of its own |
| gap_id_collisions | fresh ids are fresh in practice | a repeat is refused `stream_id_must_be_new` (`duplicate_refused`) and changes nothing (`refused_keeps_log`): availability only |
| gap_storage_durability | the store (Postgres or SQLite) keeps what it reports committed | nothing |
| gap_store_compare_and_set | the append commits exactly at the expected length | what follows if it does (`cas_refines_run`) |
| gap_read_decide_append | the host's sync-decide-append glue is `attemptBatch` | the protocol (`cas_refines_run`, `batch_answer`) and the engine's bookkeeping (`entryRequest_spec`, `entrySync_spec`) |
| gap_concurrency | each stream's appends serialise through compare-and-set | any interleaving of committed batches is `run` (`cas_refines_run`) |
| gap_compiled_engine | the Lean and C compilers, the runtime, the pinned primitives and `@[csimp]` replacements | `scripts/Audit.lean` pins every one reached |
| gap_runtime_failures | the parser, the runtime and the IO loop do not fail mid-answer | no panic is reachable from the decision functions (audit) |
| gap_unproved_edge | the engine's per-stream map, message dispatch and loop | the edge is audited for panics and foreign JSON code |
| gap_no_unsafe_declarations | no `partial`, `unsafe`, `implemented_by`, `extern`, `native_decide` of ours | the word scan and the audit, every check |
| gap_read_visibility | who may read what | nothing: reads are outside the model, and the host restricts none: any authenticated principal reads any stream |
| gap_engine_is_revision | the binary judging a stream was built from its revision (a commit and a package path) | the revision never changes (`proof_revision_fixed`, `proof_revision_unique`, `new_proof_new_stream`, `Layer.ValidX.proof_revision_unique`); the host checks the engine's stamped commit and package; the build records a provenance manifest. An engine built from a changed tree reports `<commit>-dirty`, which is no revision key: no host installs or serves it |
| gap_snapshot_fold | a stored snapshot is the fold of the rows it names | if so, deciding from it is deciding from the stream (`snapshot_sound`); the host re-folds before trusting one |
| gap_stream_field | the schema's stream field (`stream_id`) is the request's stream | the host refuses an answer on another stream than the one it computed |

## Host-computed, not proved

| assumption | what is trusted | what is checked instead |
|---|---|---|
| host_chain | the host computes each stream's hash chain and meta commitments as `chain.py` specifies; the chain is outside the proofs | anyone recomputes it from `stream.rows` (`provenstream verify`, `replay`), against heads they kept |

## Not shortcuts

The verified path uses no `sorry`, `admit`, `axiom`, `partial`, `unsafe`, `implemented_by`, `extern` or
`native_decide`, and every declaration under `Provenstream`, `Log`, `Principals`, `Tasks` and `Tower` depends on
`propext`, `Quot.sound` and `Classical.choice` at most (`scripts/Axioms.lean`, `provenstream check`).
`ProvenstreamCheck.lean` (the audit itself) imports `Lean` and uses `partial`; it is not on the verified path and is
excluded from the scan.

## What a layer adds to the trust

Nothing beyond the gaps above, for the core's guarantees: they hold of every layer by `Layer.ValidX.base`,
`Layer.ValidX.admitted`, `Layer.ValidX.close_by_opener` and `Layer.ValidX.opener_fixed`. A layer's own guarantees
are exactly its own theorems; a rule it did not write is not enforced, and a property it did not prove is not claimed.
A layer that speaks of persons and agents (`examples/principals`) proves what its own events say of them; that a
principal is in fact a person or an agent is decided where tokens are issued (gap_principal_issuance), since the host
keeps no kinds.
