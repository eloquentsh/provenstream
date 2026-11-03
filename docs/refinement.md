# Layers as refinement

A layer (`Layer B`, `Provenstream/Layer.lean`) adds commands, events, rules and guards to a base `B`: the core
(`coreBase`) or a layer with everything below it (`L.toBase`). The combined service `L.service` interleaves the
base's events (`.inl`) and the layer's (`.inr`). In the terms of refinement, the mechanism proves:

| property | theorem | what it says |
|---|---|---|
| forward simulation by projection | `ValidX.base`, `ValidX.cores` | the base's events of a valid combined log form a valid base log: every behaviour of the layer, projected, is a behaviour of the base |
| stuttering | `bases_snoc_inr` | a layer event projects to no base event |
| admission | `ValidX.admitted`, `ValidX.admitted_open`, `ValidX.snoc_inr_iff` | every layer event was admitted by the base before any layer rule (at the core: the stream exists and is not closed; any actor) |
| guards only refuse more | `ValidX.base_refusal_stands`, `ValidX.snoc_inl_iff` | on a base event the base's rules come first and the layer's guards after; a base refusal stands in every layer |
| towers compose | `toBase_admits`, `h.base.base` | a layer on a layer: validity projects level by level, and the admission asked at the top is the bottom base's |
| references | `ValidX.ref_earlier`, `ref_target_fixed`, `ValidX.ref_target_valid` | every `ref` param names an earlier accepted event of the same stream, at a position that never changes |

Through these, every core theorem holds in every layer, stated over `cores log` (the core's events of a combined
log): `Layer.ValidX.close_by_opener` (every close, in every layer, is by the stream's opener),
`Layer.ValidX.opener_fixed` (the opener never changes), `Layer.ValidX.close_final` (nothing, of the core or a layer,
after a close) and `Layer.ValidX.proof_revision_unique` (one revision per stream).

What it does **not** give: anything about a layer's own events beyond its own rules and the core's admission. The
core admits any actor on an open stream, so who may act is what each layer's rules say, read from `v.opener` and its
own events. A guarantee about layer events is a theorem the layer proves from `ValidX.holds` (or `holdsNamed`,
`refHoldsNamed`); a rule it did not write is not enforced.

A layer's command names are disjoint from the base's (`names_ok`, checked by `decide`), so it cannot redefine a base
command. Its schema is `layerSchemaOk` (its commands mint nothing).

## References

A param of field kind `ref` (on the wire a natural number, or absent or `null`) names an earlier event of the same
stream by its 0-based position, the sequence number the host stores. Before any rule of the layer the mechanism
refuses an event whose references are not below the stream's length (`ref_must_name_an_earlier_event`). A layer's
`refRules` then read what its `tag` says of each position (`none` for base events), so a layer can require, say, that
a target is one of its own events of a given kind. No example layer has a `ref` param: the tasks layer names a parent
by its `task_id` (kind `uuid?`), and its own rule `parent_task_must_exist` requires a task of the same stream. In a
tower, a lower
layer's references index the stream as that layer sees it (its events and those below); that is the stored position
only for the top layer.

## The opener is where permissions start

The core's one rule about people is `only_opener_can_close`, a theorem in every layer (`Layer.ValidX.close_by_opener`).
The layers here build their permissions on the same fact, the stream's opener, which the core fixes
(`opener_fixed`):

- `examples/log`: `log.append` by the opener only (`only_opener_can_append`; `append_by_opener`).
- `examples/principals`: the opener is the first admin, implicitly; admins invite persons (`principal.invite`),
  promote invited persons to admins (`principal.promote`) and summon agents (`principal.summon`). Theorems:
  `declarations_by_admins`, `admins_are_persons`, `agents_never_promoted`, `declared_once`, `one_role`,
  `declared_permanent`.
- `examples/tasks`, on the core directly: the opener opens tasks and assigns them, the assignee completes
  (`only_opener_can_open_tasks`, `only_opener_can_assign`, `only_assignee_can_finish`). Theorems:
  `tasks_opened_by_opener` (nobody creates work but the opener), `assignees_named_by_opener` (nobody assigns but the
  opener), `completed_by_assignee`, `opened_once`, `assigned_once`, `completed_once`, `parent_is_earlier_task`,
  `parent_ne_self`, `rules_ignore_parent`; and the core's, inherited (`tasks_close_by_opener`, `tasks_close_final`).
- `examples/work`, on the core directly: the opener creates and assigns an item, the assignee asks preparers other
  than itself and decides, the asked reply (`only_opener_can_create`, `only_opener_can_assign`,
  `only_assignee_can_ask`, `only_asked_preparers_can_reply`, `only_assignee_can_decide`). Theorems:
  `created_by_opener`, `assigned_by_opener`, `asked_by_assignee`, `replied_by_asked_preparer`,
  `completed_by_assignee`, `cancelled_by_assignee`, `preparer_ne_assignee`, `created_once`, `item_created`,
  `assigned_once`, `asked_once`, `replied_once`, `decided_once`, `decision_final` (nothing about an item after its
  decision); and the core's (`work_close_by_opener`, `work_close_final`).

[`docs/model.md`](model.md) tables each layer's commands, events, rules and theorems.

## The three-level tower (`tests/tower`)

Core ← layer A (`examples/tasks`) ← layer B (`review.approve` by the opener of completed tasks, and a guard on the
core's `stream.close` two levels down: `completed_tasks_must_be_approved_before_close`). At the top:
`approved_by_opener`, `approved_completed`, `approved_completed_by_assignee` (layer A's `completed_by_assignee`, one
level down), `close_after_reviews` (the guard: at every close, every completed task is approved),
`tower_close_by_opener` (the core's, through `h.base`), `tower_tasks_opened_by_opener` and
`tower_parent_is_earlier_task` (layer A's),
`approve_admitted` and `tower_close_final` (the core's admission and close at the top). A worked story checks the
answers, including the two-level guard and the core's rule winning over it.

## The negative tests (`tests/proof-negative`)

`run.py` copies the tasks layer, builds it unchanged (the control), applies a case's exact edits, and requires the
build to fail with every error inside the named declaration:

- `anyone-opens`, `anyone-assigns`, `anyone-finishes`: the rule `only_opener_can_open_tasks`,
  `only_opener_can_assign` or `only_assignee_can_finish` is weakened to let anyone act; exactly the theorem drawn from
  it (`tasks_opened_by_opener`, `assignees_named_by_opener`, `completed_by_assignee`) fails to build.
- `other-closes`: the layer adds a guard meant to let someone other than the opener close, and an attempted proof of
  a valid log in which another principal closes. The attempt fails exactly at the step where the core refuses the
  close (`only_opener_can_close`), while in the same file the core's guarantee (every close is by the opener) builds.
- `close-twice`: the same for a second close of a closed stream (`stream_must_be_open`), while the core's guarantee
  that nothing follows a close builds.
- `takes-a-core-name`: the layer names one of its commands `stream.close`; the layer itself fails to build
  (`names_ok`).

What is shown: the mechanism gives a layer no way to accept a core event the core refuses
(`ValidX.base_refusal_stands` is the general statement); the attempts' failures are evidence, the general theorem is
the proof.
