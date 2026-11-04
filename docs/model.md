# The formal model

Lean 4 (v4.35.0), core library only: no Mathlib, no `import Lean` on the verified path. The one import beyond `Init` is
`Std.Data.HashMap` from the toolchain's own Std, used by the unproved engine edge (`Provenstream/Engine/Step.lean`, its
cache), not by anything verified. Sources in `Provenstream/` (the core), `examples/log`, `examples/principals`,
`examples/tasks`, `examples/work`, `examples/solochangecontrol` and `tests/tower` (layers on it).

## Events, commands, requests

Two core events (`Event.lean`), one constructor each: `streamOpened actor stream url meta` (`stream.opened`) and
`streamClosed actor stream meta` (`stream.closed`). There are no kinds, no roles and no declarations. A caller sends a
`Command` (no actor, no minted id); a `Request` is the caller's id (`actor_id` on the wire), the command and the fresh
ids the host minted. `toEvent` makes exactly one event, or refuses `fresh_ids_must_match_the_command` when the fresh
ids are not as many as the command mints, and `toRequest` inverts it (`toEvent_ok_iff`, `toEvent_toRequest`,
`toRequest_toEvent`). The event's actor is the request's caller (`toEvent_actor`), its stream the command's
(`toEvent_stream`), and its minted ids the fresh ones (`toEvent_minted`). Every command, the core's and every
layer's, is on the wire by a schema entry (`Schema.lean`: its params and their field kinds, the ids it mints, the
param naming its stream, its event and the event's fields, and a sentence saying who may send it), which is also what
the engine prints to describe itself, with the names of the rules that judge each command.

A stream's proof revision is its `proof_revision_url`, which names a commit and a package (`validRevisionUrl`):
`<repo>/commit/<commit>` (also `<repo>#<commit>`, `<repo>@<commit>`) the repository's root package,
`<repo>/tree/<commit>/<package>` another package of the same commit. So one commit serves several proofs, each its own
revision.

## Validity and the core's rules

A log is a list of events. `Valid` (`Service.lean`) is the logs built only by accepting candidates: each event held
every rule against the log before it. The rules (`Rules.lean`) read a `View` of the event's stream only
(`rejection_local`):

```lean
structure View where
  opened : Bool
  closed : Bool
  /-- `none` until opened; fixed once set (`opener_fixed`). -/
  opener : Option Id
```

each a flat statement over the past (`Past.opened`, `Past.closed`, `Past.opener`). The core's rules, in order (the
first that fails is the reason):

| rule | command | requires |
|---|---|---|
| `stream_id_must_be_new` | `stream.open` | the minted id names no stream opened before |
| `revision_url_must_name_a_commit` | `stream.open` | the URL is a revision URL (`validRevisionUrl`) |
| `stream_must_exist` | `stream.close` | the stream was opened |
| `stream_must_be_open` | `stream.close` | the stream is not closed |
| `only_opener_can_close` | `stream.close` | the actor is the stream's opener |

What the core asks of every layer event, before the layer's rules, is `View.admits`: the stream exists and is open
(`stream_must_exist`, `stream_must_be_open`; `View.admits_none`). It admits any actor: who may act is each layer's
business, and a layer's rules read `v.opener`. "Only the opener may act" cannot be a core rule, since a layer can only
refuse more: no layer could ever let anyone else act.

`check` decides `Valid` (`check_iff_valid`); `run` of any requests produces only valid logs (`run_valid`), and every
valid log is `run` of its own requests (`run_total`).

## What the core guarantees (`Theorems.lean`)

| theorem | statement, for a valid log | |
|---|---|---|
| `close_by_opener` | every close is by the stream's opener, as the log before it says | new |
| `opener_fixed` | a stream is opened once: two openings of one stream id are one event, one opener, one revision | restated (was `stream_fixed`) |
| `opener_stays`, `opener_of_open`, `opener_mem`, `opener_isSome` | once a stream has an opener, nothing changes it; it is the actor of the opening | new |
| `close_admitted`, `close_final`, `close_once` | a close is on an open stream; nothing on the stream follows it; a stream closes once | kept |
| `opened_of_mem`, `opened_iff` | every event is on a stream opened before it; a stream exists iff it was opened | kept |
| `open_fresh`, `minted_once`, `minted_same`, `minted_open`, `minted_eq_opened` | a stream id is minted once, by its opening, and by nothing else | kept |
| `proof_revision_fixed`, `proof_revision_unique`, `proof_revision_stays`, `stream_revision_valid`, `new_proof_new_stream`, `fold_url` | a stream's revision is set by its opening, is a valid revision URL, and never changes; a new proof means a new stream | kept |
| `duplicate_refused`, `refused_keeps_log` | a repeated id is refused; a refusal changes nothing | kept |
| `stream_id_new_iff_stream_empty`, `respond_local`, `run_project` | deciding is per stream | kept (`stream_id_new_iff_stream_empty` was `idTaken_iff_stream_empty`) |
| `cas_refines_run` (generic, `Service.lean`) | any interleaving of compare-and-set batch appends is `run` of the committed requests | kept |
| `fold_sound`, `snapshot_sound`, `entryRequest_spec`, `entrySync_spec`, `replayRows_sound`, `replayRows_total` | the engine's fast path, snapshots, per-stream bookkeeping and replay are the specification | kept |
| `requestFromJ_toJ`, `eventFromJ_toJ`, `stateFromJ_toJ`, `rowFromJ_toJ`, `requestFromJ_schema`, `requestToJ_schema` | the wire codecs round-trip, and the advertised schema is the decoded one | kept |

**History.** The earlier core declared principals and their kinds (persons, admins, agents) itself and proved
theorems about them. The two-command core has no declarations, so those theorems are gone with them; the core proves
nothing about who a principal is. What they said of admins and agents is now said by `examples/principals`, as
theorems about its own events (`declared_once`, `one_role`, `declared_permanent`, `admins_are_persons`; below).

## Layers

A `Layer B` (`Layer.lean`, [refinement](refinement.md)) adds commands, events, rules and guards to a base `B`: the core
(`coreBase`), or a layer with everything below it (`L.toBase`). Proved once for every layer, over `ValidX` (the valid
combined logs):

| theorem | statement | |
|---|---|---|
| `ValidX.base`, `ValidX.cores` | the core's events of a layer's valid log are a valid core log | kept |
| `ValidX.base_refusal_stands` | a core refusal is a refusal in every layer; a layer's guards only refuse more | kept |
| `ValidX.close_by_opener` | in every layer, every close is by the stream's opener | new |
| `ValidX.opener_fixed` | in every layer, a stream's opener (and revision) never changes | new |
| `ValidX.close_final`, `ValidX.proof_revision_unique` | nothing, of the core or any layer, after a close; one revision per stream | kept |
| `ValidX.admitted`, `ValidX.admitted_open` | every layer event is on an open, unclosed stream (it no longer says its actor was declared) | weaker |
| `ValidX.holds`, `ValidX.holdsNamed`, `ValidX.guardHolds`, `ValidX.refHoldsNamed` | every rule, guard and reference rule of the layer held of each of its events | kept |

### References

A param of field kind `ref` names an earlier event of the same stream by its 0-based position (the sequence number
the host stores and returns); on the wire it is a natural number, or absent or `null` for none. Any layer may use
one; no example does (a field naming a task, a principal or any other thing by its id is a `uuid`, or a `uuid?`
when it may be absent or `null`, and the layer's rules say what it must name). The mechanism checks every reference of every layer event before the layer's rules: a position not below the
stream's length at decision time is refused `ref_must_name_an_earlier_event`. A layer reads its targets through its
`tag` and `refRules`. Proved once for every layer:

| theorem | statement |
|---|---|
| `ValidX.ref_earlier` | every reference names a position below the referring event's own, holding an earlier event of the same stream: no forward, self, cross-stream or cyclic references |
| `ref_target_fixed` | the event at a position never changes, whatever is appended |
| `ValidX.ref_target_valid` | the target is an accepted event: the log before it is valid with it appended, so every theorem of accepted events holds of it |

## The layers in this repository

Each is a layer on the core, served from the same commit as the core, each by its package path. Every command takes
`stream_id` and an optional `meta`; every event carries `event`, `stream_id`, `actor_id` and `meta`, plus the fields
listed. Each command's rules come after the core's admission (`stream_must_exist`, `stream_must_be_open`).

### `examples/log`

| command | event | rules |
|---|---|---|
| `log.append {stream_id, text, meta?}` | `log.appended {text}` | `only_opener_can_append` |

`append_by_opener`: every append in a valid log is by the stream's opener. `append_on_open_stream`: every append is on
an open, unclosed stream (`ValidX.admitted_open`).

### `examples/principals`

| command | event | rules |
|---|---|---|
| `principal.invite {stream_id, principal_id, meta?}` | `principal.invited {principal_id}`: a person | `only_admins_can_invite`, `principal_must_be_new` |
| `principal.promote {stream_id, principal_id, meta?}` | `principal.promoted {principal_id}`: an invited person made an admin | `only_admins_can_promote`, `principal_must_be_invited`, `principal_is_promoted_once` |
| `principal.summon {stream_id, principal_id, meta?}` | `principal.summoned {principal_id}`: an agent | `only_admins_can_summon`, `principal_must_be_new` |

An admin is the opener (implicitly: no event declares it) or a promoted principal. `principal_must_be_new`: not yet
invited or summoned in the stream, and not its opener. Principal ids are any UUIDs: the proof cannot check that the
host knows them. Person and agent are only what this layer's events say: nothing proves the opener a person, which is
decided where tokens are issued.

| theorem | statement |
|---|---|
| `declarations_by_admins` | every invite, promote and summon is by an admin of the stream at that point |
| `admins_are_persons` | every admin other than the opener was invited in the stream (a person, as this layer's events say) |
| `promoted_was_invited`, `promoted_once` | a promoted principal was invited, and is promoted once |
| `agents_never_promoted` | a summoned principal is never promoted, so never an admin |
| `declared_once` | a principal is invited or summoned at most once per stream, and never its opener |
| `one_role` | no principal is both invited and summoned in a stream |
| `declared_permanent`, `admin_stays` | once invited, summoned or promoted, always so in every extension of the log; so is being an admin |

### `examples/tasks`

Tasks sits on the core directly, not on principals.

| command | event | rules |
|---|---|---|
| `task.open {stream_id, task_id, parent_task_id?, meta?}` | `task.opened {task_id, parent_task_id}` | `only_opener_can_open_tasks`, `task_id_must_be_new`, `parent_task_must_exist` |
| `task.assign {stream_id, task_id, assignee_id, meta?}` | `task.assigned {task_id, assignee_id}` | `only_opener_can_assign`, `task_must_exist`, `task_is_assigned_once` |
| `task.complete {stream_id, task_id, meta?}` | `task.completed {task_id}` | `task_must_exist`, `only_assignee_can_finish` (an unassigned task too), `task_is_completed_once` |

`parent_task_id` (kind `uuid?`) is the parent's own `task_id`, or absent or null: a task opened earlier on the same
stream (`parent_task_must_exist`). A task is assigned once, to any principal.

| theorem | statement |
|---|---|
| `tasks_opened_by_opener` | nobody creates work but the opener: every `task.open` is by the stream's opener |
| `assignees_named_by_opener` | nobody assigns but the opener: every `task.assign` is by the opener, so every assignee was named by it |
| `completed_by_assignee` | a task is completed only by its assignee, assigned before |
| `opened_once`, `assigned_after_open`, `assigned_once`, `completed_after_open`, `completed_once` | each step once, and in order |
| `parent_is_earlier_task`, `parent_ne_self`, `rules_ignore_parent` | a present `parent_task_id` names a task whose `task.opened` is earlier on the same stream; no task is its own parent; every rule but `parent_task_must_exist` holds of a child exactly as of a task without a parent |
| `tasks_close_by_opener`, `tasks_close_final` | the core's, inherited (`Layer.ValidX.close_by_opener`, `Layer.ValidX.close_final`) |

### `examples/work`

A basic task system on the core directly. Every id is any UUID; a reply's preparation travels in `meta`.

| command | event | rules |
|---|---|---|
| `work.create {stream_id, work_id, meta?}` | `work.created {work_id}` | `only_opener_can_create`, `work_id_must_be_new` |
| `work.assign {stream_id, work_id, assignee_id, meta?}` | `work.assigned {work_id, assignee_id}` | `only_opener_can_assign`, `work_must_exist`, `work_is_assigned_once` |
| `work.ask {stream_id, work_id, preparer_id, meta?}` | `work.asked {work_id, preparer_id}` | `work_must_exist`, `only_assignee_can_ask`, `work_must_be_undecided`, `preparer_must_not_be_the_assignee`, `preparer_is_asked_once` |
| `work.reply {stream_id, work_id, meta?}` | `work.replied {work_id}` | `work_must_exist`, `only_asked_preparers_can_reply`, `work_must_be_undecided`, `preparer_replies_once` |
| `work.complete {stream_id, work_id, meta?}` | `work.completed {work_id}` | `work_must_exist`, `only_assignee_can_decide`, `work_is_decided_once` |
| `work.cancel {stream_id, work_id, meta?}` | `work.cancelled {work_id}` | `work_must_exist`, `only_assignee_can_decide`, `work_is_decided_once` |

An item is decided when it is completed or cancelled. The opener may assign an item to itself; the assignee may not
ask itself to prepare; an unassigned item can be neither asked about nor decided (the assignee rules fail with no
assignee). Completion needs no reply.

| theorem | statement |
|---|---|
| `created_by_opener`, `assigned_by_opener` | nobody creates or assigns work but the opener |
| `asked_by_assignee` | every ask is by the item's assignee, whom the opener named |
| `replied_by_asked_preparer` | every reply is by a preparer the assignee asked, the assignee named by the opener |
| `completed_by_assignee`, `cancelled_by_assignee` | every decision is by the item's assignee |
| `preparer_ne_assignee` | no preparer is the item's assignee |
| `created_once`, `item_created`, `assigned_once`, `asked_once`, `replied_once`, `decided_once` | each step once, and on a created item |
| `decision_final` | after an item is completed or cancelled, no work event about it is accepted (`no_event_once_decided`, `decision_admitted`) |
| `work_close_by_opener`, `work_close_final` | the core's, inherited |

### `examples/solochangecontrol`

Software changes on one person's repository, on the core directly. The opener creates a change and decides it; the
revision fields are `url` text (`validUrl`: a scheme, `://`, no whitespace or control character, at most 2048
characters), compared as strings. What a URL points at, and whether a pushed revision descends from the branch it was
handed, is the harness's check, not the proof's.

| command | event | rules |
|---|---|---|
| `change.create {stream_id, change_id, from_revision_url, meta?}` | `change.created` | `only_opener_can_create`, `change_id_must_be_new` |
| `change.branch {stream_id, change_id, developer_id, branch_revision_url, meta?}` | `change.branched` | `change_must_exist`, `revisions_must_be_unique`, `only_opener_can_branch`, `developer_must_not_be_the_opener`, `developer_is_branched_once`, `developer_must_not_be_a_reviewer`, `change_must_not_be_pulled`, `change_must_be_undecided` |
| `change.push {stream_id, change_id, pushed_revision_url, meta?}` | `change.pushed` | `change_must_exist`, `revisions_must_be_unique`, `change_must_not_be_pulled`, `only_branched_developers_can_push`, `change_must_be_undecided` |
| `change.pull {stream_id, change_id, meta?}` | `change.pulled` | `change_must_exist`, `only_opener_can_pull`, `change_is_pulled_once`, `change_must_be_undecided` |
| `change.review {stream_id, change_id, reviewed_revision_url, screen_url, meta?}` | `change.reviewed` | `change_must_exist`, `revisions_must_be_unique`, `reviewer_must_not_be_a_developer`, `reviewer_must_not_be_the_opener`, `change_must_be_undecided` |
| `change.merge {stream_id, change_id, merged_revision_url, meta?}` | `change.merged` | `change_must_exist`, `revisions_must_be_unique`, `only_opener_can_decide`, `change_is_decided_once` |
| `change.abandon {stream_id, change_id, meta?}` | `change.abandoned` | `change_must_exist`, `only_opener_can_decide`, `change_is_decided_once` |

A change is decided when it is merged or abandoned. The pull cuts off branches and pushes and is a prerequisite of
nothing: the opener may merge or abandon, and a reviewer may review, with or without it. Review is optional and
repeatable, by anyone who is neither a developer of the change nor the opener, and a reviewer is never afterwards
branched. Every revision named on a change (its starting revision, each branch revision, every pushed, reviewed and
merged revision) is unique on that change, so each role leaves its own revision. Commands are intent: `merged` is
final whether or not the merge in git succeeds, and a continuation is a fresh change. The theorems are named as the
sentence each proves.

| theorem | statement |
|---|---|
| `every_change_is_created_by_the_opener`, `every_branch_is_by_the_opener`, `the_pull_is_by_the_opener`, `the_merge_is_by_the_opener`, `the_abandon_is_by_the_opener` | the opener creates, branches, pulls and decides |
| `every_push_is_by_a_branched_developer` | every push is by a developer the opener branched |
| `roles_are_disjoint` (`no_developer_is_the_opener`, `no_developer_is_a_reviewer`, `no_reviewer_is_the_opener`) | a developer of a change is neither the opener nor ever a reviewer of it, in either order; a reviewer is not the opener |
| `revisions_are_distinct` (`the_merged_revision_is_none_of_the_others`, `no_reviewed_revision_is_a_developers`, `no_pushed_revision_is_the_branch_revision`) | no two events of a change name the same revision |
| `a_change_is_created_once`, `every_event_names_a_created_change`, `a_developer_is_branched_once`, `a_change_is_pulled_once`, `a_change_is_decided_once` | each step once, and on a created change |
| `nothing_is_branched_or_pushed_after_the_pull` | after the pull, no branch or push of the change is accepted |
| `nothing_follows_a_decision` | after a change is merged or abandoned, no change event about it is accepted (`no_event_once_decided`, `decision_admitted`) |
| `the_creator_can_always_merge` | a theorem of acceptance (`Service.respond_accepted_iff`, `Layer.ValidX.snoc_inr_iff`): after any valid log in which the stream is open with opener `a`, the change exists and is undecided, and the revision is not yet named on it, the service accepts `a`'s merge, whatever else has or has not happened |
| `only_the_opener_closes_the_stream`, `nothing_follows_a_close` | the core's, inherited |

### The tower (`tests/tower`)

Reviews on tasks on the core, a layer on a layer:

| command | event | rules |
|---|---|---|
| `review.approve {stream_id, task_id, meta?}` | `review.approved {task_id}` | `only_opener_can_approve`, `task_must_be_completed`, `task_is_approved_once` |
| `stream.close` (a guard, after the core's rules) | | `completed_tasks_must_be_approved_before_close` |

| theorem | statement |
|---|---|
| `approved_by_opener` | every approval is by the stream's opener |
| `approved_completed`, `approved_completed_by_assignee` | only a completed task is approved, completed by its assignee, whom the opener named (the tasks layer's theorem, one level down) |
| `close_after_reviews` | at every close, every completed task of the stream is approved: the guard reaching the core two levels down |
| `tower_close_by_opener`, `tower_tasks_opened_by_opener`, `tower_parent_is_earlier_task`, `approve_admitted`, `tower_close_final` | the core's and the tasks layer's theorems, and the core's admission, at the top |

## Revisions and reads

The revision a stream names never changes (`proof_revision_fixed`, `proof_revision_unique`,
`Layer.ValidX.proof_revision_unique`), and the host serves each stream only with the engine built from that commit
and package (gap_engine_is_revision). Who reads a stream is not modelled: no proof says who reads, and the host
restricts no read (gap_read_visibility).

## Not proved

`docs/tcb.md` tables every gap; each is stated in full at the end of `Theorems.lean`.
