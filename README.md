# Provenstream

**Event-sourced streams whose rules are proved.** You write the rules of a stream (which commands exist, who may
issue each, and when) in Lean 4 and prove what they guarantee. Lean compiles those same functions into an engine, and
a generic host runs many streams, each judged forever by the engine of the proof revision it named when it was opened.
MIT license. The site is [provenstream.eloquentanalytics.com](https://provenstream.eloquentanalytics.com), with
[the work proof walked through](https://provenstream.eloquentanalytics.com/proofs/work/) for a reader who has never
opened a proof assistant.

## Why it matters

Most systems that record who did what keep their rules in application code. Nobody outside can check that the code
enforces what the documentation says, and the rules can change under the history they govern. That matters most where
several parties act on one record, and more so now that some of those parties are software agents: you want to know,
not hope, that an agent could not have done what only a person may do.

Provenstream makes three things checkable by anyone:

1. **What the rules guarantee.** Each guarantee is a theorem about every valid log, re-checked by Lean's kernel. For
   example: only the stream's opener ever closes it (`close_by_opener`), its opener never changes (`opener_fixed`),
   nothing follows a close (`close_final`).
2. **That the code which decides is the code that was proved.** The engine runs the proved functions, compiled by the
   Lean compiler. There is no second implementation to drift from the proof.
3. **That a stream's history is what its proof allows.** A stream names its proof revision (a commit and a package
   path) when it is opened, and that never changes (`proof_revision_fixed`). Anyone can rebuild the engine from that
   commit and replay the stream: every stored command must be accepted again and give exactly its stored event.

What is *not* proved is listed, not hidden: see [What is trusted](#what-is-trusted).

## How it works

A **stream** is an event-sourced log. Callers send **commands**; the engine checks each one against the stream's
history with its **rules** (guards, in Event-B terms). An accepted command becomes exactly one **event**, appended to
the log; a refused command changes nothing (`refused_keeps_log`) and the answer names the rule that refused it. A
**valid log** is one built only this way, and every **theorem** is an invariant of valid logs: a safety property
("nothing bad ever happens") that holds after every accepted event.

**Principals** are the identities that issue commands. To the host a principal is an id and its tokens, nothing
more: it authenticates callers with bearer tokens and records no kind, role or account. Every command carries the
caller's `actor_id` (the host fills it in from the token, and refuses one that is not the token's principal:
`actor_id_must_match_the_token`), so the engine always sees who acts. The core knows one principal per stream, its
**opener**; who else may act, and in what role (a person, an agent, an admin), is what a layer's own events say.

### The core

Every stream has two commands, and every proof builds on them:

| command | params | event | effect |
|---|---|---|---|
| `stream.open` | `proof_revision_url`, `meta`? (`stream_id` minted by the host) | `stream.opened {event, stream_id, actor_id, meta, proof_revision_url}` | opens a stream and names its proof revision; the caller is its opener |
| `stream.close` | `stream_id`, `meta`? | `stream.closed {event, stream_id, actor_id, meta}` | closes the stream for good; nothing is appended after it |

Events are named in the past tense, every id ends in `_id`, and every event, the core's and every layer's, carries
`event`, `stream_id`, `actor_id` and `meta`.

Its one rule about people is that **only the opener can close a stream**, a theorem (`close_by_opener`) every layer
inherits: a layer can only refuse more, so no layer can ever let anyone else close a stream. The core's rules, in
order (the first that fails is the reason):

| rule | refuses |
|---|---|
| `stream_id_must_be_new` | an open whose minted id names a stream already opened |
| `revision_url_must_name_a_commit` | an open whose URL is not a repository URL and a full commit |
| `stream_must_exist` | a close of a stream never opened |
| `stream_must_be_open` | a close of a closed stream |
| `only_opener_can_close` | a close by anyone but the stream's opener |

Before any rule, a command must come with as many minted ids as its schema says (`fresh_ids_must_match_the_command`;
only a broken host sees it).

The core holds only what no layer can add itself: a stream's identity, its proof revision, its opener and its end. It
has no declarations, no roles and no person or agent distinction, and no kinds anywhere: not in the core, not in the
schema, not in the host. What it gives
every layer is a stream's `View`, and one check, made of every layer event before the layer's own rules:

```lean
structure View where          -- the facts of a stream's past, as every layer's rules see them
  opened : Bool
  closed : Bool
  opener : Option Id           -- none until opened; fixed once set (opener_fixed)

def View.admits (v : View) (_a : Id) : Option String :=     -- asked of every layer event, before its rules
  if !v.opened then some "stream_must_exist"
  else if v.closed then some "stream_must_be_open"
  else none
```

The core admits any actor on an open stream, and leaves each layer to say who may act. "Only the opener may act"
cannot be a core rule: since a layer can only refuse more, it would mean no layer could ever let anyone else act,
delegate or be assigned anything. Instead the opener is where every permission starts, and a layer's rules read
`v.opener`.

### Every refusal names the rule broken

A rule is named for what it requires, not for what went wrong, so a refusal reads as the rule the caller broke:

```
provenstream: refused: only_opener_can_close
```

This holds for every reason a caller sees, the host's included: a child task whose parent is no task of its stream is
refused `parent_task_must_exist`, an open naming a revision the host does not serve `revision_must_be_installed`, a
repository other than the engine's `repository_must_match_the_engine`, an engine that does not answer as the core does
`engine_must_implement_the_interface`, a reused idempotency key with different params
`idempotency_key_must_match_its_request`, an `actor_id` other than the caller's `actor_id_must_match_the_token`, and a
read of a stream never opened `stream_must_exist`. There is no fixed grammar for these names: `only_opener_can_close`
and `stream_must_be_open` are examples of the style, not a pattern every layer must follow.

### Layers: refinement by superposition

A **layer** adds its own commands, events and rules to the core, for example tasks that the opener assigns and
assignees complete. Layers are a **refinement** of the core in the standard sense, of the specific kind called
**superposition**:

- **Core events are kept unchanged.** A layer cannot alter or reinterpret them.
- **Layer events are stuttering steps** for the core: they change nothing the core can see (Event-B: new events
  refine `skip`; `bases_snoc_inr`).
- **Guard strengthening only.** A layer can refuse more of the core's commands, never accept more
  (`ValidX.base_refusal_stands`).
- **Projection.** Drop a layer's events from any valid log and what remains is a valid core log (`ValidX.base`). This
  projection is a refinement mapping in Abadi and Lamport's sense.

So every core theorem holds in every layer, proved once in the core rather than once per layer: in every layer every
close is by the opener (`ValidX.close_by_opener`), the opener never changes (`ValidX.opener_fixed`), nothing follows a
close (`ValidX.close_final`), and every layer event is on an open, unclosed stream (`ValidX.admitted`). Layers stack
into **towers**, and the projection works level by level. Only safety theorems carry over this way: a layer may
refuse everything, so nothing about progress (liveness) is inherited, and none is claimed.

A field ending in `_id` is an id: a canonical UUID (kind `uuid`), or one that may be absent or `null` (`uuid?`, as
the tasks layer's `parent_task_id`, the parent's own `task_id`). A text field may be optional the same way: its kind
ends in `?` (`eml?`, as the email layer's `in_reply_to_url`), and the value is the text, or absent or `null`.
For the rarer field that names an earlier event by
its position, the core also has a kind **`ref`**: it checks every reference before a layer's rules run
(`ref_must_name_an_earlier_event`) and proves it points backwards (`ValidX.ref_earlier`) to an event that never
changes (`ref_target_fixed`), so references cannot form cycles. No example uses it.

The examples, from smallest up (all served from one commit, each by its package path):

| proof | commands, and their events | who may send them | what it proves |
|---|---|---|---|
| `examples/log` | `log.append {stream_id, text, meta?}` → `log.appended {text}` | the opener (`only_opener_can_append`) | every append is by the opener (`append_by_opener`): a notebook only its opener writes in |
| `examples/principals` | `principal.invite`, `principal.promote`, `principal.summon` `{stream_id, principal_id, meta?}` → `principal.invited`, `principal.promoted`, `principal.summoned {principal_id}` | an admin; the opener is the first admin, implicitly | admins are the opener and promoted invitees (persons, as this layer's events say), agents are summoned and never promoted, every declaration is made once and is permanent |
| `examples/tasks` | `task.open {stream_id, task_id, parent_task_id?, meta?}`, `task.assign {stream_id, task_id, assignee_id, meta?}`, `task.complete {stream_id, task_id, meta?}` → `task.opened`, `task.assigned`, `task.completed` | the opener opens and assigns; the assignee completes | every task was opened by the opener (`tasks_opened_by_opener`), every assignee was named by the opener (`assignees_named_by_opener`), a task is completed only by its assignee (`completed_by_assignee`) |
| `examples/work` | `work.create {stream_id, work_id, meta?}`, `work.assign {stream_id, work_id, assignee_id, meta?}`, `work.ask {stream_id, work_id, preparer_id, meta?}`, `work.reply {stream_id, work_id, meta?}`, `work.complete`, `work.cancel {stream_id, work_id, meta?}` → `work.created`, `work.assigned`, `work.asked`, `work.replied`, `work.completed`, `work.cancelled` | the opener creates and assigns; the assignee asks and decides; the asked reply | a basic task system: nobody creates or assigns work but the opener (`created_by_opener`, `assigned_by_opener`), only the assignee asks for preparations and decides (`asked_by_assignee`, `completed_by_assignee`, `cancelled_by_assignee`), only the asked reply (`replied_by_asked_preparer`), and nothing about an item follows its decision (`decision_final`) |
| `examples/solochangecontrol` | `change.create {stream_id, change_id, from_revision_url, meta?}`, `change.branch {stream_id, change_id, developer_id, branch_revision_url, meta?}`, `change.push {stream_id, change_id, pushed_revision_url, meta?}`, `change.pull {stream_id, change_id, meta?}`, `change.review {stream_id, change_id, reviewed_revision_url, screen_url, meta?}`, `change.merge {stream_id, change_id, merged_revision_url, meta?}`, `change.abandon {stream_id, change_id, meta?}` → `change.created`, `change.branched`, `change.pushed`, `change.pulled`, `change.reviewed`, `change.merged`, `change.abandoned` | the opener creates, branches, pulls and decides; the branched developers push; anyone else reviews | software changes on one person's repository: the opener hands developers other than itself a branch (`every_branch_is_by_the_opener`), who push (`every_push_is_by_a_branched_developer`); the pull cuts off incoming work (`nothing_is_branched_or_pushed_after_the_pull`); a developer is never a reviewer nor the opener (`roles_are_disjoint`); no revision is named twice on a change (`revisions_are_distinct`); the opener's merge of an undecided change is always accepted (`the_creator_can_always_merge`); nothing about a change follows its decision (`nothing_follows_a_decision`) |
| `examples/email` | `email.create {stream_id, email_id, in_reply_to_url?, meta?}`, `email.solicit {stream_id, email_id, drafter_id, meta?}`, `email.draft {stream_id, email_id, draft_url, meta?}`, `email.compose {stream_id, email_id, composed_url, screen_url, meta?}`, `email.send {stream_id, email_id, sent_url, meta?}`, `email.discard {stream_id, email_id, meta?}` → `email.created`, `email.solicited`, `email.drafted`, `email.composed`, `email.sent`, `email.discarded` | the opener creates, solicits and decides; the solicited drafters draft; anyone else composes | outgoing email one person sends: every field naming a message must end in `.eml`; the opener solicits drafters other than itself (`every_solicitation_is_by_the_opener`), who draft (`every_draft_is_by_a_solicited_drafter`); the first composed draft ends drafting (`nothing_is_solicited_or_drafted_after_the_compose`); a drafter is never a composer nor the opener (`roles_are_disjoint`); no `.eml` is named twice on an email (`emls_are_distinct`); the opener's send of an undecided email is always accepted (`the_creator_can_always_send`); nothing about an email follows its decision (`nothing_follows_a_decision`) |
| `examples/emailtriage` | `triage.create {stream_id, triage_id, message_url, meta?}`, `triage.ask {stream_id, triage_id, adviser_id, meta?}`, `triage.advise {stream_id, triage_id, verdict, meta?}`, `triage.review {stream_id, triage_id, verdict, meta?}`, `triage.reply {stream_id, triage_id, email_id, meta?}`, `triage.ignore {stream_id, triage_id, meta?}` → `triage.created`, `triage.asked`, `triage.advised`, `triage.reviewed`, `triage.replied`, `triage.ignored` | the opener creates, asks and decides; the asked advisers advise; anyone else reviews | what to do with a message that arrived: a verdict is exactly `reply` or `ignore`; the opener asks advisers other than itself (`every_ask_is_by_the_opener`), who advise once (`every_advice_is_by_an_asked_adviser`, `an_adviser_advises_once`); the first review ends asking and advising (`nothing_is_asked_or_advised_after_the_review`); an adviser is never a reviewer nor the opener (`roles_are_disjoint`); the opener's ignore of an undecided triage is always accepted (`the_creator_can_always_ignore`); nothing about a triage follows its decision (`nothing_follows_a_decision`) |
| `examples/email-triage-and-reply` | `principal.invite`, `principal.summon` `{stream_id, principal_id, meta?}`, `principal.delegate {stream_id, delegate_id, meta?}`; `email.create`, `email.solicit`, `email.prepare`, `email.draft`, `email.send`, `email.discard`; `triage.request`, `triage.ask`, `triage.advise`, `triage.consider`, `triage.reply`, `triage.work`, `triage.ignore`, `triage.defer` → one event each | the opener and its delegates; solicited preparers prepare; asked advisers advise | one person's mail on one stream: the opener owns every item; persons and agents are declared once; a person delegates its own authority, once per delegate, for the stream's life (`each_delegate_has_one_delegator`); a delegate of the owner acts for it, never through a chain (`no_act_rests_on_a_chain`); the terminal commands need a person (`no_agent_makes_a_terminal_decision`); a preparer never drafts and an adviser never considers (`roles_are_disjoint`); a reply names an email of the stream that answers no other triage (`an_email_answers_one_triage`) |
| `tests/tower` | `review.approve {stream_id, task_id, meta?}` → `review.approved`, on tasks | the opener | a review layer on the tasks layer; its guard refuses `stream.close` while a completed task awaits its review, a guard reaching two levels down |

`examples/log` is one command and one rule in about ten lines of Lean, the first proof to read. `examples/principals`
is the familiar roles, as a layer: `principal.invite` declares a person, `principal.promote` makes an invited person
an admin, `principal.summon` declares an agent, each naming an existing principal. Its rules are
`only_admins_can_invite`, `only_admins_can_promote`, `only_admins_can_summon`, `principal_must_be_new` (on invite and
summon: not yet invited or summoned, and not the opener), `principal_must_be_invited` and
`principal_is_promoted_once`. That an admin is a person is this layer's theorem about its own events
(`admins_are_persons`); nothing proves the opener a person, which is decided where tokens are issued. A stream of
it has five commands, the core's two and its own three.

The tasks layer sits on the core directly, not on principals. Its rules are `only_opener_can_open_tasks`,
`task_id_must_be_new` and `parent_task_must_exist` for `task.open` (`parent_task_id`, when given, is the parent's
own `task_id`, a task opened earlier on the same stream: `parent_is_earlier_task`, so no task is its own parent,
`parent_ne_self`); `only_opener_can_assign`, `task_must_exist` and `task_is_assigned_once` for `task.assign`,
to any principal, once; `task_must_exist`, `only_assignee_can_finish` (an unassigned task too) and
`task_is_completed_once` for `task.complete`. The tower's are `only_opener_can_approve`, `task_must_be_completed` and
`task_is_approved_once`, and its guard on the core's close is `completed_tasks_must_be_approved_before_close`. Since
the tasks layer's permissions rest on `v.opener`, "nobody creates work but the opener" and "nobody assigns but the
opener" are theorems of the layer, inherited by every layer on top of it.

The work layer (`examples/work`) is a basic task system on the core directly: the opener creates an item (`work.create`:
`only_opener_can_create`, `work_id_must_be_new`) and assigns it, to any principal, itself included (`work.assign`:
`only_opener_can_assign`, `work_must_exist`, `work_is_assigned_once`); the assignee asks any number of other
principals to prepare it (`work.ask`: `work_must_exist`, `only_assignee_can_ask`, `work_must_be_undecided`,
`preparer_must_not_be_the_assignee`, `preparer_is_asked_once`); each asked preparer replies once, its preparation in
`meta` (`work.reply`: `work_must_exist`, `only_asked_preparers_can_reply`, `work_must_be_undecided`,
`preparer_replies_once`); and the assignee completes or cancels the item, once, whether or not anyone replied
(`work.complete`, `work.cancel`: `work_must_exist`, `only_assignee_can_decide`, `work_is_decided_once`). Its headline
theorem is `decision_final`: once an item is completed or cancelled, no work event about it is accepted. Who may read
a reply is not the proof's business: the host restricts no read, so an application that wants preparers to work
independently keeps the replies from each other itself.

### Running streams

The engine is a native process that reads one JSON request per line and answers with the event or the refusal. It
describes itself (`--describe`): for every command its params and their types, the ids the host mints, a sentence
saying who may send it, its event and that event's fields, and the names of the rules that can refuse it, with the
protocol (`"protocol": 2`).
That the described params are exactly what it decodes is proved (`requestFromJ_schema`). The host therefore needs no
code for any particular proof. It:

- authenticates callers, fills in each command's `actor_id`, mints ids, and issues principals (`principal.create`);
- runs one engine per proof revision (a commit and a package path), started on demand and stopped when idle;
- appends with **optimistic concurrency** (compare-and-set at the expected length; that this refines the proved
  semantics under any interleaving is `cas_refines_run`) and honours **idempotency keys**, so a retry is not recorded
  twice;
- keeps a per-stream **hash chain** with **salted commitments** to each event's free-text `meta`, and returns the
  chain head with every accepted command. If you keep a head, any later change to the history before it is
  detectable. The commitment lets `meta` be erased while the chain still verifies.

**Reading is the host's business, and it restricts nothing.** No proof says who reads: any authenticated principal can
read any stream (`stream.events`, `stream.head`, `stream.get`, ...). There are no accounts and no kinds. Whoever runs
a host holds its database, and so every stream, anyway; keep what must stay private out of `meta`, or erase it.

`provenstream verify` rebuilds a stream's engine from its own commit and package, recomputes the hash chain, and
replays every row. Each built engine comes with a **provenance manifest** recording the commit, source tree, toolchain
and engine hash.

### The command line reads a proof's description

A stream's commands are its proof's, so the command line knows only the core's two by heart. For any other, it uses
the revision's **description**, never a build: before it sends a command to a stream (or with `--proof`), it checks
the method and params against the description and answers `method_not_found` or `invalid_params` itself (exit 5),
sending nothing. The rules stay the host's. The description comes from a local engine's `--describe` when one is
given, else from the host's `revision.describe`, cached by commit under `~/.provenstream/proofs`. With no description
to be had, the command fails with a clear message and a non-zero exit; it never falls back to compiling Lean.

`provenstream -h --proof <proof>` prints the same description as stable Markdown, for people and for agents: every
command with who may send it, its params, its event and fields, how to call it, the possible answers and the rule
names. `<proof>` is a full revision URL, 7 or more hex digits of a revision the host serves (with `/<package>` for a
package other than the repository's root, as in `4f1c2a9/examples/tasks`), or the path of an engine or of a build
directory with its `PROVENANCE.json`. A revision URL names a commit and a package: `<repo>/commit/<commit>` for the
root package, `<repo>/tree/<commit>/<package>` for another. No stream or proof command compiles; only `engine build`
and `engine check` do, for proof authors and hosts, and `conform` when it is given no engines.

## What is trusted

Every proof is checked by Lean's kernel. The verified path uses no `sorry` and no axiom beyond Lean's standard
`propext`, `Quot.sound` and `Classical.choice`, and no `partial`, `unsafe`, `extern`, `implemented_by` or
`native_decide`; the checks enforce this.

The guarantees still rest on parts that are not proved. This is the **trusted computing base**, listed item by item
in [`docs/tcb.md`](docs/tcb.md) and in `Provenstream/Theorems.lean`. In short:

- **The Lean compiler and runtime.** Compilation is trusted, not verified (`gap_compiled_engine`), and so is the JSON
  edge between host and engine (`gap_wire_bytes`, `gap_unproved_edge`).
- **The host.** It authenticates the caller and fills in `actor_id` from the token (`gap_token_is_caller`), computes
  the hash chain, and runs the engine built from the stream's revision (`gap_engine_is_revision`). It attests nothing
  else: there are no kinds to attest.
- **Storage.** Postgres or SQLite keeps what it reports appended and does compare-and-set (`gap_storage_durability`,
  `gap_store_compare_and_set`).
- **Who may read what.** Not modelled, and not restricted (`gap_read_visibility`): every authenticated principal reads
  every stream, and whoever runs the host holds the database.

The hash chain is tamper-evident only relative to heads someone kept. It does not stop an operator from rewriting a
whole chain nobody holds a head for; signed receipts and published heads are planned.

## Glossary

| term | meaning here |
|---|---|
| event-sourced stream | state is the append-only list of events; current state is rebuilt by replaying it |
| command | a request to change a stream: accepted, it becomes one event; refused, nothing changes |
| event | a recorded fact: an accepted command, with its actor |
| rule (guard) | a check against the stream's history that decides whether a command is accepted, named for what it requires |
| valid log | a log built only by accepting commands that passed every rule |
| theorem (invariant) | a statement proved true of every valid log |
| safety property | "nothing bad ever happens"; every guarantee here is of this kind |
| principal | an identity that issues commands: to the host, an id and its tokens; a person or an agent only where a layer's events say so |
| opener | the principal that opened a stream: the only one who can close it, and where a layer's permissions start |
| description | what an engine says of itself: its commands, params, events and rule names |
| refinement | a layer is a stricter version of its base: everything it records, the base allows |
| superposition | a layer adds its own events and rules without changing the base's |
| guard strengthening | a layer can refuse more, never accept more |
| projection (refinement mapping) | remove a layer's events from a valid log and a valid base log remains |
| stuttering step | a layer event that changes nothing the base can see |
| tower | layers stacked on layers |
| kernel-checked proof | a proof re-checked by Lean's small trusted kernel |
| trusted computing base | what the guarantees depend on but do not prove ([`docs/tcb.md`](docs/tcb.md)) |
| optimistic concurrency | an append succeeds only if the stream still has the length the decision was made at |
| idempotency key | a key that makes retrying a command safe: it is not recorded twice |
| hash chain | each row's hash covers the row before it; a kept head detects later changes to earlier rows |
| salted commitment | a hash of `meta` with a random salt: binds the value without revealing it |
| replay | rebuilding or re-checking a stream by passing its rows through the engine again |
| provenance manifest | the record of which commit, tree and toolchain built an engine |

## Quick start

### Use the command line

There is no hosted service. The command line talks to the local host unless told otherwise: `http://127.0.0.1:8080`,
where `provenstream serve` listens by default (`DEFAULT_BASE_URL`, `host/provenstream/client.py`). A remote host is
named with `--base-url`, `PROVENSTREAM_BASE_URL` or a configured `default_host`. `provenstream login` reads your token
from stdin (on a
terminal, a prompt that does not echo it; never an argument), checks it with the host's `whoami`, and keeps it for
that host: in the system keychain with the keyring extra (`pip install './host[keyring]'`), else in
`~/.provenstream/credentials.json`, readable by you only. Every remote command then sends it, and only to that host;
it is never printed. `PROVENSTREAM_TOKEN` and `--token-file` still work and win over a stored token, for CI and
scripts.

The help shows the core's two commands, and says where the rest come from:

```
$ provenstream -h
usage: provenstream [-h [--proof PROOF]] [--version] [--base-url URL] [--token-file FILE] [--principal P]
                    [--db DB] [--as PRINCIPAL] [--engines DIR] COMMAND ...

A stream is a proof. Every stream has the core's two commands:

  stream open [PROOF_URL] [--meta TEXT] [--alias NAME] [--no-use] [--from-git]
      open a stream judged by the proof at PROOF_URL (a revision URL, or 7+ hex digits of a revision the
      host serves); you are its opener, and it becomes the current stream
  stream close STREAM (--yes | --confirm STREAM) [--meta TEXT] [--dry-run]
      close STREAM for good; only its opener can (only_opener_can_close). On a terminal it asks you to type
      the stream's alias or id; elsewhere it needs --yes, or --confirm STREAM naming the same stream (exit 2)

  provenstream stream open https://example.org/provenstream/commit/<commit> --alias ledger
  provenstream stream close ledger --yes

The rest of the command line:
  stream events|head|verify|use|alias   read any stream; the current stream and aliases
  revision list|describe                the proof revisions a host serves
  api METHOD [JSON] [-f KEY=VALUE]      any method, checked against the stream's proof before it is sent
  principal create                      a new principal and its token (saved, never printed)
  auth login|logout|status|rotate       tokens, stored per host (login, logout, whoami)
  config get|set|unset|list             settings without secrets
  host serve|replay|export|import|principal create|token rotate    run a host, on its database
  engine init|check|build|install|describe                         proof projects and engines
  status, conform, help

Exit codes: 0 done, 1 a check failed, 2 usage, 3 unauthorized, 4 refused (the rule is printed),
5 method not found or invalid params, 6 unavailable, 7 needs local mode, 8 mode misconfigured.

A stream's other commands come from its proof: provenstream -h --proof <proof> shows them.
```

A stream's own commands, as Markdown an agent can read (here the principals layer's, shortened):

````
$ provenstream -h --proof 4f1c2a9/examples/principals
# Proof 4f1c2a9/examples/principals

- repository: https://example.org/provenstream
- commit: 4f1c2a9e7b03d6185a2c4e90f7d1b38c6a5e2f04
- package: examples/principals
- revision URL: https://example.org/provenstream/tree/4f1c2a9e7b03d6185a2c4e90f7d1b38c6a5e2f04/examples/principals
- protocol: 2
- commands: stream.open, stream.close, principal.invite, principal.promote, principal.summon

Every command also takes `actor_id` (optional: the caller, filled in from the token; any other is refused
actor_id_must_match_the_token) and `idempotency_key` (optional: 1 to 200 chars; a retry with the same key answers
the first answer).

## stream.open

...

## principal.promote

Who may send it: an admin: the stream's opener, or a principal promoted in the stream.

| param | type | required | notes |
|---|---|---|---|
| stream_id | uuid | required | |
| principal_id | uuid | required | |
| meta | meta | optional | opaque text, at most 4096 bytes; committed to by the chain, erasable |

Minted by the host: none.

Event `principal.promoted`: `{event, stream_id, actor_id, meta, principal_id}`

Call it:

```sh
provenstream api principal.promote -f stream_id=<stream> -f principal_id=<principal>
```

Rules, in order: stream_must_exist, stream_must_be_open, only_admins_can_promote, principal_must_be_invited,
principal_is_promoted_once.

## principal.summon

...

## Answers

| answer | exit | what |
|---|---|---|
| accepted | 0 | `{seq, event, chain}`: the event's position, the event, the chain head after it |
| refused | 4 | `refused: <rule>`: one of the rules below; nothing stored |
| method_not_found | 5 | not a command of this proof; checked before sending |
| invalid_params | 5 | params not as above; checked before sending |

## Rules

| rule | commands |
|---|---|
| stream_id_must_be_new | stream.open |
| revision_url_must_name_a_commit | stream.open |
| stream_must_exist | every command but stream.open |
...
| principal_is_promoted_once | principal.promote |
````

A session on a host that serves the tasks layer, as the opener and then as an agent the opener assigns (the agent's
token stored with `provenstream principal create --save-as agent`):

```
$ provenstream login                              # paste the token; logged in to <host> as 3f9c1e72-...
$ provenstream principal create --save-as agent   # a principal for the agent; its token stored for the host
8e21d4b0-6f3a-4c97-b852-1d0e9a7c5f34
$ S=$(provenstream stream open \
      https://example.org/provenstream/tree/4f1c2a9e7b03d6185a2c4e90f7d1b38c6a5e2f04/examples/tasks \
      --alias ledger -q event.stream_id)          # the new stream's id; now the current stream
$ echo $S
019a3b4e-7c21-7d4a-9f02-5e8b1c6d3a90
$ provenstream api task.open -f stream_id=$S -f task_id=7a4c2e19-0d5b-4f83-a6e1-93c0b8d2f457
{
  "chain": "b1e04f7c9a3d62e58f0c71a4d9b26e3f8c5a01d7e4b9f62c3a8d50e1f7b4c926",
  "event": {
    "actor_id": "3f9c1e72-4b8d-4a06-9e15-c27d80b4f613",
    "event": "task.opened",
    "meta": null,
    "parent_task_id": null,
    "stream_id": "019a3b4e-7c21-7d4a-9f02-5e8b1c6d3a90",
    "task_id": "7a4c2e19-0d5b-4f83-a6e1-93c0b8d2f457"
  },
  "seq": 1
}
$ provenstream api task.open -f stream_id=$S -f task_id=c05d9a3e-2b17-4e68-8f40-6a1d7e9b3c52 \
      -f parent_task_id=7a4c2e19-0d5b-4f83-a6e1-93c0b8d2f457 -q seq      # a child: its parent's task_id
2
$ provenstream api task.assign -f stream_id=$S -f task_id=7a4c2e19-0d5b-4f83-a6e1-93c0b8d2f457 \
      -f assignee_id=8e21d4b0-6f3a-4c97-b852-1d0e9a7c5f34 -q seq
3
$ provenstream api task.complete -f stream_id=$S -f task_id=7a4c2e19-0d5b-4f83-a6e1-93c0b8d2f457 \
      --principal agent -q event.event              # as the assignee
task.completed
$ provenstream api stream.panic -f stream_id=$S
provenstream: method not found: stream.panic is not a command of 4f1c2a9/examples/tasks (its description; nothing sent)
$ echo $?
5
$ provenstream stream close ledger --yes --principal agent
provenstream: refused: only_opener_can_close
$ echo $?
4
$ provenstream stream close ledger --yes -q seq   # as the opener
5
```

`stream close --dry-run` reports whether a close would be accepted and sends nothing. The rest of the stream tree:

```sh
provenstream whoami                                 # which principal, which token source, and the host's whoami
provenstream revision list                          # the proof revisions the host serves
provenstream revision describe 4f1c2a9/examples/tasks   # a revision's description, as JSON
provenstream stream events                          # the current stream's events, each with its seq and chain head
provenstream stream head -q chain                   # keep this head
provenstream stream use <another stream>            # switch: a UUID, an alias, or its last 8+ hex digits
provenstream stream verify ledger --repo . --head <seq>:<chain>   # rebuild the engine from its revision, replay
```

**New principals.** `provenstream principal create` asks the host (`principal.create`) for a new principal, as any
signed-in principal: it prints only the new `principal_id`, and its token goes to `--token-file PATH` (created 0600,
never over an existing file) or, in remote mode, is stored for the host under `--save-as NAME` (in the keychain with
the keyring extra, else `~/.provenstream/credentials.json`; then `--principal NAME` sends it). One of the two is
required (exit 2 without): the token is never printed. In local mode it acts `--as` a principal the store knows. The
first principal of a new host comes from its operator, `provenstream host principal create --token-file FILE` (local
mode, no token; it prints `{principal_id}`).

**The current stream.** `stream open` makes the stream it opens the current one (`--no-use` not to), and `head`,
`events` and `verify` act on it when no stream is named, saying which on a terminal. It is kept in the nearest
`.provenstream/client.json` above the current directory, a project file holding `host`, `proof_revision_url`, `stream`
and `aliases` and no secret, so it is safe to commit; outside a project, in `~/.provenstream/config.json` (`stream use
--project` starts a project file here). A flag wins over `PROVENSTREAM_STREAM`, which wins over the project file,
which wins over the config. A project's `host` is a default like `config default_host`, below `--base-url` and
`PROVENSTREAM_BASE_URL`. A stream argument is a UUID, an alias (`stream alias NAME STREAM`, or `stream open --alias
NAME`), or the last 8 or more hex digits of a stream known here; never its first digits, since a UUIDv7 begins with its
timestamp.

**Opening from a checkout.** With no PROOF_URL, `stream open` uses the configured `proof_revision_url`, else, in a
git repository with a `provenstream.json`, `<origin as https>/commit/<HEAD>`: refused when tracked files have changes
or when HEAD is on no remote branch, since a host builds the engine from a commit it can fetch. 7 or more hex digits
name a revision the host serves. `--from-git` derives the URL even when one is configured.

**Closing** is final, so `close` never acts on the current stream implicitly, and asks: on a terminal it shows the
stream's id, alias, proof URL and opener and closes only when you type the alias, the full id or its last 8
characters. Elsewhere it needs `--yes` or `--confirm STREAM` (exit 2 without either), and `--dry-run` reports whether
a close would be accepted and sends nothing.

**A layer's commands** go through `api METHOD`, its params as JSON and `-f key=value` (the value as JSON when it
parses, else as a string). Before sending, `api` checks the method and params against the stream's proof, as above.
Every command that prints JSON takes `-q PATH`, one value of it (`events.0.seq`; strings bare). The commands form a
tree; the flat verbs from before it still work, unchanged but for close's confirmation:

| command | flat alias | does |
|---|---|---|
| `stream open\|close\|head\|events\|verify` | `open`, `close`, `head`, `events`, `verify` | a stream's life and reads |
| `stream use`, `stream alias` | | the current stream, names for streams |
| `revision list\|describe` | `revisions` | the proof revisions served |
| `api METHOD`, `status` | `call`, `mode` | any method; the resolved mode and token |
| `principal create` | | a new principal; its token to a file or stored for the host, never printed |
| `auth login\|logout\|status\|rotate` | `login`, `logout`, `whoami` | stored tokens |
| `host serve\|replay\|export\|import\|principal create\|token rotate` | `serve`, `replay`, ... | run a host, on its database |
| `engine init\|check\|build\|install\|describe` | `init`, `check`, ... | proof projects and engines |

Exit codes: 0 done, 1 a check failed or a confirmation did not match, 2 usage, 3 unauthorized, 4 refused (the rule is
printed), 5 method not found or invalid params (the command line's own check against the proof, or the host's; an
unknown or ambiguous stream argument too), 6 unavailable (and no description of the proof to be had), 7 the command
needs local mode, 8 the mode is misconfigured. 3 to 6 are the host's answer table (`host/provenstream/protocol.py`),
the same whichever way a call travels; an unavailable answer names an incident in the host's log instead of the
failure. `events` pages through a long stream itself (`stream.events` answers at most 1000 events, with `next`).
`provenstream status` says which mode a command would run in, what decided it, where it would go and which token it
would send; `provenstream help` lists every command with its alias and mode.

Several principals can be stored for one host (you, and the agents you run): the last one logged in is the host's
active principal, and `--principal P` (its id, or the name `principal create --save-as` gave it) picks another for one
command. `provenstream auth rotate` asks the host for a new token and saves it where the old one was before it reports
anything. `provenstream logout` forgets a stored token, which stays valid on the host until it is rotated. Settings
without secrets live in `~/.provenstream/config.json` (`provenstream config set default_host URL`, `config list` for
every setting and where its value came from); flags win over the environment, the environment over a project file, and
that over the config file.

### Run a host in five minutes

Everything on one machine: no database server (streams go to the SQLite file `~/.provenstream/streams.db`) and no
remote host. You need Python 3.9+ and Lean via elan, to build the engine.

```sh
pip install ./host                                   # from a checkout of https://github.com/eloquentsh/provenstream.git
export PROVENSTREAM_ENGINES=$PWD/engines
provenstream engine build --repo . --commit "$(git rev-parse HEAD)" --out build/core   # the core's engine: prints its proof_url
provenstream engine install build/core
provenstream host principal create --token-file me.token   # the operator's: prints {principal_id}; the token to the file
provenstream host serve --port 8080 &                # POST /rpc, GET /healthz
provenstream login --base-url http://127.0.0.1:8080 --default --token-file me.token
provenstream stream open <the proof_url build printed>   # {seq, event: {stream_id, ...}, chain}; the current stream
provenstream stream events
provenstream stream head
```

The same host works without a server. In process (Python), an embedder holds the database and so acts as the operator,
for any principal it names; `host.handle(message, auth)` takes a JSON-RPC request as it is, and `command` and `query`
are its shorthands:

```python
from provenstream.host import Host, Operator

host = Host.open("streams.db", "engines")              # the store (a path ending .db), and the engines directory above
me = host.command("principal.create", auth=Operator(None))["principal_id"]
s = host.command("stream.open", auth=Operator(me), proof_revision_url=PROOF_URL)["event"]["stream_id"]
print(host.query("stream.events", auth=Operator(me), stream_id=s)["events"])
host.close()
```

From any other language, over stdin and stdout: one JSON-RPC request per line in, one answer per line out, in order,
as one principal for the whole session (`--as PRINCIPAL`, or `--token-file FILE` for a token):

```sh
printf '%s\n' '{"jsonrpc":"2.0","id":1,"method":"whoami"}' | provenstream serve --stdio --as <principal>
```

Every carrier answers a message with the same bytes. Every method, param, result and error is in
[HOST-PROTOCOL.md](HOST-PROTOCOL.md), generated from the code; a host also describes itself as an OpenRPC document
(`provenstream api rpc.discover`).

### Use your own host

Every command runs in one of two modes, decided once per invocation:

1. `PROVENSTREAM_MODE`, if set (`remote` or `local`);
2. otherwise **local** if `--db` is given or `PROVENSTREAM_DATABASE_URL` is set;
3. otherwise **local** for a command that only works locally when no host is named (`--base-url`,
   `PROVENSTREAM_BASE_URL`), with the default database;
4. otherwise **remote**.

`DATABASE_URL` and `PGHOST` and the other `PG*` variables never choose the mode, and neither does the configured
`default_host`. **Remote** commands go to `--base-url` (or `PROVENSTREAM_BASE_URL`, else `default_host`, else the
local host) as the principal of the token: `--token-file`, else `PROVENSTREAM_TOKEN`, else the one
`provenstream login` stored for that host.
**Local** commands use the database directly, in process, with the engines of `--engines` (or
`PROVENSTREAM_ENGINES`), through the same service and compare-and-set append as `serve`, so they are safe beside a
running host. Mixing the two (a base URL in local mode, `--as` in remote mode, `--principal` or `auth` in local mode,
`--db` with `PROVENSTREAM_MODE=remote`) is an error, never ignored.

| commands | remote | local |
|---|---|---|
| `open`, `close`, `call`, `principal create` (and their `stream ...` and `api` forms) | JSON-RPC as the token's principal | in process, as `--as PRINCIPAL` |
| `events`, `head` | read through the host | in process; no `--as` needed, reads are unrestricted |
| `verify` | read through the host | read the database (`verify --rows FILE` works in both) |
| `revisions` | the host's | the engines directory's `revisions.json` |
| `serve` (or `serve --stdio`), `host principal create`, `token rotate`, `replay`, `export`, `import` | an error when a host is named: they need a database (exit 7); with nothing named, the default database | as usual |
| `auth login`, `logout`, `status`, `rotate` (and `login`, `logout`, `whoami`) | the host's tokens, stored for it | an error (exit 8): local mode needs no token |
| `init`, `check`, `build`, `describe`, `install`, `config`, `help` | files only, in both modes | files only |

Local mode is operator access: `--as` acts as any principal the store knows, without a token, which anyone with
access to the database could do anyway. The proofs still decide every write. In local mode the proof check reads the
description from the engines directory's engine for the stream's revision.

A whole session in local mode, on a throwaway SQLite file, with no network:

```
$ export PROVENSTREAM_ENGINES=$PWD/engines DB=$PWD/demo.db
$ me=$(provenstream host principal create --db $DB --token-file me.token -q principal_id)   # the operator's
$ other=$(provenstream principal create --db $DB --as $me --token-file other.token)         # prints the id only
$ S=$(provenstream stream open https://example.org/provenstream/commit/4f1c2a9e7b03d6185a2c4e90f7d1b38c6a5e2f04 \
      --db $DB --as $me -q event.stream_id)
$ provenstream api stream.panic -f stream_id=$S --db $DB --as $me
provenstream: method not found: stream.panic is not a command of 4f1c2a9 (its description; nothing sent)
$ echo $?
5
$ provenstream stream close $S --yes --db $DB --as $other
provenstream: refused: only_opener_can_close
$ echo $?
4
$ provenstream stream close $S --yes --db $DB --as $me
{
  "chain": "6d2f8a0c4e91b7d35a0e6c2f9b48d17e3c5a90f2b6e14d8c7a3f05e9d2b1c684",
  "event": {
    "actor_id": "3f9c1e72-4b8d-4a06-9e15-c27d80b4f613",
    "event": "stream.closed",
    "meta": null,
    "stream_id": "019a3b4e-7c21-7d4a-9f02-5e8b1c6d3a90"
  },
  "seq": 1
}
```

A host keeps its streams in a database and creates its tables on first start. With none named it is the SQLite file
`~/.provenstream/streams.db` (directory created 0700), so `provenstream serve` needs no database server. `--db` or
`PROVENSTREAM_DATABASE_URL` names another: `sqlite:///abs/path.db` or a path ending `.db`, or Postgres for several
hosts on one database (`pip install './host[postgres]'`) in either connection-string form, `postgresql://...` or
`host=... dbname=...`; `postgresql://` alone uses libpq's own settings (`PGHOST`, `~/.pgpass`, ...), as `psql` does.
`provenstream export FILE` and `provenstream import FILE` move streams between stores, every chain checked on import.
Tokens are not moved: issue each principal a token again for its own id, `provenstream host principal create --id
<principal> --token-file FILE`.

```sh
pip install ./host                    # or bin/provenstream from the checkout; needs Lean via elan, Python 3.9+
export PROVENSTREAM_ENGINES=engines   # streams go to ~/.provenstream/streams.db (or --db / PROVENSTREAM_DATABASE_URL)
provenstream engine build --repo . --commit "$(git rev-parse HEAD)" --package examples/tasks --out build/tasks
provenstream engine install build/tasks
provenstream engine describe build/tasks/engine     # what the engine says of itself: commands, events, rule names
provenstream host principal create --token-file me.token   # prints {principal_id}; the token to the file
provenstream host serve --port 8080
# from here on, remote: through the host, with a token
provenstream login --base-url http://127.0.0.1:8080 --default --token-file me.token
provenstream -h --proof build/tasks                 # the tasks layer's commands, from its build directory
provenstream stream open <repository URL>/tree/<commit>/examples/tasks   # a stream judged by the tasks layer
provenstream api task.open -f stream_id=<stream> -f task_id=<uuid>                       # a layer command: through api
provenstream api task.open -f stream_id=<stream> -f task_id=<uuid> -f parent_task_id=<the parent's task_id>  # a child
provenstream stream verify <stream> --repo .        # builds the stream's own package (here examples/tasks), replays
```

The engine built above is the `examples/tasks` layer on the core, so its streams have the core's two commands plus
`task.open`, `task.assign` and `task.complete`. A revision is a commit and a package path, so each proof of one commit
(the core, every example, the tower) is a revision of its own, served side by side: `engine install` puts each engine in
`engines/<commit>/<package or _root>/`, listed in `engines/revisions.json` under its revision (`<commit>` for the root
package, `<commit>/<package>` for another).

With Docker instead: `docker/build-engine.sh . HEAD examples/tasks`, then
`docker compose -f docker/docker-compose.yml up`.

### Check the proofs

```sh
scripts/check.sh          # build, axioms, forbidden words, audit, self-tests, the examples, tower, corpus, negative proofs
scripts/test_host.sh      # the environment's tests and the conformance suite, against a throwaway Postgres
provenstream conform --compare --engines engines   # the conformance suite on every carrier, in parallel, on SQLite
provenstream conform --compare --engines engines --db "$(python3 scripts/pgtmp.py db DIR)"   # the same on Postgres
```

The revision module an engine is built from (`CoreRevision.lean`; each example's `<Name>Revision.lean`) is written by
`scripts/stamp_revision` before each build and is not in git: a commit cannot name its own hash. So a bare
`lake build` fails on a fresh clone; run `scripts/check.sh` or `provenstream engine build`, which stamp it first.
`scripts/test_host.sh` and `scripts/pgtmp.py` find the Postgres binaries in `PROVENSTREAM_PG_BIN`, else on `PATH`, else
in Homebrew's `/opt/homebrew/opt/postgresql@16/bin`; on Linux, set `PROVENSTREAM_PG_BIN` to your Postgres bin directory
(`/usr/lib/postgresql/16/bin` on Debian).

**The main suite is command sequences.** `conformance/` holds many sequences of commands, valid and invalid, across
the core, `examples/log`, `examples/principals`, `examples/tasks`, `examples/work` and the tower, each with its validated outcome:
every answer, refusal reason, event, seq and chain head. `provenstream conform` runs them on the three carriers (in
process, `serve --stdio` and `serve` over HTTP) in parallel, on SQLite and on Postgres, and with `--compare` checks
that every carrier answered with the same bytes: 8304 cases on each carrier, 8064 of them in 515 command sequences on
those proofs; `examples/solochangecontrol` has no sequences and no corpus session yet, so `conform` does not serve it.
`--db` names the store (a Postgres connection string, as `scripts/pgtmp.py` makes for a throwaway
cluster, or a SQLite path); the run adds streams and principals to it. Pytest (`host/tests/`) covers only the
environment: building, installing, the command line, configuration, the keyring and the interface check. A behaviour a
sequence can show is shown by a sequence.

A host of your own, in any language, is Provenstream-compatible when it passes the
[conformance suite](conformance/README.md): `provenstream conform --base-url URL --tokens FILE --revision-url URL` runs
it against a host at a URL, as four principals of it (`opener`, `other`, `third`, `outsider`, each a token file),
skipping the cases that need operator access.

An engine **implements the stream interface** when it answers the core's recorded sessions (`corpus/sessions/core-*`,
sealed by `corpus/SHA256SUMS`) as the core does; `engine build`, `engine install`, `engine check` and a host's
`stream.open` check it (`engine_must_implement_the_interface`). `tests/proof-negative/` holds variants of the tasks
layer that must fail to build: three weaken a rule (anyone opens, assigns or completes a task) and exactly the theorem
drawn from it fails (and one of the work layer: anyone asks, and `asked_by_assignee` fails; and two of the email triage and reply layer:
a reply may reuse an email, and `an_email_answers_one_triage` fails; an agent may send, and
`every_terminal_decision_is_by_the_owner_or_a_person_delegate` fails); one tries to let someone other than the opener close a stream, one to close it twice, and one
names a command `stream.close`. The check passes only if each fails exactly where it should.
`tests/not-the-interface/` holds proofs that build but do not inherit from the core's, among them `otherbase`, the
tasks layer on a copy of the core's base with `only_opener_can_close` removed: the source check finds each.

### Write a layer

```sh
provenstream engine init notes   # a Lake package on Provenstream.Interface: a layer, a theorem, examples, an engine
provenstream engine check notes
```

Start from `examples/log`: one command, one rule (`v.opener == some actor`) and its theorem.

## Layout

| path | what |
|---|---|
| `Provenstream/` | the core: its two commands, schemas, wire, generic service, layer mechanism, theorems, interface, engine edge |
| `examples/log/` | the smallest layer: `log.append`, by the opener only |
| `examples/principals/` | persons, admins and agents as a layer: `principal.invite`, `principal.promote`, `principal.summon` |
| `examples/tasks/` | tasks the opener opens and assigns and the assignee completes, with an optional `parent_task_id` |
| `examples/work/` | a basic task system: the opener creates and assigns an item, the assignee asks preparers, who reply, and completes or cancels it |
| `examples/solochangecontrol/` | software changes on one person's repository: the opener branches a change to developers, who push; reviewers publish a screen and their own revision; the pull cuts off incoming work; the opener merges or abandons; every revision named on a change is unique |
| `examples/email-triage-and-reply/` | one person's mail on one stream: triage and reply, persons and agents, delegation |
| `tests/tower/`, `tests/proof-negative/`, `tests/not-the-interface/` | reviews on tasks, a layer on a layer; proofs that must fail to build; proofs that must fail the source check |
| `corpus/` | recorded engine sessions, replayed byte for byte; the stream interface |
| `conformance/` | the main suite: command sequences and their outcomes, on any carrier or a host at a URL |
| `host/` | the Python host and the `provenstream` command line |
| `docs/` | [model](docs/model.md), [refinement](docs/refinement.md), [trusted computing base](docs/tcb.md), [hosting](docs/hosting.md), [security](docs/security.md), [remote builds](docs/phase2.md), [economics](docs/economics.md); the engine's line protocol is [PROTOCOL.md](PROTOCOL.md), the host's interface [HOST-PROTOCOL.md](HOST-PROTOCOL.md) (generated) |

## Related work

Provenstream's layers are a narrow form of the refinement used in **Event-B** (Abrial, *Modeling in Event-B*, 2010)
and in superposition refinement (Katz, 1993; Back and Sere, 1996): guard strengthening, new events refining `skip`,
and a projection that is a refinement mapping (Abadi and Lamport, 1991). **LeanMachines** (Peschanski, iFM 2024)
brings broader Event-B-style refinement to Lean 4, including data refinement and convergence proofs, checked per
model. Provenstream's narrower form lets the refinement be proved once, in core Lean without Mathlib, and compiled
into a running engine. Its log model is **event sourcing** in the usual sense (Fowler, 2005).

## License

MIT. See [LICENSE](LICENSE). "The Provenstream authors" are the contributors recorded in the repository's history.

Provenstream's own code is MIT. A built engine also contains the Lean 4 runtime and standard library (Apache-2.0), GMP
(LGPL-3.0), mimalloc and libuv (MIT): see [THIRD_PARTY_NOTICES](THIRD_PARTY_NOTICES), which travels with every engine
and in the host image. The host's optional Postgres driver, psycopg, is LGPL-3.0; importing it does not change the
host's license.
