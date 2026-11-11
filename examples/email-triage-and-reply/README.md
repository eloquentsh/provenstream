# Email triage and reply

One person's mail on one stream. The opener records each message that arrives as a triage and decides it. The opener
also creates the emails it sends and decides them. Helpers are declared on the stream as persons or as agents. A
person can delegate its own authority to them.

The layer grows from two proofs, `examples/email` and `examples/emailtriage`. Those two stay as they are. Here the
composer and the reviewer are gone, and a delegate takes both places. The old drafter is now the preparer. The layer
is `EmailTriageAndReply.mailbox`, and its engine is `email-triage-and-reply-engine`.

## The model

The owner of every email and every triage is the stream's opener. Creating and requesting need the opener's
authority. So a delegate that creates an item creates it for the opener, and the opener owns it.

Principals come in two kinds. `principal.invite` declares a person, and `principal.summon` declares an agent. The
opener counts as a person and is never declared. A principal is declared once, as one kind.

A person delegates its own authority with `principal.delegate`. The delegate must be declared, must not be the person
itself, and must have no delegator yet. A delegation lasts for the stream's life. So each delegate has exactly one
delegator, and "on whose behalf" is never in doubt. A delegate acts with its delegator's own authority. It never passes
on authority it holds as someone else's delegate.

A delegate of the owner may do what the owner does, with one exception. The terminal commands need a person:
`email.send`, `email.discard`, `triage.reply`, `triage.work`, `triage.ignore` and `triage.defer`. An agent delegate
never makes them. An invited delegate may make them for the owner. A delegate of another principal gets nothing on
the owner's items.

The roles never meet on one item. A preparer of an email never drafts it, and a drafter is never solicited on it. An
adviser of a triage never considers it, and a considerer is never asked on it. A preparer or an adviser is declared,
and is neither the owner nor the principal who solicits or asks it.

Work goes on until the decision. Soliciting and preparing continue after a draft, and asking and advising continue
after a consideration. After a decision nothing more happens on the item. A deferral closes a triage as the other
decisions do. Coming back to the message later is a new `triage.request`.

A field ending in `_eml_url` is a URL ending in `.eml`. The `.eml` URLs named on one email are all different: the
message replied to, each draft and the sent message. `preparation_url` and `screen_url` are plain URLs, outside that
check. A verdict is exactly `reply`, `work`, `ignore` or `defer`.

A `triage.reply` names an `email_id`. The email must be created on this stream, and no earlier reply may name it. So a
reply begun on a triage is an email of the same stream, and each email answers at most one triage.

## The rules

Every layer command meets the core's admission first (`stream_must_exist`, `stream_must_be_open`). Then its rules run
in this order, and the first that refuses names the refusal.

| command | event | rules, in order |
|---|---|---|
| `principal.invite {stream_id, principal_id, meta?}` | `principal.invited` | `only_opener_or_delegates_can_invite`, `principal_must_be_new` |
| `principal.summon {stream_id, principal_id, meta?}` | `principal.summoned` | `only_opener_or_delegates_can_summon`, `principal_must_be_new` |
| `principal.delegate {stream_id, delegate_id, meta?}` | `principal.delegated` | `only_persons_can_delegate`, `delegate_must_be_declared`, `delegate_must_not_be_the_delegator`, `delegate_must_be_new` |
| `email.create {stream_id, email_id, in_reply_to_eml_url?, meta?}` | `email.created` | `only_opener_or_delegates_can_create`, `email_id_must_be_new` |
| `email.solicit {stream_id, email_id, preparer_id, meta?}` | `email.solicited` | `email_must_exist`, `only_owner_or_delegates_can_solicit`, `preparer_must_not_be_the_owner`, `preparer_must_be_declared`, `preparer_must_not_be_the_soliciter`, `preparer_is_solicited_once`, `preparer_must_not_be_a_drafter`, `email_must_be_undecided` |
| `email.prepare {stream_id, email_id, preparation_url, meta?}` | `email.prepared` | `email_must_exist`, `only_solicited_preparers_can_prepare`, `email_must_be_undecided` |
| `email.draft {stream_id, email_id, draft_eml_url, screen_url, meta?}` | `email.drafted` | `email_must_exist`, `eml_urls_must_be_unique`, `drafter_must_not_be_a_preparer`, `only_owner_or_delegates_can_draft`, `email_must_be_undecided` |
| `email.send {stream_id, email_id, sent_eml_url, meta?}` | `email.sent` | `email_must_exist`, `eml_urls_must_be_unique`, `only_owner_or_person_delegates_can_decide`, `email_is_decided_once` |
| `email.discard {stream_id, email_id, meta?}` | `email.discarded` | `email_must_exist`, `only_owner_or_person_delegates_can_decide`, `email_is_decided_once` |
| `triage.request {stream_id, triage_id, message_eml_url, meta?}` | `triage.requested` | `only_opener_or_delegates_can_request`, `triage_id_must_be_new` |
| `triage.ask {stream_id, triage_id, adviser_id, meta?}` | `triage.asked` | `triage_must_exist`, `only_owner_or_delegates_can_ask`, `adviser_must_not_be_the_owner`, `adviser_must_be_declared`, `adviser_must_not_be_the_asker`, `adviser_is_asked_once`, `adviser_must_not_be_a_considerer`, `triage_must_be_undecided` |
| `triage.advise {stream_id, triage_id, verdict, meta?}` | `triage.advised` | `triage_must_exist`, `only_asked_advisers_can_advise`, `adviser_advises_once`, `triage_must_be_undecided` |
| `triage.consider {stream_id, triage_id, verdict, meta?}` | `triage.considered` | `triage_must_exist`, `considerer_must_not_be_an_adviser`, `only_owner_or_delegates_can_consider`, `triage_must_be_undecided` |
| `triage.reply {stream_id, triage_id, email_id, meta?}` | `triage.replied` | `triage_must_exist`, `only_owner_or_person_delegates_can_decide`, `triage_is_decided_once`, `reply_must_name_an_unclaimed_email` |
| `triage.work {stream_id, triage_id, work_id, meta?}` | `triage.worked` | `triage_must_exist`, `only_owner_or_person_delegates_can_decide`, `triage_is_decided_once` |
| `triage.ignore {stream_id, triage_id, meta?}` | `triage.ignored` | `triage_must_exist`, `only_owner_or_person_delegates_can_decide`, `triage_is_decided_once` |
| `triage.defer {stream_id, triage_id, meta?}` | `triage.deferred` | `triage_must_exist`, `only_owner_or_person_delegates_can_decide`, `triage_is_decided_once` |

Every event carries its command's fields and `actor_id`. A read of a stream adds `invited`, `summoned`, `delegations`,
the email's keys and the triage's keys. The name `only_owner_or_person_delegates_can_decide` is one rule for the
email's decisions and another for the triage's. No command meets both.

## The theorems

`EmailTriageAndReply/Theorems.lean` proves the guarantees. It uses no `sorry` and no axiom beyond `propext`,
`Quot.sound` and `Classical.choice`. A few of them, by the sentence each names:

- `a_principal_is_declared_once`, `no_person_is_an_agent`, `the_opener_is_never_declared`
- `every_delegator_is_a_person`, `every_delegate_is_declared`, `each_delegate_has_one_delegator`
- `a_delegation_adds_exactly_its_pair`, `a_delegation_is_permanent`
- `every_act_is_by_the_owner_or_a_delegate`, `no_act_rests_on_a_chain`
- `every_terminal_decision_is_by_the_owner_or_a_person_delegate`, `no_agent_makes_a_terminal_decision`
- `Email.no_preparer_is_a_drafter`, `Triage.no_adviser_is_a_considerer`
- `Email.soliciting_goes_on_after_a_draft`, `Triage.asking_goes_on_after_a_consideration`
- `Triage.nothing_follows_a_deferral`, `Reply.an_email_answers_one_triage`
- `the_creator_can_always_send`, `the_creator_can_always_ignore`, `the_creator_can_always_defer`,
  `the_creator_can_always_reply`

The last four are theorems of acceptance. Each says that the owner, or a person delegate of the owner, gets the
command accepted from any state that meets the rules it reads.

## The story

`EmailTriageAndReply/Examples.lean` tells one stream's story, checked at build time and in the engine's self-test.
Every rule refuses something in it.

Ann opens the stream. She invites Cy and Fay as persons and summons Dee and Eve as agents. She delegates to Eve, an
agent, and to Fay, a person. Eve then declares Gus and Hal for Ann. Hal delegates to Gus, so Gus acts for Hal and gets
nothing on Ann's mail.

Ann creates an email in reply to an inbound message. Ann solicits Cy, Eve solicits Dee, and both prepare. Eve drafts,
and Ann drafts too. Fay is solicited after the drafts and prepares. Eve tries to send and is refused, because an agent
makes no terminal decision. Fay sends it for Ann.

Then a message arrives as a triage. Cy and Dee are asked, and Cy advises. Eve considers, and so does Ann. Fay is asked
after the consideration, and Dee and Fay advise. Eve creates an email in reply to the message, and Fay replies to the
triage with it. A second triage tries to reply with the same email and is refused. Ann defers it, and coming back to
that message is a new triage. Ann closes the stream at the end.

## The tests

`tests/` holds a Python model of the layer and three tests against the compiled engine. `tests/README.md` describes
them.

```sh
PYTHONPATH=host python3 -m pytest examples/email-triage-and-reply/tests -q
```
