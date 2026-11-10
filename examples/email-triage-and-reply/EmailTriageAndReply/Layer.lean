-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Provenstream.Interface

/-!
# Email triage and reply: a layer on the core

One person's mail on one stream. The opener records each message that arrives as a triage and decides it. The opener
also creates the emails it sends and decides them. The opener declares the principals who help, as persons or as
agents, and delegates its authority to them. The layer grows from two proofs, `examples/email` and
`examples/emailtriage`. Their composers and reviewers are gone here, and the delegate takes both places. The old
drafter is the preparer.

The principal commands:

- `principal.invite {stream_id, principal_id, meta?}` → `principal.invited`: declares a person.
- `principal.summon {stream_id, principal_id, meta?}` → `principal.summoned`: declares an agent.
- `principal.delegate {stream_id, delegate_id, meta?}` → `principal.delegated`: a person (the opener or an invited
  principal) delegates its own authority to a declared principal.

The email commands:

- `email.create {stream_id, email_id, in_reply_to_eml_url?, meta?}` → `email.created`
- `email.solicit {stream_id, email_id, preparer_id, meta?}` → `email.solicited`
- `email.prepare {stream_id, email_id, preparation_url, meta?}` → `email.prepared`
- `email.draft {stream_id, email_id, draft_eml_url, screen_url, meta?}` → `email.drafted`
- `email.send {stream_id, email_id, sent_eml_url, meta?}` → `email.sent`
- `email.discard {stream_id, email_id, meta?}` → `email.discarded`

The triage commands:

- `triage.request {stream_id, triage_id, message_eml_url, meta?}` → `triage.requested`
- `triage.ask {stream_id, triage_id, adviser_id, meta?}` → `triage.asked`
- `triage.advise {stream_id, triage_id, verdict, meta?}` → `triage.advised`
- `triage.consider {stream_id, triage_id, verdict, meta?}` → `triage.considered`
- `triage.reply {stream_id, triage_id, email_id, meta?}` → `triage.replied`
- `triage.work {stream_id, triage_id, work_id, meta?}` → `triage.worked`
- `triage.ignore {stream_id, triage_id, meta?}` → `triage.ignored`
- `triage.defer {stream_id, triage_id, meta?}` → `triage.deferred`

A principal is declared once, as a person or an agent, and never the opener (`principal_must_be_new`). The opener
counts as a person. A delegation lasts for the stream's life. Each delegate has one delegator
(`delegate_must_be_new`), so a delegate always acts on one principal's behalf. A delegate acts with its delegator's
own authority, never with authority it holds as someone else's delegate.

The owner of every email and every triage is the opener. Creating and requesting need the opener's authority, so a
delegate creates for the opener. The owner or a delegate of the owner creates, requests, invites, summons, solicits,
asks, drafts and considers. The terminal commands need a person: `email.send`, `email.discard`, `triage.reply`,
`triage.work`, `triage.ignore` and `triage.defer`. The owner makes them, or a delegate of the owner who was invited.
An agent delegate never does. A solicited preparer prepares, and an asked adviser advises once. A preparer or an
adviser is declared, and is neither the owner nor the one who solicits or asks it.

The roles never meet on one item. A preparer of an email never drafts it, and a drafter is never solicited on it. An
adviser of a triage never considers it, and a considerer is never asked on it. Soliciting, preparing, asking and
advising go on until the decision. A deferral closes the triage as the other decisions do. Coming back to the message
later is a new triage.

A field ending in `_eml_url` is an `eml` field (`validEml`): a URL ending in `.eml`. The `.eml` URLs named on one email
are unique on it (`eml_urls_must_be_unique`). `preparation_url` and `screen_url` are `url` fields, outside that check.
A verdict is exactly `reply`, `work`, `ignore` or `defer`. A `triage.reply` names an email created on this stream that
no earlier reply names (`reply_must_name_an_unclaimed_email`).

The memory is one list of notes `(what, item, value)`, in order. The principal events make `invited`, `summoned` and
`delegate` (delegator, delegate). The email events make `email`, `reply_to`, `preparer`, `preparation`, `drafter`,
`draft`, `sent` and `discarded`. The triage events make `triage`, `adviser`, `advice`, `verdict`, `considerer`,
`consideration`, `replied`, `worked`, `ignored` and `deferred`.
-/

namespace EmailTriageAndReply
open Provenstream Provenstream.Layer Provenstream.Wire

/-- A URL: a scheme, `://` and something after it; no whitespace or control character; at most 2048 characters. -/
def validUrl (s : String) : Bool :=
  s.length ≤ 2048 && s.all (fun (c : Char) => 32 < c.val && c.val != 127) &&
  match s.splitOn "://" with
  | [scheme, rest] => !scheme.isEmpty && !rest.isEmpty
  | _ => false

/-- The URL of an `.eml`: a URL whose last four characters are `.eml`. It is spelled on the character list, so the
compiled form reaches no primitive the audit does not trust. -/
def endsWithEml (s : String) : Bool :=
  match s.toList.reverse with
  | 'l' :: 'm' :: 'e' :: '.' :: _ => true
  | _ => false

def validEml (s : String) : Bool := validUrl s && endsWithEml s

/-- A verdict: exactly `reply`, `work`, `ignore` or `defer`. -/
def validVerdict (s : String) : Bool := s == "reply" || s == "work" || s == "ignore" || s == "defer"

/-- The kind of a preparation or screen field. -/
def urlKind : Kind := .text "url" validUrl

/-- The kind of an `_eml_url` field. -/
def emlKind : Kind := .text "eml" validEml

/-- The kind of an optional `_eml_url` field (`eml?`): an `.eml` URL, or absent or `null`. -/
def emlOptKind : Kind := .textOpt "eml" validEml

/-- The kind of a verdict field. -/
def verdictKind : Kind := .text "verdict" validVerdict

inductive PrincipalCommand where
  | invite (stream principal : Id) («meta» : Meta)
  | summon (stream principal : Id) («meta» : Meta)
  | delegate (stream delegate : Id) («meta» : Meta)
  deriving DecidableEq

inductive EmailCommand where
  | create (stream email : Id) (replyTo : Option String) («meta» : Meta)
  | solicit (stream email preparer : Id) («meta» : Meta)
  | prepare (stream email : Id) (preparation : String) («meta» : Meta)
  | draft (stream email : Id) (draft screen : String) («meta» : Meta)
  | send (stream email : Id) (sent : String) («meta» : Meta)
  | discard (stream email : Id) («meta» : Meta)
  deriving DecidableEq

inductive TriageCommand where
  | request (stream triage : Id) (message : String) («meta» : Meta)
  | ask (stream triage adviser : Id) («meta» : Meta)
  | advise (stream triage : Id) (verdict : String) («meta» : Meta)
  | consider (stream triage : Id) (verdict : String) («meta» : Meta)
  | reply (stream triage email : Id) («meta» : Meta)
  | work (stream triage item : Id) («meta» : Meta)
  | ignore (stream triage : Id) («meta» : Meta)
  | defer (stream triage : Id) («meta» : Meta)
  deriving DecidableEq

/-- A command of the layer: a delegation, an email command or a triage command. -/
inductive MailCommand where
  | principal (c : PrincipalCommand)
  | email (c : EmailCommand)
  | triage (c : TriageCommand)
  deriving DecidableEq

inductive PrincipalEvent where
  | invited (actor stream principal : Id) («meta» : Meta)
  | summoned (actor stream principal : Id) («meta» : Meta)
  | delegated (actor stream delegate : Id) («meta» : Meta)
  deriving DecidableEq

inductive EmailEvent where
  | created (actor stream email : Id) (replyTo : Option String) («meta» : Meta)
  | solicited (actor stream email preparer : Id) («meta» : Meta)
  | prepared (actor stream email : Id) (preparation : String) («meta» : Meta)
  | drafted (actor stream email : Id) (draft screen : String) («meta» : Meta)
  | sent (actor stream email : Id) (sent : String) («meta» : Meta)
  | discarded (actor stream email : Id) («meta» : Meta)
  deriving DecidableEq

inductive TriageEvent where
  | requested (actor stream triage : Id) (message : String) («meta» : Meta)
  | asked (actor stream triage adviser : Id) («meta» : Meta)
  | advised (actor stream triage : Id) (verdict : String) («meta» : Meta)
  | considered (actor stream triage : Id) (verdict : String) («meta» : Meta)
  | replied (actor stream triage email : Id) («meta» : Meta)
  | worked (actor stream triage item : Id) («meta» : Meta)
  | ignored (actor stream triage : Id) («meta» : Meta)
  | deferred (actor stream triage : Id) («meta» : Meta)
  deriving DecidableEq

/-- An event of the layer: a delegation, an email event or a triage event. -/
inductive MailEvent where
  | principal (e : PrincipalEvent)
  | email (e : EmailEvent)
  | triage (e : TriageEvent)
  deriving DecidableEq

/-- A note an event makes: what, the principal, email or triage, and whom or which (a principal, a URL, a verdict, an
email or work item id, or `""`). -/
abbrev Note := String × String × String

/-- The note an email's replied-to message makes: one when the email is a reply, none otherwise. -/
def replyNotes (k : String) : Option String → List Note
  | none => []
  | some u => [("reply_to", k, u)]

def principalNotes : PrincipalEvent → List Note
  | .invited _ _ p _ => [("invited", p, "")]
  | .summoned _ _ p _ => [("summoned", p, "")]
  | .delegated a _ d _ => [("delegate", a, d)]

def emailNotes : EmailEvent → List Note
  | .created a _ k r _ => ("email", k, a) :: replyNotes k r
  | .solicited _ _ k p _ => [("preparer", k, p)]
  | .prepared _ _ k u _ => [("preparation", k, u)]
  | .drafted a _ k u _ _ => [("drafter", k, a), ("draft", k, u)]
  | .sent _ _ k u _ => [("sent", k, u)]
  | .discarded _ _ k _ => [("discarded", k, "")]

def triageNotes : TriageEvent → List Note
  | .requested _ _ k u _ => [("triage", k, u)]
  | .asked _ _ k d _ => [("adviser", k, d)]
  | .advised a _ k v _ => [("advice", k, a), ("verdict", k, v)]
  | .considered a _ k v _ => [("considerer", k, a), ("consideration", k, v)]
  | .replied _ _ k e _ => [("replied", k, e)]
  | .worked _ _ k i _ => [("worked", k, i)]
  | .ignored _ _ k _ => [("ignored", k, "")]
  | .deferred _ _ k _ => [("deferred", k, "")]

def notes : MailEvent → List Note
  | .principal e => principalNotes e
  | .email e => emailNotes e
  | .triage e => triageNotes e

/-- The memory's step: the event's notes, appended. -/
def addNotes (st : List Note) (e : MailEvent) : List Note := st ++ notes e

/-- Some note says `what` of item `k`. -/
def noted (w : List Note) (what k : String) : Bool := w.any fun n => n.1 == what && n.2.1 == k

/-- `d` is a delegate of `o`: `o` delegated `d` on the stream. A delegation lasts for the stream's life. -/
def isDelegateOf (w : List Note) (o d : String) : Bool := w.contains ("delegate", o, d)

/-- `d` is a delegate of someone. -/
def hasDelegator (w : List Note) (d : String) : Bool := w.any fun n => n.1 == "delegate" && n.2.2 == d

/-- `a` is a person: the opener, or a principal invited on the stream. -/
def isPerson (opener : Option Id) (w : List Note) (a : String) : Bool := opener == some a || noted w "invited" a

/-- `p` is not yet declared on the stream (neither invited nor summoned), and is not its opener. -/
def isNew (opener : Option Id) (w : List Note) (p : String) : Bool :=
  !noted w "invited" p && !noted w "summoned" p && opener != some p

/-- `a` acts with the authority of `owner`: it is the owner, or a delegate of the owner. -/
def forOwner (owner : Option Id) (w : List Note) (a : String) : Bool :=
  owner == some a || owner.any fun o => isDelegateOf w o a

/-- `a` makes a terminal decision for `owner`: it is the owner, or a delegate of the owner who is a person. An agent
delegate does not. -/
def personForOwner (owner : Option Id) (w : List Note) (a : String) : Bool :=
  owner == some a || owner.any fun o => isDelegateOf w o a && noted w "invited" a

/-- The email `k` is decided: sent or discarded. -/
def emailDecided (w : List Note) (k : String) : Bool := noted w "sent" k || noted w "discarded" k

/-- The triage `k` is decided: replied, made a work item, ignored or deferred. -/
def triageDecided (w : List Note) (k : String) : Bool :=
  noted w "replied" k || noted w "worked" k || noted w "ignored" k || noted w "deferred" k

/-- A note of this kind names an `.eml` of its email. -/
def namesEml (what : String) : Bool := what == "reply_to" || what == "draft" || what == "sent"

/-- Some note names the `.eml` `u` of email `k`. -/
def emlNamed (w : List Note) (k u : String) : Bool :=
  w.any fun n => namesEml n.1 && n.2.1 == k && n.2.2 == u

/-- Some triage's reply names email `e`. -/
def replyClaimed (w : List Note) (e : String) : Bool := w.any fun n => n.1 == "replied" && n.2.2 == e

/-- The items some note says `what` of, in order. -/
def itemsOf (w : List Note) (what : String) : List String := w.filterMap fun n => if n.1 == what then some n.2.1 else none

/-- The item and the third slot of each note saying `what`, as `{<key>, <who>}`. -/
def pairsOf (w : List Note) (what key who : String) : J :=
  .arr (w.filterMap fun n => if n.1 == what then some (.obj [(key, .str n.2.1), (who, .str n.2.2)]) else none)

def notesToJ (st : List Note) : J := .arr (st.map fun (f, k, q) => .arr [.str f, .str k, .str q])

def notesFromJ : J → Except String (List Note)
  | .arr xs => xs.mapM fun
    | .arr [.str f, .str k, .str q] => .ok (f, k, q)
    | _ => .error "state: expected a note"
  | _ => .error "state: expected notes"

theorem notesFromJ_toJ (st : List Note) : notesFromJ (notesToJ st) = .ok st := by
  induction st with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨f, k, q⟩ := x
    simp only [notesToJ, notesFromJ, List.map_cons, List.mapM_cons] at ih ⊢
    simp [ih, bind, Except.bind, pure, Except.pure]

abbrev mailbox : Layer where
  Cmd := MailCommand
  Ev := MailEvent
  toRequest
    | .principal (.invited a t p m) => (a, .principal (.invite t p m))
    | .principal (.summoned a t p m) => (a, .principal (.summon t p m))
    | .principal (.delegated a t d m) => (a, .principal (.delegate t d m))
    | .email (.created a t k r m) => (a, .email (.create t k r m))
    | .email (.solicited a t k d m) => (a, .email (.solicit t k d m))
    | .email (.prepared a t k u m) => (a, .email (.prepare t k u m))
    | .email (.drafted a t k u s m) => (a, .email (.draft t k u s m))
    | .email (.sent a t k u m) => (a, .email (.send t k u m))
    | .email (.discarded a t k m) => (a, .email (.discard t k m))
    | .triage (.requested a t k u m) => (a, .triage (.request t k u m))
    | .triage (.asked a t k d m) => (a, .triage (.ask t k d m))
    | .triage (.advised a t k v m) => (a, .triage (.advise t k v m))
    | .triage (.considered a t k v m) => (a, .triage (.consider t k v m))
    | .triage (.replied a t k e m) => (a, .triage (.reply t k e m))
    | .triage (.worked a t k i m) => (a, .triage (.work t k i m))
    | .triage (.ignored a t k m) => (a, .triage (.ignore t k m))
    | .triage (.deferred a t k m) => (a, .triage (.defer t k m))
  ofRequest
    | (a, .principal (.invite t p m)) => .principal (.invited a t p m)
    | (a, .principal (.summon t p m)) => .principal (.summoned a t p m)
    | (a, .principal (.delegate t d m)) => .principal (.delegated a t d m)
    | (a, .email (.create t k r m)) => .email (.created a t k r m)
    | (a, .email (.solicit t k d m)) => .email (.solicited a t k d m)
    | (a, .email (.prepare t k u m)) => .email (.prepared a t k u m)
    | (a, .email (.draft t k u s m)) => .email (.drafted a t k u s m)
    | (a, .email (.send t k u m)) => .email (.sent a t k u m)
    | (a, .email (.discard t k m)) => .email (.discarded a t k m)
    | (a, .triage (.request t k u m)) => .triage (.requested a t k u m)
    | (a, .triage (.ask t k d m)) => .triage (.asked a t k d m)
    | (a, .triage (.advise t k v m)) => .triage (.advised a t k v m)
    | (a, .triage (.consider t k v m)) => .triage (.considered a t k v m)
    | (a, .triage (.reply t k e m)) => .triage (.replied a t k e m)
    | (a, .triage (.work t k i m)) => .triage (.worked a t k i m)
    | (a, .triage (.ignore t k m)) => .triage (.ignored a t k m)
    | (a, .triage (.defer t k m)) => .triage (.deferred a t k m)
  stream
    | .principal (.invite t ..) | .principal (.summon t ..) | .principal (.delegate t ..) => t
    | .email (.create t ..) | .email (.solicit t ..) | .email (.prepare t ..) | .email (.draft t ..)
    | .email (.send t ..) | .email (.discard t ..) => t
    | .triage (.request t ..) | .triage (.ask t ..) | .triage (.advise t ..) | .triage (.consider t ..)
    | .triage (.reply t ..) | .triage (.work t ..) | .triage (.ignore t ..) | .triage (.defer t ..) => t
  schema := [{ name := "principal.invite", event := "principal.invited",
               who := some "the stream's opener or a delegate of the opener",
               fields := [("stream_id", .uuid), ("principal_id", .uuid), ("meta", .metaOpt)] },
             { name := "principal.summon", event := "principal.summoned",
               who := some "the stream's opener or a delegate of the opener",
               fields := [("stream_id", .uuid), ("principal_id", .uuid), ("meta", .metaOpt)] },
             { name := "principal.delegate", event := "principal.delegated",
               who := some "a person (the opener or an invited principal), for itself",
               fields := [("stream_id", .uuid), ("delegate_id", .uuid), ("meta", .metaOpt)] },
             { name := "email.create", event := "email.created",
               who := some "the stream's opener or a delegate of the opener",
               fields := [("stream_id", .uuid), ("email_id", .uuid), ("in_reply_to_eml_url", emlOptKind),
                          ("meta", .metaOpt)] },
             { name := "email.solicit", event := "email.solicited", who := some "the owner (the opener) or a delegate of the owner",
               fields := [("stream_id", .uuid), ("email_id", .uuid), ("preparer_id", .uuid), ("meta", .metaOpt)] },
             { name := "email.prepare", event := "email.prepared", who := some "a preparer solicited on the email",
               fields := [("stream_id", .uuid), ("email_id", .uuid), ("preparation_url", urlKind), ("meta", .metaOpt)] },
             { name := "email.draft", event := "email.drafted",
               who := some "the owner (the opener) or a delegate of the owner, not a preparer of the email",
               fields := [("stream_id", .uuid), ("email_id", .uuid), ("draft_eml_url", emlKind),
                          ("screen_url", urlKind), ("meta", .metaOpt)] },
             { name := "email.send", event := "email.sent", who := some "the owner (the opener) or a delegate of the owner who is a person",
               fields := [("stream_id", .uuid), ("email_id", .uuid), ("sent_eml_url", emlKind), ("meta", .metaOpt)] },
             { name := "email.discard", event := "email.discarded", who := some "the owner (the opener) or a delegate of the owner who is a person",
               fields := [("stream_id", .uuid), ("email_id", .uuid), ("meta", .metaOpt)] },
             { name := "triage.request", event := "triage.requested",
               who := some "the stream's opener or a delegate of the opener",
               fields := [("stream_id", .uuid), ("triage_id", .uuid), ("message_eml_url", emlKind), ("meta", .metaOpt)] },
             { name := "triage.ask", event := "triage.asked", who := some "the owner (the opener) or a delegate of the owner",
               fields := [("stream_id", .uuid), ("triage_id", .uuid), ("adviser_id", .uuid), ("meta", .metaOpt)] },
             { name := "triage.advise", event := "triage.advised", who := some "an adviser asked on the triage",
               fields := [("stream_id", .uuid), ("triage_id", .uuid), ("verdict", verdictKind), ("meta", .metaOpt)] },
             { name := "triage.consider", event := "triage.considered",
               who := some "the owner (the opener) or a delegate of the owner, not an adviser of the triage",
               fields := [("stream_id", .uuid), ("triage_id", .uuid), ("verdict", verdictKind), ("meta", .metaOpt)] },
             { name := "triage.reply", event := "triage.replied", who := some "the owner (the opener) or a delegate of the owner who is a person",
               fields := [("stream_id", .uuid), ("triage_id", .uuid), ("email_id", .uuid), ("meta", .metaOpt)] },
             { name := "triage.work", event := "triage.worked", who := some "the owner (the opener) or a delegate of the owner who is a person",
               fields := [("stream_id", .uuid), ("triage_id", .uuid), ("work_id", .uuid), ("meta", .metaOpt)] },
             { name := "triage.ignore", event := "triage.ignored", who := some "the owner (the opener) or a delegate of the owner who is a person",
               fields := [("stream_id", .uuid), ("triage_id", .uuid), ("meta", .metaOpt)] },
             { name := "triage.defer", event := "triage.deferred", who := some "the owner (the opener) or a delegate of the owner who is a person",
               fields := [("stream_id", .uuid), ("triage_id", .uuid), ("meta", .metaOpt)] }]
  toVals
    | .principal (.invite t p m) => ("principal.invite", [.s t, .s p, .m m])
    | .principal (.summon t p m) => ("principal.summon", [.s t, .s p, .m m])
    | .principal (.delegate t d m) => ("principal.delegate", [.s t, .s d, .m m])
    | .email (.create t k r m) => ("email.create", [.s t, .s k, .uo r, .m m])
    | .email (.solicit t k d m) => ("email.solicit", [.s t, .s k, .s d, .m m])
    | .email (.prepare t k u m) => ("email.prepare", [.s t, .s k, .s u, .m m])
    | .email (.draft t k u s m) => ("email.draft", [.s t, .s k, .s u, .s s, .m m])
    | .email (.send t k u m) => ("email.send", [.s t, .s k, .s u, .m m])
    | .email (.discard t k m) => ("email.discard", [.s t, .s k, .m m])
    | .triage (.request t k u m) => ("triage.request", [.s t, .s k, .s u, .m m])
    | .triage (.ask t k d m) => ("triage.ask", [.s t, .s k, .s d, .m m])
    | .triage (.advise t k v m) => ("triage.advise", [.s t, .s k, .s v, .m m])
    | .triage (.consider t k v m) => ("triage.consider", [.s t, .s k, .s v, .m m])
    | .triage (.reply t k e m) => ("triage.reply", [.s t, .s k, .s e, .m m])
    | .triage (.work t k i m) => ("triage.work", [.s t, .s k, .s i, .m m])
    | .triage (.ignore t k m) => ("triage.ignore", [.s t, .s k, .m m])
    | .triage (.defer t k m) => ("triage.defer", [.s t, .s k, .m m])
  ofVals
    | "principal.invite", [.s t, .s p, .m m] => some (.principal (.invite t p m))
    | "principal.summon", [.s t, .s p, .m m] => some (.principal (.summon t p m))
    | "principal.delegate", [.s t, .s d, .m m] => some (.principal (.delegate t d m))
    | "email.create", [.s t, .s k, .uo r, .m m] => some (.email (.create t k r m))
    | "email.solicit", [.s t, .s k, .s d, .m m] => some (.email (.solicit t k d m))
    | "email.prepare", [.s t, .s k, .s u, .m m] => some (.email (.prepare t k u m))
    | "email.draft", [.s t, .s k, .s u, .s s, .m m] => some (.email (.draft t k u s m))
    | "email.send", [.s t, .s k, .s u, .m m] => some (.email (.send t k u m))
    | "email.discard", [.s t, .s k, .m m] => some (.email (.discard t k m))
    | "triage.request", [.s t, .s k, .s u, .m m] => some (.triage (.request t k u m))
    | "triage.ask", [.s t, .s k, .s d, .m m] => some (.triage (.ask t k d m))
    | "triage.advise", [.s t, .s k, .s v, .m m] => some (.triage (.advise t k v m))
    | "triage.consider", [.s t, .s k, .s v, .m m] => some (.triage (.consider t k v m))
    | "triage.reply", [.s t, .s k, .s e, .m m] => some (.triage (.reply t k e m))
    | "triage.work", [.s t, .s k, .s i, .m m] => some (.triage (.work t k i m))
    | "triage.ignore", [.s t, .s k, .m m] => some (.triage (.ignore t k m))
    | "triage.defer", [.s t, .s k, .m m] => some (.triage (.defer t k m))
    | _, _ => none
  ofRequest_toRequest := by intro x; cases x <;> rename_i e <;> cases e <;> rfl
  toRequest_ofRequest := by intro ⟨_, x⟩; cases x <;> rename_i c <;> cases c <;> rfl
  ofVals_toVals := by intro x; cases x <;> rename_i c <;> cases c <;> rfl
  toVals_name := by intro x; cases x <;> rename_i c <;> cases c <;> simp
  memory := foldMemory [] addNotes notesToJ notesFromJ notesFromJ_toJ
  readJ st := [("invited", .arr ((itemsOf st "invited").map .str)),
               ("summoned", .arr ((itemsOf st "summoned").map .str)),
               ("delegations", pairsOf st "delegate" "delegator_id" "delegate_id"),
               ("emails", .arr ((itemsOf st "email").map .str)),
               ("replies_to", pairsOf st "reply_to" "email_id" "in_reply_to_eml_url"),
               ("preparers", pairsOf st "preparer" "email_id" "preparer_id"),
               ("preparations", pairsOf st "preparation" "email_id" "preparation_url"),
               ("drafters", pairsOf st "drafter" "email_id" "drafter_id"),
               ("drafts", pairsOf st "draft" "email_id" "draft_eml_url"),
               ("sent", pairsOf st "sent" "email_id" "sent_eml_url"),
               ("discarded", .arr ((itemsOf st "discarded").map .str)),
               ("triages", pairsOf st "triage" "triage_id" "message_eml_url"),
               ("advisers", pairsOf st "adviser" "triage_id" "adviser_id"),
               ("advice", pairsOf st "advice" "triage_id" "adviser_id"),
               ("verdicts", pairsOf st "verdict" "triage_id" "verdict"),
               ("considerers", pairsOf st "considerer" "triage_id" "considerer_id"),
               ("considerations", pairsOf st "consideration" "triage_id" "verdict"),
               ("replied", pairsOf st "replied" "triage_id" "email_id"),
               ("worked", pairsOf st "worked" "triage_id" "work_id"),
               ("ignored", .arr ((itemsOf st "ignored").map .str)),
               ("deferred", .arr ((itemsOf st "deferred").map .str))]
  rules := [-- principals: persons and agents, and their delegations
            ⟨"only_opener_or_delegates_can_invite", ["principal.invite"], fun v w e => match e with
               | .principal (.invited a ..) => forOwner v.opener w a | _ => true⟩,
            ⟨"only_opener_or_delegates_can_summon", ["principal.summon"], fun v w e => match e with
               | .principal (.summoned a ..) => forOwner v.opener w a | _ => true⟩,
            ⟨"principal_must_be_new", ["principal.invite", "principal.summon"], fun v w e => match e with
               | .principal (.invited _ _ p _) | .principal (.summoned _ _ p _) => isNew v.opener w p | _ => true⟩,
            ⟨"only_persons_can_delegate", ["principal.delegate"], fun v w e => match e with
               | .principal (.delegated a ..) => isPerson v.opener w a | _ => true⟩,
            ⟨"delegate_must_be_declared", ["principal.delegate"], fun _ w e => match e with
               | .principal (.delegated _ _ d _) => noted w "invited" d || noted w "summoned" d | _ => true⟩,
            ⟨"delegate_must_not_be_the_delegator", ["principal.delegate"], fun _ _ e => match e with
               | .principal (.delegated a _ d _) => a != d | _ => true⟩,
            ⟨"delegate_must_be_new", ["principal.delegate"], fun _ w e => match e with
               | .principal (.delegated _ _ d _) => !hasDelegator w d | _ => true⟩,
            -- email; the owner is the opener
            ⟨"only_opener_or_delegates_can_create", ["email.create"], fun v w e => match e with
               | .email (.created a ..) => forOwner v.opener w a | _ => true⟩,
            ⟨"email_id_must_be_new", ["email.create"], fun _ w e => match e with
               | .email (.created _ _ k _ _) => !noted w "email" k | _ => true⟩,
            ⟨"email_must_exist", ["email.solicit", "email.prepare", "email.draft", "email.send", "email.discard"],
             fun _ w e => match e with
               | .email (.solicited _ _ k _ _) | .email (.prepared _ _ k _ _) | .email (.drafted _ _ k _ _ _)
               | .email (.sent _ _ k _ _) | .email (.discarded _ _ k _) => noted w "email" k
               | _ => true⟩,
            ⟨"eml_urls_must_be_unique", ["email.draft", "email.send"],
             fun _ w e => match e with
               | .email (.drafted _ _ k u _ _) | .email (.sent _ _ k u _) => !emlNamed w k u
               | _ => true⟩,
            ⟨"only_owner_or_delegates_can_solicit", ["email.solicit"], fun v w e => match e with
               | .email (.solicited a ..) => forOwner v.opener w a | _ => true⟩,
            ⟨"preparer_must_not_be_the_owner", ["email.solicit"], fun v _ e => match e with
               | .email (.solicited _ _ _ p _) => v.opener != some p | _ => true⟩,
            ⟨"preparer_must_be_declared", ["email.solicit"], fun _ w e => match e with
               | .email (.solicited _ _ _ p _) => noted w "invited" p || noted w "summoned" p | _ => true⟩,
            ⟨"preparer_must_not_be_the_soliciter", ["email.solicit"], fun _ _ e => match e with
               | .email (.solicited a _ _ p _) => a != p | _ => true⟩,
            ⟨"preparer_is_solicited_once", ["email.solicit"], fun _ w e => match e with
               | .email (.solicited _ _ k p _) => !w.contains ("preparer", k, p) | _ => true⟩,
            ⟨"preparer_must_not_be_a_drafter", ["email.solicit"], fun _ w e => match e with
               | .email (.solicited _ _ k p _) => !w.contains ("drafter", k, p) | _ => true⟩,
            ⟨"only_solicited_preparers_can_prepare", ["email.prepare"], fun _ w e => match e with
               | .email (.prepared a _ k _ _) => w.contains ("preparer", k, a) | _ => true⟩,
            ⟨"drafter_must_not_be_a_preparer", ["email.draft"], fun _ w e => match e with
               | .email (.drafted a _ k _ _ _) => !w.contains ("preparer", k, a) | _ => true⟩,
            ⟨"only_owner_or_delegates_can_draft", ["email.draft"], fun v w e => match e with
               | .email (.drafted a ..) => forOwner v.opener w a | _ => true⟩,
            ⟨"only_owner_or_person_delegates_can_decide", ["email.send", "email.discard"], fun v w e => match e with
               | .email (.sent a ..) | .email (.discarded a ..) => personForOwner v.opener w a | _ => true⟩,
            ⟨"email_is_decided_once", ["email.send", "email.discard"], fun _ w e => match e with
               | .email (.sent _ _ k _ _) | .email (.discarded _ _ k _) => !emailDecided w k | _ => true⟩,
            ⟨"email_must_be_undecided", ["email.solicit", "email.prepare", "email.draft"],
             fun _ w e => match e with
               | .email (.solicited _ _ k _ _) | .email (.prepared _ _ k _ _) | .email (.drafted _ _ k _ _ _) =>
                 !emailDecided w k
               | _ => true⟩,
            -- triage; the owner is the opener
            ⟨"only_opener_or_delegates_can_request", ["triage.request"], fun v w e => match e with
               | .triage (.requested a ..) => forOwner v.opener w a | _ => true⟩,
            ⟨"triage_id_must_be_new", ["triage.request"], fun _ w e => match e with
               | .triage (.requested _ _ k _ _) => !noted w "triage" k | _ => true⟩,
            ⟨"triage_must_exist", ["triage.ask", "triage.advise", "triage.consider", "triage.reply", "triage.work",
                                   "triage.ignore", "triage.defer"],
             fun _ w e => match e with
               | .triage (.asked _ _ k _ _) | .triage (.advised _ _ k _ _) | .triage (.considered _ _ k _ _)
               | .triage (.replied _ _ k _ _) | .triage (.worked _ _ k _ _) | .triage (.ignored _ _ k _)
               | .triage (.deferred _ _ k _) => noted w "triage" k
               | _ => true⟩,
            ⟨"only_owner_or_delegates_can_ask", ["triage.ask"], fun v w e => match e with
               | .triage (.asked a ..) => forOwner v.opener w a | _ => true⟩,
            ⟨"adviser_must_not_be_the_owner", ["triage.ask"], fun v _ e => match e with
               | .triage (.asked _ _ _ d _) => v.opener != some d | _ => true⟩,
            ⟨"adviser_must_be_declared", ["triage.ask"], fun _ w e => match e with
               | .triage (.asked _ _ _ d _) => noted w "invited" d || noted w "summoned" d | _ => true⟩,
            ⟨"adviser_must_not_be_the_asker", ["triage.ask"], fun _ _ e => match e with
               | .triage (.asked a _ _ d _) => a != d | _ => true⟩,
            ⟨"adviser_is_asked_once", ["triage.ask"], fun _ w e => match e with
               | .triage (.asked _ _ k d _) => !w.contains ("adviser", k, d) | _ => true⟩,
            ⟨"adviser_must_not_be_a_considerer", ["triage.ask"], fun _ w e => match e with
               | .triage (.asked _ _ k d _) => !w.contains ("considerer", k, d) | _ => true⟩,
            ⟨"only_asked_advisers_can_advise", ["triage.advise"], fun _ w e => match e with
               | .triage (.advised a _ k _ _) => w.contains ("adviser", k, a) | _ => true⟩,
            ⟨"adviser_advises_once", ["triage.advise"], fun _ w e => match e with
               | .triage (.advised a _ k _ _) => !w.contains ("advice", k, a) | _ => true⟩,
            ⟨"considerer_must_not_be_an_adviser", ["triage.consider"], fun _ w e => match e with
               | .triage (.considered a _ k _ _) => !w.contains ("adviser", k, a) | _ => true⟩,
            ⟨"only_owner_or_delegates_can_consider", ["triage.consider"], fun v w e => match e with
               | .triage (.considered a ..) => forOwner v.opener w a | _ => true⟩,
            ⟨"only_owner_or_person_delegates_can_decide", ["triage.reply", "triage.work", "triage.ignore",
                                                         "triage.defer"],
             fun v w e => match e with
               | .triage (.replied a ..) | .triage (.worked a ..) | .triage (.ignored a ..)
               | .triage (.deferred a ..) => personForOwner v.opener w a
               | _ => true⟩,
            ⟨"triage_is_decided_once", ["triage.reply", "triage.work", "triage.ignore", "triage.defer"],
             fun _ w e => match e with
               | .triage (.replied _ _ k _ _) | .triage (.worked _ _ k _ _) | .triage (.ignored _ _ k _)
               | .triage (.deferred _ _ k _) => !triageDecided w k
               | _ => true⟩,
            ⟨"triage_must_be_undecided", ["triage.ask", "triage.advise", "triage.consider"],
             fun _ w e => match e with
               | .triage (.asked _ _ k _ _) | .triage (.advised _ _ k _ _) | .triage (.considered _ _ k _ _) =>
                 !triageDecided w k
               | _ => true⟩,
            -- the reply's email
            ⟨"reply_must_name_an_unclaimed_email", ["triage.reply"], fun _ w e => match e with
               | .triage (.replied _ _ _ x _) => noted w "email" x && !replyClaimed w x | _ => true⟩]

end EmailTriageAndReply
