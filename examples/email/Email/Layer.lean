-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Provenstream.Interface

/-!
# Email: a layer on the core

Outgoing email that one person sends. The stream's opener creates an email, new or in reply to a message in an
archive, and is the one who decides it; drafters (agents, or anyone else on the host) are each solicited once and
hand in drafts; a composer, who is neither a drafter of the email nor the opener, hands in the final draft and the
screen the opener decides from; the first composed draft ends drafting; the opener sends or discards the email, once.
Commands are intent: `sent` is final whether or not the outbox delivers, and a follow-up is a fresh email.

- `email.create {stream_id, email_id, in_reply_to_url?, meta?}` → `email.created`: the opener creates an email, its
  id new on the stream, optionally in reply to a message, named by the URL of its `.eml` in the archive.
- `email.solicit {stream_id, email_id, drafter_id, meta?}` → `email.solicited`: the opener asks a drafter other than
  itself, and not a composer of the email, for a draft, once per drafter, before the first composed draft.
- `email.draft {stream_id, email_id, draft_url, meta?}` → `email.drafted`: a solicited drafter hands in a draft, the
  URL of an `.eml`, as often as it likes, before the first composed draft.
- `email.compose {stream_id, email_id, composed_url, screen_url, meta?}` → `email.composed`: anyone who is neither a
  drafter of the email nor the opener hands in the final draft, an `.eml`, and the screen the opener should see, any
  number of times until the decision. The first composed draft cuts off solicitations and drafts. A composer is never
  afterwards a drafter of the email.
- `email.send {stream_id, email_id, sent_url, meta?}` → `email.sent`, `email.discard {stream_id, email_id, meta?}` →
  `email.discarded`: the opener decides the email, once; nothing about it follows. `sent_url` names the sent message
  as an `.eml`, in the outbox or an archive.

Every `.eml` named on an email is unique on that email (`eml_urls_must_be_unique`): the message it replies to, every
draft, every composed draft and the sent message differ, so each role hands in its own file and nobody hands back
another's. An `.eml` URL is an `eml` field (`validEml`): a URL (`validUrl`) ending in `.eml`. What it points at is the
harness's check, not the proof's. The screen is a `url` field.

Every permission rests on the core's `v.opener`: the opener creates, solicits and decides; the drafters are whom the
opener solicited; the composers are everyone else. The memory is the notes the events make (`notes`), in order:
`("email", k, "")` and, when the email is a reply, `("reply_to", k, u)`; `("drafter", k, drafter)`; `("draft", k, u)`;
`("composer", k, composer)` and `("composed", k, u)`; `("sent", k, u)`; `("discarded", k, "")`. A read of a stream
adds `emails`, `replies_to`, `drafters`, `drafts`, `composers`, `composed`, `sent` and `discarded`.
-/

namespace Email
open Provenstream Provenstream.Layer Provenstream.Wire

/-- A URL: a scheme, `://` and something after it; no whitespace or control character; at most 2048 characters. What
it points at is the harness's business. -/
def validUrl (s : String) : Bool :=
  s.length ≤ 2048 && s.all (fun (c : Char) => 32 < c.val && c.val != 127) &&
  match s.splitOn "://" with
  | [scheme, rest] => !scheme.isEmpty && !rest.isEmpty
  | _ => false

/-- The URL of an `.eml`: a URL whose last four characters are `.eml`. (Spelled on the character list rather than
with `String.endsWith`, whose compiled form reaches primitives the audit does not trust.) -/
def endsWithEml (s : String) : Bool :=
  match s.toList.reverse with
  | 'l' :: 'm' :: 'e' :: '.' :: _ => true
  | _ => false

def validEml (s : String) : Bool := validUrl s && endsWithEml s

/-- The kind of a screen field. -/
def urlKind : Kind := .text "url" validUrl

/-- The kind of an `.eml` field: the message replied to, a draft, the composed draft, the sent message. -/
def emlKind : Kind := .text "eml" validEml

/-- The kind of an optional `.eml` field (`eml?`): an `.eml` URL, or absent or `null`. -/
def emlOptKind : Kind := .textOpt "eml" validEml

inductive EmailCommand where
  | create (stream email : Id) (replyTo : Option String) («meta» : Meta)
  | solicit (stream email drafter : Id) («meta» : Meta)
  | draft (stream email : Id) (draft : String) («meta» : Meta)
  | compose (stream email : Id) (composed screen : String) («meta» : Meta)
  | send (stream email : Id) (sent : String) («meta» : Meta)
  | discard (stream email : Id) («meta» : Meta)
  deriving DecidableEq

inductive EmailEvent where
  | created (actor stream email : Id) (replyTo : Option String) («meta» : Meta)
  | solicited (actor stream email drafter : Id) («meta» : Meta)
  | drafted (actor stream email : Id) (draft : String) («meta» : Meta)
  | composed (actor stream email : Id) (composed screen : String) («meta» : Meta)
  | sent (actor stream email : Id) (sent : String) («meta» : Meta)
  | discarded (actor stream email : Id) («meta» : Meta)
  deriving DecidableEq

/-- A note an email event makes: what (`email`, `reply_to`, `drafter`, `draft`, `composer`, `composed`, `sent`,
`discarded`), the email, and whom or which (a principal, an `.eml` URL, or `""`). -/
abbrev Note := String × String × String

/-- The note an email's replied-to message makes: one when the email is a reply, none otherwise. -/
def replyNotes (k : String) : Option String → List Note
  | none => []
  | some u => [("reply_to", k, u)]

def notes : EmailEvent → List Note
  | .created _ _ k r _ => ("email", k, "") :: replyNotes k r
  | .solicited _ _ k d _ => [("drafter", k, d)]
  | .drafted _ _ k u _ => [("draft", k, u)]
  | .composed a _ k u _ _ => [("composer", k, a), ("composed", k, u)]
  | .sent _ _ k u _ => [("sent", k, u)]
  | .discarded _ _ k _ => [("discarded", k, "")]

/-- The memory's step: the event's notes, appended. -/
def addNotes (st : List Note) (e : EmailEvent) : List Note := st ++ notes e

/-- Some note says `what` of email `k`. -/
def noted (w : List Note) (what k : String) : Bool := w.any fun n => n.1 == what && n.2.1 == k

/-- The email `k` is decided: sent or discarded. -/
def decided (w : List Note) (k : String) : Bool := noted w "sent" k || noted w "discarded" k

/-- A note of this kind names an `.eml` of its email. -/
def namesEml (what : String) : Bool :=
  what == "reply_to" || what == "draft" || what == "composed" || what == "sent"

/-- Some note names the `.eml` `u` of email `k`. -/
def emlNamed (w : List Note) (k u : String) : Bool :=
  w.any fun n => namesEml n.1 && n.2.1 == k && n.2.2 == u

/-- The emails some note says `what` of, in order. -/
def itemsOf (w : List Note) (what : String) : List String := w.filterMap fun n => if n.1 == what then some n.2.1 else none

/-- The email and the third slot of each note saying `what`, as `{email_id, <who>}`. -/
def pairsOf (w : List Note) (what who : String) : J :=
  .arr (w.filterMap fun n => if n.1 == what then some (.obj [("email_id", .str n.2.1), (who, .str n.2.2)]) else none)

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

abbrev outbound : Layer where
  Cmd := EmailCommand
  Ev := EmailEvent
  toRequest
    | .created a t k r m => (a, .create t k r m)
    | .solicited a t k d m => (a, .solicit t k d m)
    | .drafted a t k u m => (a, .draft t k u m)
    | .composed a t k u s m => (a, .compose t k u s m)
    | .sent a t k u m => (a, .send t k u m)
    | .discarded a t k m => (a, .discard t k m)
  ofRequest
    | (a, .create t k r m) => .created a t k r m
    | (a, .solicit t k d m) => .solicited a t k d m
    | (a, .draft t k u m) => .drafted a t k u m
    | (a, .compose t k u s m) => .composed a t k u s m
    | (a, .send t k u m) => .sent a t k u m
    | (a, .discard t k m) => .discarded a t k m
  stream | .create t .. | .solicit t .. | .draft t .. | .compose t .. | .send t .. | .discard t .. => t
  schema := [{ name := "email.create", event := "email.created", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("email_id", .uuid), ("in_reply_to_url", emlOptKind), ("meta", .metaOpt)] },
             { name := "email.solicit", event := "email.solicited", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("email_id", .uuid), ("drafter_id", .uuid), ("meta", .metaOpt)] },
             { name := "email.draft", event := "email.drafted", who := some "a drafter the opener solicited",
               fields := [("stream_id", .uuid), ("email_id", .uuid), ("draft_url", emlKind), ("meta", .metaOpt)] },
             { name := "email.compose", event := "email.composed",
               who := some "anyone who is neither a drafter of the email nor the opener",
               fields := [("stream_id", .uuid), ("email_id", .uuid), ("composed_url", emlKind),
                          ("screen_url", urlKind), ("meta", .metaOpt)] },
             { name := "email.send", event := "email.sent", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("email_id", .uuid), ("sent_url", emlKind), ("meta", .metaOpt)] },
             { name := "email.discard", event := "email.discarded", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("email_id", .uuid), ("meta", .metaOpt)] }]
  toVals
    | .create t k r m => ("email.create", [.s t, .s k, .uo r, .m m])
    | .solicit t k d m => ("email.solicit", [.s t, .s k, .s d, .m m])
    | .draft t k u m => ("email.draft", [.s t, .s k, .s u, .m m])
    | .compose t k u s m => ("email.compose", [.s t, .s k, .s u, .s s, .m m])
    | .send t k u m => ("email.send", [.s t, .s k, .s u, .m m])
    | .discard t k m => ("email.discard", [.s t, .s k, .m m])
  ofVals
    | "email.create", [.s t, .s k, .uo r, .m m] => some (.create t k r m)
    | "email.solicit", [.s t, .s k, .s d, .m m] => some (.solicit t k d m)
    | "email.draft", [.s t, .s k, .s u, .m m] => some (.draft t k u m)
    | "email.compose", [.s t, .s k, .s u, .s s, .m m] => some (.compose t k u s m)
    | "email.send", [.s t, .s k, .s u, .m m] => some (.send t k u m)
    | "email.discard", [.s t, .s k, .m m] => some (.discard t k m)
    | _, _ => none
  memory := foldMemory [] addNotes notesToJ notesFromJ notesFromJ_toJ
  readJ st := [("emails", .arr ((itemsOf st "email").map .str)),
               ("replies_to", pairsOf st "reply_to" "in_reply_to_url"),
               ("drafters", pairsOf st "drafter" "drafter_id"),
               ("drafts", pairsOf st "draft" "draft_url"),
               ("composers", pairsOf st "composer" "composer_id"),
               ("composed", pairsOf st "composed" "composed_url"),
               ("sent", pairsOf st "sent" "sent_url"),
               ("discarded", .arr ((itemsOf st "discarded").map .str))]
  rules := [⟨"only_opener_can_create", ["email.create"], fun v _ e => match e with
               | .created a .. => v.opener == some a | _ => true⟩,
            ⟨"email_id_must_be_new", ["email.create"], fun _ w e => match e with
               | .created _ _ k _ _ => !noted w "email" k | _ => true⟩,
            ⟨"email_must_exist", ["email.solicit", "email.draft", "email.compose", "email.send", "email.discard"],
             fun _ w e => match e with
               | .solicited _ _ k _ _ | .drafted _ _ k _ _ | .composed _ _ k _ _ _ | .sent _ _ k _ _
               | .discarded _ _ k _ => noted w "email" k
               | _ => true⟩,
            ⟨"eml_urls_must_be_unique", ["email.draft", "email.compose", "email.send"],
             fun _ w e => match e with
               | .drafted _ _ k u _ | .composed _ _ k u _ _ | .sent _ _ k u _ => !emlNamed w k u
               | _ => true⟩,
            ⟨"only_opener_can_solicit", ["email.solicit"], fun v _ e => match e with
               | .solicited a .. => v.opener == some a | _ => true⟩,
            ⟨"drafter_must_not_be_the_opener", ["email.solicit"], fun v _ e => match e with
               | .solicited _ _ _ d _ => v.opener != some d | _ => true⟩,
            ⟨"drafter_is_solicited_once", ["email.solicit"], fun _ w e => match e with
               | .solicited _ _ k d _ => !w.contains ("drafter", k, d) | _ => true⟩,
            ⟨"drafter_must_not_be_a_composer", ["email.solicit"], fun _ w e => match e with
               | .solicited _ _ k d _ => !w.contains ("composer", k, d) | _ => true⟩,
            ⟨"email_must_not_be_composed", ["email.solicit", "email.draft"], fun _ w e => match e with
               | .solicited _ _ k _ _ | .drafted _ _ k _ _ => !noted w "composed" k | _ => true⟩,
            ⟨"only_solicited_drafters_can_draft", ["email.draft"], fun _ w e => match e with
               | .drafted a _ k _ _ => w.contains ("drafter", k, a) | _ => true⟩,
            ⟨"composer_must_not_be_a_drafter", ["email.compose"], fun _ w e => match e with
               | .composed a _ k _ _ _ => !w.contains ("drafter", k, a) | _ => true⟩,
            ⟨"composer_must_not_be_the_opener", ["email.compose"], fun v _ e => match e with
               | .composed a .. => v.opener != some a | _ => true⟩,
            ⟨"only_opener_can_decide", ["email.send", "email.discard"], fun v _ e => match e with
               | .sent a .. | .discarded a .. => v.opener == some a | _ => true⟩,
            ⟨"email_is_decided_once", ["email.send", "email.discard"], fun _ w e => match e with
               | .sent _ _ k _ _ | .discarded _ _ k _ => !decided w k | _ => true⟩,
            ⟨"email_must_be_undecided", ["email.solicit", "email.draft", "email.compose"],
             fun _ w e => match e with
               | .solicited _ _ k _ _ | .drafted _ _ k _ _ | .composed _ _ k _ _ _ => !decided w k | _ => true⟩]

end Email
