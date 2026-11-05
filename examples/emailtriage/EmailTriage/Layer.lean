-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Provenstream.Interface

/-!
# Inbound email triage: a layer on the core

What to do with a message that arrived. The stream's opener records every inbound message as a triage and is the
one who decides it; advisers (agents, or anyone else on the host) are each asked once and send back a verdict, `reply`,
`work` or `ignore`; a reviewer, who is neither an adviser of the triage nor the opener, makes the final call, the same
three words; the opener decides the triage, once: `reply` (an email is created on the email proof to draft it), `work`
(a general work item is created for it, on a stream of the work proof) or `ignore`. Commands are intent: `replied`
means the reply was begun, not sent; the email proof decides the sending. `worked` means the item was begun, not done.

- `triage.create {stream_id, triage_id, message_url, meta?}` → `triage.created`: the opener records an inbound
  message, its id new on the stream, named by the URL of its `.eml` in the archive.
- `triage.ask {stream_id, triage_id, adviser_id, meta?}` → `triage.asked`: the opener asks an adviser other than
  itself, and not a reviewer of the triage, for a verdict, once per adviser, before the first review.
- `triage.advise {stream_id, triage_id, verdict, meta?}` → `triage.advised`: an asked adviser sends its verdict,
  `reply`, `work` or `ignore`, once, before the first review. The reason is in `meta`.
- `triage.review {stream_id, triage_id, verdict, meta?}` → `triage.reviewed`: anyone who is neither an adviser of
  the triage nor the opener makes the final call, `reply`, `work` or `ignore`, any number of times until the decision. The
  first review cuts off asks and advice. A reviewer is never afterwards an adviser of the triage.
- `triage.reply {stream_id, triage_id, email_id, meta?}` → `triage.replied`, `triage.work {stream_id, triage_id,
  work_id, meta?}` → `triage.worked`, `triage.ignore {stream_id, triage_id, meta?}` → `triage.ignored`: the opener
  decides the triage, once; nothing about it follows. `email_id` is the email the reply is drafted as, on a stream of
  the email proof. `work_id` is the item the message became, on a stream of the work proof.

A verdict is a `verdict` field: exactly `reply`, `work` or `ignore` (`validVerdict`). The message URL is an `eml` field: a URL
(`validUrl`) ending in `.eml`. What it points at is the harness's check, not the proof's.

Every permission rests on the core's `v.opener`: the opener creates, asks and decides; the advisers are whom the
opener asked; the reviewers are everyone else. The memory is the notes the events make (`notes`), in order:
`("triage", k, message)`; `("adviser", k, adviser)`; `("advice", k, adviser)` and `("verdict", k, verdict)`;
`("reviewer", k, reviewer)` and `("call", k, verdict)`; `("replied", k, email)`; `("worked", k, work)`;
`("ignored", k, "")`. A read of a stream adds `triages`, `advisers`, `advice`, `verdicts`, `reviewers`, `calls`,
`replied`, `worked` and `ignored`.
-/

namespace EmailTriage
open Provenstream Provenstream.Layer Provenstream.Wire

/-- A URL: a scheme, `://` and something after it; no whitespace or control character; at most 2048 characters. -/
def validUrl (s : String) : Bool :=
  s.length ≤ 2048 && s.all (fun (c : Char) => 32 < c.val && c.val != 127) &&
  match s.splitOn "://" with
  | [scheme, rest] => !scheme.isEmpty && !rest.isEmpty
  | _ => false

/-- The URL of an `.eml`: a URL whose last four characters are `.eml` (spelled on the character list, as the email
layer does, so the compiled form reaches no primitive the audit does not trust). -/
def endsWithEml (s : String) : Bool :=
  match s.toList.reverse with
  | 'l' :: 'm' :: 'e' :: '.' :: _ => true
  | _ => false

def validEml (s : String) : Bool := validUrl s && endsWithEml s

/-- A verdict: exactly `reply`, `work` or `ignore`. -/
def validVerdict (s : String) : Bool := s == "reply" || s == "work" || s == "ignore"

/-- The kind of the message field. -/
def emlKind : Kind := .text "eml" validEml

/-- The kind of a verdict field. -/
def verdictKind : Kind := .text "verdict" validVerdict

inductive TriageCommand where
  | create (stream triage : Id) (message : String) («meta» : Meta)
  | ask (stream triage adviser : Id) («meta» : Meta)
  | advise (stream triage : Id) (verdict : String) («meta» : Meta)
  | review (stream triage : Id) (verdict : String) («meta» : Meta)
  | reply (stream triage email : Id) («meta» : Meta)
  | work (stream triage item : Id) («meta» : Meta)
  | ignore (stream triage : Id) («meta» : Meta)
  deriving DecidableEq

inductive TriageEvent where
  | created (actor stream triage : Id) (message : String) («meta» : Meta)
  | asked (actor stream triage adviser : Id) («meta» : Meta)
  | advised (actor stream triage : Id) (verdict : String) («meta» : Meta)
  | reviewed (actor stream triage : Id) (verdict : String) («meta» : Meta)
  | replied (actor stream triage email : Id) («meta» : Meta)
  | worked (actor stream triage item : Id) («meta» : Meta)
  | ignored (actor stream triage : Id) («meta» : Meta)
  deriving DecidableEq

/-- A note a triage event makes: what (`triage`, `adviser`, `advice`, `verdict`, `reviewer`, `call`, `replied`,
`worked`, `ignored`), the triage, and whom or which (a principal, an `.eml` URL, a verdict, an email or work item id, or
`""`). -/
abbrev Note := String × String × String

def notes : TriageEvent → List Note
  | .created _ _ k u _ => [("triage", k, u)]
  | .asked _ _ k d _ => [("adviser", k, d)]
  | .advised a _ k v _ => [("advice", k, a), ("verdict", k, v)]
  | .reviewed a _ k v _ => [("reviewer", k, a), ("call", k, v)]
  | .replied _ _ k e _ => [("replied", k, e)]
  | .worked _ _ k i _ => [("worked", k, i)]
  | .ignored _ _ k _ => [("ignored", k, "")]

/-- The memory's step: the event's notes, appended. -/
def addNotes (st : List Note) (e : TriageEvent) : List Note := st ++ notes e

/-- Some note says `what` of triage `k`. -/
def noted (w : List Note) (what k : String) : Bool := w.any fun n => n.1 == what && n.2.1 == k

/-- The triage `k` is decided: replied, made a work item, or ignored. -/
def decided (w : List Note) (k : String) : Bool := noted w "replied" k || noted w "worked" k || noted w "ignored" k

/-- The triages some note says `what` of, in order. -/
def itemsOf (w : List Note) (what : String) : List String := w.filterMap fun n => if n.1 == what then some n.2.1 else none

/-- The triage and the third slot of each note saying `what`, as `{triage_id, <who>}`. -/
def pairsOf (w : List Note) (what who : String) : J :=
  .arr (w.filterMap fun n => if n.1 == what then some (.obj [("triage_id", .str n.2.1), (who, .str n.2.2)]) else none)

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

abbrev inbound : Layer where
  Cmd := TriageCommand
  Ev := TriageEvent
  toRequest
    | .created a t k u m => (a, .create t k u m)
    | .asked a t k d m => (a, .ask t k d m)
    | .advised a t k v m => (a, .advise t k v m)
    | .reviewed a t k v m => (a, .review t k v m)
    | .replied a t k e m => (a, .reply t k e m)
    | .worked a t k i m => (a, .work t k i m)
    | .ignored a t k m => (a, .ignore t k m)
  ofRequest
    | (a, .create t k u m) => .created a t k u m
    | (a, .ask t k d m) => .asked a t k d m
    | (a, .advise t k v m) => .advised a t k v m
    | (a, .review t k v m) => .reviewed a t k v m
    | (a, .reply t k e m) => .replied a t k e m
    | (a, .work t k i m) => .worked a t k i m
    | (a, .ignore t k m) => .ignored a t k m
  stream | .create t .. | .ask t .. | .advise t .. | .review t .. | .reply t .. | .work t .. | .ignore t .. => t
  schema := [{ name := "triage.create", event := "triage.created", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("triage_id", .uuid), ("message_url", emlKind), ("meta", .metaOpt)] },
             { name := "triage.ask", event := "triage.asked", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("triage_id", .uuid), ("adviser_id", .uuid), ("meta", .metaOpt)] },
             { name := "triage.advise", event := "triage.advised", who := some "an adviser the opener asked",
               fields := [("stream_id", .uuid), ("triage_id", .uuid), ("verdict", verdictKind), ("meta", .metaOpt)] },
             { name := "triage.review", event := "triage.reviewed",
               who := some "anyone who is neither an adviser of the triage nor the opener",
               fields := [("stream_id", .uuid), ("triage_id", .uuid), ("verdict", verdictKind), ("meta", .metaOpt)] },
             { name := "triage.reply", event := "triage.replied", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("triage_id", .uuid), ("email_id", .uuid), ("meta", .metaOpt)] },
             { name := "triage.work", event := "triage.worked", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("triage_id", .uuid), ("work_id", .uuid), ("meta", .metaOpt)] },
             { name := "triage.ignore", event := "triage.ignored", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("triage_id", .uuid), ("meta", .metaOpt)] }]
  toVals
    | .create t k u m => ("triage.create", [.s t, .s k, .s u, .m m])
    | .ask t k d m => ("triage.ask", [.s t, .s k, .s d, .m m])
    | .advise t k v m => ("triage.advise", [.s t, .s k, .s v, .m m])
    | .review t k v m => ("triage.review", [.s t, .s k, .s v, .m m])
    | .reply t k e m => ("triage.reply", [.s t, .s k, .s e, .m m])
    | .work t k i m => ("triage.work", [.s t, .s k, .s i, .m m])
    | .ignore t k m => ("triage.ignore", [.s t, .s k, .m m])
  ofVals
    | "triage.create", [.s t, .s k, .s u, .m m] => some (.create t k u m)
    | "triage.ask", [.s t, .s k, .s d, .m m] => some (.ask t k d m)
    | "triage.advise", [.s t, .s k, .s v, .m m] => some (.advise t k v m)
    | "triage.review", [.s t, .s k, .s v, .m m] => some (.review t k v m)
    | "triage.reply", [.s t, .s k, .s e, .m m] => some (.reply t k e m)
    | "triage.work", [.s t, .s k, .s i, .m m] => some (.work t k i m)
    | "triage.ignore", [.s t, .s k, .m m] => some (.ignore t k m)
    | _, _ => none
  memory := foldMemory [] addNotes notesToJ notesFromJ notesFromJ_toJ
  readJ st := [("triages", pairsOf st "triage" "message_url"),
               ("advisers", pairsOf st "adviser" "adviser_id"),
               ("advice", pairsOf st "advice" "adviser_id"),
               ("verdicts", pairsOf st "verdict" "verdict"),
               ("reviewers", pairsOf st "reviewer" "reviewer_id"),
               ("calls", pairsOf st "call" "verdict"),
               ("replied", pairsOf st "replied" "email_id"),
               ("worked", pairsOf st "worked" "work_id"),
               ("ignored", .arr ((itemsOf st "ignored").map .str))]
  rules := [⟨"only_opener_can_create", ["triage.create"], fun v _ e => match e with
               | .created a .. => v.opener == some a | _ => true⟩,
            ⟨"triage_id_must_be_new", ["triage.create"], fun _ w e => match e with
               | .created _ _ k _ _ => !noted w "triage" k | _ => true⟩,
            ⟨"triage_must_exist", ["triage.ask", "triage.advise", "triage.review", "triage.reply", "triage.work", "triage.ignore"],
             fun _ w e => match e with
               | .asked _ _ k _ _ | .advised _ _ k _ _ | .reviewed _ _ k _ _ | .replied _ _ k _ _ | .worked _ _ k _ _
               | .ignored _ _ k _ => noted w "triage" k
               | _ => true⟩,
            ⟨"only_opener_can_ask", ["triage.ask"], fun v _ e => match e with
               | .asked a .. => v.opener == some a | _ => true⟩,
            ⟨"adviser_must_not_be_the_opener", ["triage.ask"], fun v _ e => match e with
               | .asked _ _ _ d _ => v.opener != some d | _ => true⟩,
            ⟨"adviser_is_asked_once", ["triage.ask"], fun _ w e => match e with
               | .asked _ _ k d _ => !w.contains ("adviser", k, d) | _ => true⟩,
            ⟨"adviser_must_not_be_a_reviewer", ["triage.ask"], fun _ w e => match e with
               | .asked _ _ k d _ => !w.contains ("reviewer", k, d) | _ => true⟩,
            ⟨"triage_must_not_be_reviewed", ["triage.ask", "triage.advise"], fun _ w e => match e with
               | .asked _ _ k _ _ | .advised _ _ k _ _ => !noted w "reviewer" k | _ => true⟩,
            ⟨"only_asked_advisers_can_advise", ["triage.advise"], fun _ w e => match e with
               | .advised a _ k _ _ => w.contains ("adviser", k, a) | _ => true⟩,
            ⟨"adviser_advises_once", ["triage.advise"], fun _ w e => match e with
               | .advised a _ k _ _ => !w.contains ("advice", k, a) | _ => true⟩,
            ⟨"reviewer_must_not_be_an_adviser", ["triage.review"], fun _ w e => match e with
               | .reviewed a _ k _ _ => !w.contains ("adviser", k, a) | _ => true⟩,
            ⟨"reviewer_must_not_be_the_opener", ["triage.review"], fun v _ e => match e with
               | .reviewed a .. => v.opener != some a | _ => true⟩,
            ⟨"only_opener_can_decide", ["triage.reply", "triage.work", "triage.ignore"], fun v _ e => match e with
               | .replied a .. | .worked a .. | .ignored a .. => v.opener == some a | _ => true⟩,
            ⟨"triage_is_decided_once", ["triage.reply", "triage.work", "triage.ignore"], fun _ w e => match e with
               | .replied _ _ k _ _ | .worked _ _ k _ _ | .ignored _ _ k _ => !decided w k | _ => true⟩,
            ⟨"triage_must_be_undecided", ["triage.ask", "triage.advise", "triage.review"],
             fun _ w e => match e with
               | .asked _ _ k _ _ | .advised _ _ k _ _ | .reviewed _ _ k _ _ => !decided w k | _ => true⟩]

end EmailTriage
