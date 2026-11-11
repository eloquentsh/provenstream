-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Provenstream.Interface

/-!
# Action: a layer on the core

A gate in front of a browser. Reads of the page never reach this stream. Every other action is asked about here before it runs, and an
evaluator says whether it gets ready for the task or completes it. Getting ready is approved. Completing is rejected.

- `evaluator.name {stream_id, evaluator_id, meta?}` -> `evaluator.named`: the opener names an evaluator other than itself, once each.
- `action.evaluate {stream_id, action_id, context_url, mode, meta?}` -> `action.evaluated`: anyone asks about one action, its id new.
  `context_url` pins a file holding everything an evaluator reads: the task, the action and, for an action on a page, the page as
  markdown with the target marked. `mode` is `readonly` or `action_allowed`.
- `action.approve {stream_id, action_id, meta?}` -> `action.approved`, `action.reject {stream_id, action_id, meta?}` -> `action.rejected`:
  the opener or an evaluator answers, once. Whoever asked never answers.

- `overrider.name {stream_id, overrider_id, meta?}` -> `overrider.named`: the opener names an overrider other than itself, once each. An
  overrider is the browser extension, which overrides only after the person types their code in its own window.
- `action.override {stream_id, action_id, meta?}` -> `action.overridden`: an overrider overrides a rejected action, once, before it is
  recorded. Whoever asked never overrides.
- `action.record {stream_id, action_id, outcome, result_url, meta?}` -> `action.recorded`: whoever asked records what happened, once. The
  outcome is `done`, `failed` or `not_run`, and `result_url` pins a file of the result that names the context. Only an action that may
  run is recorded as `done` or `failed`.

An action may run once it is approved, or once it is rejected and then overridden. A read of a stream names these in `runnable`. An
action with no answer may not run, so an evaluator's opinion is always on the stream first. `mode` records what the asker wanted, and
decides nothing: only an override lets a rejected action run.

An engine cannot see a page or fetch a URL, and it cannot stop a browser. It checks the form of the pin and nothing about the bytes.
Whoever reads the URL checks the bytes against the pin. The extension runs an action only when `runnable` names it.

The memory is the notes the events make: `("evaluator", "", e)`, `("action", k, asker)`, `("mode", k, mode)`, `("approved", k, who)` and
`("rejected", k, who)`, `("overrider", "", o)`, `("overridden", k, who)` and `("recorded", k, outcome)`.
-/

namespace Action
open Provenstream Provenstream.Layer Provenstream.Wire

/-- A URL: a scheme, `://` and something after it; no whitespace or control character; at most 2048 characters. -/
def validUrl (s : String) : Bool :=
  s.length ≤ 2048 && s.all (fun (c : Char) => 32 < c.val && c.val != 127) &&
  match s.splitOn "://" with
  | [scheme, rest] => !scheme.isEmpty && !rest.isEmpty
  | _ => false

/-- The hex digits of a pin. -/
def isLowerHex (c : Char) : Bool := ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

/-- The characters before the first `&`. -/
def beforeAmp : List Char → List Char
  | [] => []
  | c :: cs => if c == '&' then [] else c :: beforeAmp cs

/-- The sha256 a URL pins: the 64 hex digits after `#sha256=`, up to `&` or the end. -/
def pinOf (u : String) : Option String :=
  match (u.toList.dropWhile (· != '#')) with
  | '#' :: 's' :: 'h' :: 'a' :: '2' :: '5' :: '6' :: '=' :: rest =>
    let h := beforeAmp rest
    if h.length == 64 && h.all isLowerHex then some (String.ofList h) else none
  | _ => none

/-- The URL carries a pin. This is the form of the pin alone: the proof never sees the bytes. -/
def pinned (u : String) : Bool :=
  match pinOf u with
  | some _ => true
  | none => false

def validOutcome (s : String) : Bool := s == "done" || s == "failed" || s == "not_run"

def readonly : String := "readonly"
def actionAllowed : String := "action_allowed"
def validMode (s : String) : Bool := s == readonly || s == actionAllowed

def urlKind : Kind := .text "url" validUrl
def outcomeKind : Kind := .text "outcome" validOutcome
def modeKind : Kind := .text "mode" validMode

inductive ActionCommand where
  | nameEvaluator (stream evaluator : Id) («meta» : Meta)
  | evaluate (stream action : Id) (context mode : String) («meta» : Meta)
  | approve (stream action : Id) («meta» : Meta)
  | reject (stream action : Id) («meta» : Meta)
  | nameOverrider (stream overrider : Id) («meta» : Meta)
  | override (stream action : Id) («meta» : Meta)
  | record (stream action : Id) (outcome result : String) («meta» : Meta)
  deriving DecidableEq

inductive ActionEvent where
  | evaluatorNamed (actor stream evaluator : Id) («meta» : Meta)
  | evaluated (actor stream action : Id) (context mode : String) («meta» : Meta)
  | approved (actor stream action : Id) («meta» : Meta)
  | rejected (actor stream action : Id) («meta» : Meta)
  | overriderNamed (actor stream overrider : Id) («meta» : Meta)
  | overridden (actor stream action : Id) («meta» : Meta)
  | recorded (actor stream action : Id) (outcome result : String) («meta» : Meta)
  deriving DecidableEq

abbrev Note := String × String × String

def notes : ActionEvent → List Note
  | .evaluatorNamed _ _ e _ => [("evaluator", "", e)]
  | .evaluated a _ k _ f _ => [("action", k, a), ("mode", k, f)]
  | .approved a _ k _ => [("approved", k, a)]
  | .rejected a _ k _ => [("rejected", k, a)]
  | .overriderNamed _ _ o _ => [("overrider", "", o)]
  | .overridden a _ k _ => [("overridden", k, a)]
  | .recorded _ _ k o _ _ => [("recorded", k, o)]

def addNotes (st : List Note) (e : ActionEvent) : List Note := st ++ notes e

def noted (w : List Note) (what k : String) : Bool := w.any fun n => n.1 == what && n.2.1 == k

def answered (w : List Note) (k : String) : Bool := noted w "approved" k || noted w "rejected" k

/-- The action may run: approved, or rejected and then overridden. No answer, no run. -/
def mayRun (w : List Note) (k : String) : Bool :=
  noted w "approved" k || (noted w "rejected" k && noted w "overridden" k)

/-- The actions that may run, in the order they were asked about. -/
def runnable (w : List Note) : List String :=
  w.filterMap fun n => if n.1 == "action" && mayRun w n.2.1 then some n.2.1 else none

def thirdOf (w : List Note) (what : String) : List String := w.filterMap fun n => if n.1 == what then some n.2.2 else none

def pairsOf (w : List Note) (what name : String) : J :=
  .arr (w.filterMap fun n => if n.1 == what then some (.obj [("action_id", .str n.2.1), (name, .str n.2.2)]) else none)

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

abbrev actions : Layer where
  Cmd := ActionCommand
  Ev := ActionEvent
  toRequest
    | .evaluatorNamed a t e m => (a, .nameEvaluator t e m)
    | .evaluated a t k c f m => (a, .evaluate t k c f m)
    | .approved a t k m => (a, .approve t k m)
    | .rejected a t k m => (a, .reject t k m)
    | .overriderNamed a t o m => (a, .nameOverrider t o m)
    | .overridden a t k m => (a, .override t k m)
    | .recorded a t k o r m => (a, .record t k o r m)
  ofRequest
    | (a, .nameEvaluator t e m) => .evaluatorNamed a t e m
    | (a, .evaluate t k c f m) => .evaluated a t k c f m
    | (a, .approve t k m) => .approved a t k m
    | (a, .reject t k m) => .rejected a t k m
    | (a, .nameOverrider t o m) => .overriderNamed a t o m
    | (a, .override t k m) => .overridden a t k m
    | (a, .record t k o r m) => .recorded a t k o r m
  stream | .nameEvaluator t .. | .evaluate t .. | .approve t .. | .reject t .. | .nameOverrider t .. | .override t .. | .record t .. => t
  schema := [{ name := "evaluator.name", event := "evaluator.named", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("evaluator_id", .uuid), ("meta", .metaOpt)] },
             { name := "action.evaluate", event := "action.evaluated", who := some "anyone",
               fields := [("stream_id", .uuid), ("action_id", .uuid), ("context_url", urlKind), ("mode", modeKind), ("meta", .metaOpt)] },
             { name := "action.approve", event := "action.approved", who := some "the opener or an evaluator, never whoever asked",
               fields := [("stream_id", .uuid), ("action_id", .uuid), ("meta", .metaOpt)] },
             { name := "action.reject", event := "action.rejected", who := some "the opener or an evaluator, never whoever asked",
               fields := [("stream_id", .uuid), ("action_id", .uuid), ("meta", .metaOpt)] },
             { name := "overrider.name", event := "overrider.named", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("overrider_id", .uuid), ("meta", .metaOpt)] },
             { name := "action.override", event := "action.overridden", who := some "an overrider the opener named, never whoever asked",
               fields := [("stream_id", .uuid), ("action_id", .uuid), ("meta", .metaOpt)] },
             { name := "action.record", event := "action.recorded", who := some "whoever asked about the action",
               fields := [("stream_id", .uuid), ("action_id", .uuid), ("outcome", outcomeKind), ("result_url", urlKind), ("meta", .metaOpt)] }]
  toVals
    | .nameEvaluator t e m => ("evaluator.name", [.s t, .s e, .m m])
    | .evaluate t k c f m => ("action.evaluate", [.s t, .s k, .s c, .s f, .m m])
    | .approve t k m => ("action.approve", [.s t, .s k, .m m])
    | .reject t k m => ("action.reject", [.s t, .s k, .m m])
    | .nameOverrider t o m => ("overrider.name", [.s t, .s o, .m m])
    | .override t k m => ("action.override", [.s t, .s k, .m m])
    | .record t k o r m => ("action.record", [.s t, .s k, .s o, .s r, .m m])
  ofVals
    | "evaluator.name", [.s t, .s e, .m m] => some (.nameEvaluator t e m)
    | "action.evaluate", [.s t, .s k, .s c, .s f, .m m] => some (.evaluate t k c f m)
    | "action.approve", [.s t, .s k, .m m] => some (.approve t k m)
    | "action.reject", [.s t, .s k, .m m] => some (.reject t k m)
    | "overrider.name", [.s t, .s o, .m m] => some (.nameOverrider t o m)
    | "action.override", [.s t, .s k, .m m] => some (.override t k m)
    | "action.record", [.s t, .s k, .s o, .s r, .m m] => some (.record t k o r m)
    | _, _ => none
  memory := foldMemory [] addNotes notesToJ notesFromJ notesFromJ_toJ
  readJ st := [("evaluators", .arr ((thirdOf st "evaluator").map .str)),
               ("actions", pairsOf st "action" "asker_id"),
               ("approved", pairsOf st "approved" "by"),
               ("rejected", pairsOf st "rejected" "by"),
               ("modes", pairsOf st "mode" "mode"),
               ("overriders", .arr ((thirdOf st "overrider").map .str)),
               ("overridden", pairsOf st "overridden" "by"),
               ("runnable", .arr ((runnable st).map .str)),
               ("recorded", pairsOf st "recorded" "outcome")]
  rules := [⟨"only_opener_can_name_evaluators", ["evaluator.name"], fun v _ e => match e with
               | .evaluatorNamed a .. => v.opener == some a | _ => true⟩,
            ⟨"evaluator_must_not_be_the_opener", ["evaluator.name"], fun v _ e => match e with
               | .evaluatorNamed _ _ x _ => v.opener != some x | _ => true⟩,
            ⟨"evaluator_is_named_once", ["evaluator.name"], fun _ w e => match e with
               | .evaluatorNamed _ _ x _ => !w.contains ("evaluator", "", x) | _ => true⟩,
            ⟨"action_id_must_be_new", ["action.evaluate"], fun _ w e => match e with
               | .evaluated _ _ k .. => !noted w "action" k | _ => true⟩,
            ⟨"context_url_must_be_pinned", ["action.evaluate"], fun _ _ e => match e with
               | .evaluated _ _ _ c _ _ => pinned c | _ => true⟩,
            ⟨"action_must_exist", ["action.approve", "action.reject", "action.override", "action.record"], fun _ w e => match e with
               | .approved _ _ k _ | .rejected _ _ k _ | .overridden _ _ k _ | .recorded _ _ k _ _ _ => noted w "action" k | _ => true⟩,
            ⟨"only_opener_can_name_overriders", ["overrider.name"], fun v _ e => match e with
               | .overriderNamed a .. => v.opener == some a | _ => true⟩,
            ⟨"overrider_must_not_be_the_opener", ["overrider.name"], fun v _ e => match e with
               | .overriderNamed _ _ x _ => v.opener != some x | _ => true⟩,
            ⟨"overrider_is_named_once", ["overrider.name"], fun _ w e => match e with
               | .overriderNamed _ _ x _ => !w.contains ("overrider", "", x) | _ => true⟩,
            ⟨"only_overriders_can_override", ["action.override"], fun _ w e => match e with
               | .overridden a .. => w.contains ("overrider", "", a) | _ => true⟩,
            ⟨"asker_must_not_override", ["action.override"], fun _ w e => match e with
               | .overridden a _ k _ => !w.contains ("action", k, a) | _ => true⟩,
            ⟨"only_a_rejection_is_overridden", ["action.override"], fun _ w e => match e with
               | .overridden _ _ k _ => noted w "rejected" k | _ => true⟩,
            ⟨"action_is_overridden_once", ["action.override"], fun _ w e => match e with
               | .overridden _ _ k _ => !noted w "overridden" k | _ => true⟩,
            ⟨"override_comes_before_the_record", ["action.override"], fun _ w e => match e with
               | .overridden _ _ k _ => !noted w "recorded" k | _ => true⟩,
            ⟨"only_opener_or_evaluator_can_answer", ["action.approve", "action.reject"], fun v w e => match e with
               | .approved a .. | .rejected a .. => v.opener == some a || w.contains ("evaluator", "", a) | _ => true⟩,
            ⟨"asker_must_not_answer", ["action.approve", "action.reject"], fun _ w e => match e with
               | .approved a _ k _ | .rejected a _ k _ => !w.contains ("action", k, a) | _ => true⟩,
            ⟨"only_the_asker_records", ["action.record"], fun _ w e => match e with
               | .recorded a _ k _ _ _ => w.contains ("action", k, a) | _ => true⟩,
            ⟨"result_url_must_be_pinned", ["action.record"], fun _ _ e => match e with
               | .recorded _ _ _ _ r _ => pinned r | _ => true⟩,
            ⟨"an_attempt_must_be_allowed", ["action.record"], fun _ w e => match e with
               | .recorded _ _ k o _ _ => o == "not_run" || mayRun w k | _ => true⟩,
            ⟨"action_is_recorded_once", ["action.record"], fun _ w e => match e with
               | .recorded _ _ k _ _ _ => !noted w "recorded" k | _ => true⟩,
            ⟨"action_is_answered_once", ["action.approve", "action.reject"], fun _ w e => match e with
               | .approved _ _ k _ | .rejected _ _ k _ => !answered w k | _ => true⟩]

end Action
