-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Provenstream.Interface

/-!
# Action: a layer on the core

A gate in front of a browser. Reads of the page never reach this stream. Every other action is asked about here before it runs, and an
evaluator says whether it gets ready for the task or completes it. Getting ready is approved. Completing is rejected.

- `evaluator.name {stream_id, evaluator_id, meta?}` -> `evaluator.named`: the opener names an evaluator other than itself, once each.
- `action.evaluate {stream_id, action_id, context_url, page_url, mode, meta?}` -> `action.evaluated`: anyone asks about one action, its id
  new. `context_url` pins a file holding everything an evaluator reads. `page_url` pins the page as markdown, with the target marked, or
  is `none` for an action on no page. `mode` is `readonly` or `action_allowed`.
- `action.approve {stream_id, action_id, meta?}` -> `action.approved`, `action.reject {stream_id, action_id, meta?}` -> `action.rejected`:
  the opener or an evaluator answers, once. Whoever asked never answers.

An action may run once it has an answer: an approval in any mode, or a rejection in `action_allowed`, which overrides it. A read of a
stream names these in `runnable`. An action with no answer may not run, so an evaluator's opinion is always on the stream first.

An engine cannot see a page or fetch a URL, and it cannot stop a browser. It checks the form of the pin and nothing about the bytes.
Whoever reads the URL checks the bytes against the pin. A broker runs an action only when `runnable` names it.

The memory is the notes the events make: `("evaluator", "", e)`, `("action", k, asker)`, `("mode", k, mode)`, `("approved", k, who)` and
`("rejected", k, who)`.
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

/-- A page URL: a URL, or `none` for an action on no page, like opening a tab. -/
def validPageUrl (s : String) : Bool := s == "none" || validUrl s

def readonly : String := "readonly"
def actionAllowed : String := "action_allowed"
def validMode (s : String) : Bool := s == readonly || s == actionAllowed

def urlKind : Kind := .text "url" validUrl
def pageUrlKind : Kind := .text "page_url" validPageUrl
def modeKind : Kind := .text "mode" validMode

inductive ActionCommand where
  | nameEvaluator (stream evaluator : Id) («meta» : Meta)
  | evaluate (stream action : Id) (context page mode : String) («meta» : Meta)
  | approve (stream action : Id) («meta» : Meta)
  | reject (stream action : Id) («meta» : Meta)
  deriving DecidableEq

inductive ActionEvent where
  | evaluatorNamed (actor stream evaluator : Id) («meta» : Meta)
  | evaluated (actor stream action : Id) (context page mode : String) («meta» : Meta)
  | approved (actor stream action : Id) («meta» : Meta)
  | rejected (actor stream action : Id) («meta» : Meta)
  deriving DecidableEq

abbrev Note := String × String × String

def notes : ActionEvent → List Note
  | .evaluatorNamed _ _ e _ => [("evaluator", "", e)]
  | .evaluated a _ k _ _ f _ => [("action", k, a), ("mode", k, f)]
  | .approved a _ k _ => [("approved", k, a)]
  | .rejected a _ k _ => [("rejected", k, a)]

def addNotes (st : List Note) (e : ActionEvent) : List Note := st ++ notes e

def noted (w : List Note) (what k : String) : Bool := w.any fun n => n.1 == what && n.2.1 == k

def answered (w : List Note) (k : String) : Bool := noted w "approved" k || noted w "rejected" k

/-- The action may run: approved in any mode, or rejected in `action_allowed`, which overrides the rejection. No answer, no run. -/
def mayRun (w : List Note) (k : String) : Bool :=
  noted w "approved" k || (noted w "rejected" k && w.contains ("mode", k, actionAllowed))

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
    | .evaluated a t k c g f m => (a, .evaluate t k c g f m)
    | .approved a t k m => (a, .approve t k m)
    | .rejected a t k m => (a, .reject t k m)
  ofRequest
    | (a, .nameEvaluator t e m) => .evaluatorNamed a t e m
    | (a, .evaluate t k c g f m) => .evaluated a t k c g f m
    | (a, .approve t k m) => .approved a t k m
    | (a, .reject t k m) => .rejected a t k m
  stream | .nameEvaluator t .. | .evaluate t .. | .approve t .. | .reject t .. => t
  schema := [{ name := "evaluator.name", event := "evaluator.named", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("evaluator_id", .uuid), ("meta", .metaOpt)] },
             { name := "action.evaluate", event := "action.evaluated", who := some "anyone",
               fields := [("stream_id", .uuid), ("action_id", .uuid), ("context_url", urlKind), ("page_url", pageUrlKind), ("mode", modeKind), ("meta", .metaOpt)] },
             { name := "action.approve", event := "action.approved", who := some "the opener or an evaluator, never whoever asked",
               fields := [("stream_id", .uuid), ("action_id", .uuid), ("meta", .metaOpt)] },
             { name := "action.reject", event := "action.rejected", who := some "the opener or an evaluator, never whoever asked",
               fields := [("stream_id", .uuid), ("action_id", .uuid), ("meta", .metaOpt)] }]
  toVals
    | .nameEvaluator t e m => ("evaluator.name", [.s t, .s e, .m m])
    | .evaluate t k c g f m => ("action.evaluate", [.s t, .s k, .s c, .s g, .s f, .m m])
    | .approve t k m => ("action.approve", [.s t, .s k, .m m])
    | .reject t k m => ("action.reject", [.s t, .s k, .m m])
  ofVals
    | "evaluator.name", [.s t, .s e, .m m] => some (.nameEvaluator t e m)
    | "action.evaluate", [.s t, .s k, .s c, .s g, .s f, .m m] => some (.evaluate t k c g f m)
    | "action.approve", [.s t, .s k, .m m] => some (.approve t k m)
    | "action.reject", [.s t, .s k, .m m] => some (.reject t k m)
    | _, _ => none
  memory := foldMemory [] addNotes notesToJ notesFromJ notesFromJ_toJ
  readJ st := [("evaluators", .arr ((thirdOf st "evaluator").map .str)),
               ("actions", pairsOf st "action" "asker_id"),
               ("approved", pairsOf st "approved" "by"),
               ("rejected", pairsOf st "rejected" "by"),
               ("modes", pairsOf st "mode" "mode"),
               ("runnable", .arr ((runnable st).map .str))]
  rules := [⟨"only_opener_can_name_evaluators", ["evaluator.name"], fun v _ e => match e with
               | .evaluatorNamed a .. => v.opener == some a | _ => true⟩,
            ⟨"evaluator_must_not_be_the_opener", ["evaluator.name"], fun v _ e => match e with
               | .evaluatorNamed _ _ x _ => v.opener != some x | _ => true⟩,
            ⟨"evaluator_is_named_once", ["evaluator.name"], fun _ w e => match e with
               | .evaluatorNamed _ _ x _ => !w.contains ("evaluator", "", x) | _ => true⟩,
            ⟨"action_id_must_be_new", ["action.evaluate"], fun _ w e => match e with
               | .evaluated _ _ k .. => !noted w "action" k | _ => true⟩,
            ⟨"context_url_must_be_pinned", ["action.evaluate"], fun _ _ e => match e with
               | .evaluated _ _ _ c _ _ _ => pinned c | _ => true⟩,
            ⟨"page_url_must_be_pinned", ["action.evaluate"], fun _ _ e => match e with
               | .evaluated _ _ _ _ g _ _ => g == "none" || pinned g | _ => true⟩,
            ⟨"action_must_exist", ["action.approve", "action.reject"], fun _ w e => match e with
               | .approved _ _ k _ | .rejected _ _ k _ => noted w "action" k | _ => true⟩,
            ⟨"only_opener_or_evaluator_can_answer", ["action.approve", "action.reject"], fun v w e => match e with
               | .approved a .. | .rejected a .. => v.opener == some a || w.contains ("evaluator", "", a) | _ => true⟩,
            ⟨"asker_must_not_answer", ["action.approve", "action.reject"], fun _ w e => match e with
               | .approved a _ k _ | .rejected a _ k _ => !w.contains ("action", k, a) | _ => true⟩,
            ⟨"action_is_answered_once", ["action.approve", "action.reject"], fun _ w e => match e with
               | .approved _ _ k _ | .rejected _ _ k _ => !answered w k | _ => true⟩]

end Action
