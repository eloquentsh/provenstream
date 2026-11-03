-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Tasks.Layer

/-!
# Layer B: reviews, on layer A (`tasks.toBase`)

`review.approve {stream_id, task_id, meta?}` → `review.approved`: the stream's opener approves a task that layer A
says is completed, once. Its rules read the core's view and what layer A exposes (`v.1`, `v.2`: the notes of the
stream's task events). One guard on the core's `stream.close`, two levels down: a stream is not closed while one of
its tasks is completed and not approved (`completed_tasks_must_be_approved_before_close`). A guard can only refuse
more, so the core's rules come first, and every core and layer-A guarantee holds at the top.
-/

namespace Tower
open Provenstream Provenstream.Layer Tasks

inductive ReviewCommand where
  | approve (stream task : Id) («meta» : Meta)
  deriving DecidableEq

inductive ReviewEvent where
  | approved (actor stream task : Id) («meta» : Meta)
  deriving DecidableEq

/-- An approval states that its task is approved. -/
def reviewMarks : ReviewEvent → List Fact
  | .approved _ _ k _ => [("approved", k)]

abbrev reviews : Layer tasks.toBase where
  Cmd := ReviewCommand
  Ev := ReviewEvent
  toRequest | .approved a t k m => (a, .approve t k m)
  ofRequest | (a, .approve t k m) => .approved a t k m
  stream | .approve t .. => t
  schema := [{ name := "review.approve", event := "review.approved", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("task_id", .uuid), ("meta", .metaOpt)] }]
  toVals | .approve t k m => ("review.approve", [.s t, .s k, .m m])
  ofVals
    | "review.approve", [.s t, .s k, .m m] => some (.approve t k m)
    | _, _ => none
  memory := Memory.facts reviewMarks
  readJ st := [("approved", .arr ((factKeys st "approved").map .str))]
  rules := [⟨"only_opener_can_approve", ["review.approve"], fun v _ e => match e with
               | .approved a .. => v.1.opener == some a⟩,
            ⟨"task_must_be_completed", ["review.approve"], fun v _ e => match e with
               | .approved _ _ k _ => noted v.2 "completed" k⟩,
            ⟨"task_is_approved_once", ["review.approve"], fun _ w e => match e with
               | .approved _ _ k _ => !w "approved" k⟩]
  guards := [⟨"completed_tasks_must_be_approved_before_close", ["stream.close"], fun v w e => match e with
               | .inl (.streamClosed ..) => (completedTasks v.2).all (w "approved")
               | _ => true⟩]

end Tower
