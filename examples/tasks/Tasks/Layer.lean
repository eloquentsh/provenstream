-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Provenstream.Interface

/-!
# Tasks: a layer on the core

- `task.open {stream_id, task_id, parent_task_id?, meta?}` → `task.opened`: the stream's opener opens a task, its id new
  on the stream. `parent_task_id`, when given (kind `uuid?`), is the parent's own `task_id`: a task already opened on
  the same stream (`parent_task_must_exist`).
- `task.assign {stream_id, task_id, assignee_id, meta?}` → `task.assigned`: the opener assigns an open task to any
  principal, once.
- `task.complete {stream_id, task_id, meta?}` → `task.completed`: the task's assignee completes it, once (an unassigned
  task cannot be completed: `only_assignee_can_finish`).

Every permission rests on the core's `v.opener`: nobody opens or assigns work but the opener, and nobody completes it
but whom the opener named. The memory is the notes the events make (`notes`), in order: `("task", k, "")`,
`("assigned", k, assignee)`, `("completed", k, "")`. It is what the layer exposes to a layer above (`tests/tower`), and
a read of a stream adds `tasks`, `assigned` (`{task_id, assignee_id}`) and `completed`.
-/

namespace Tasks
open Provenstream Provenstream.Layer Provenstream.Wire

inductive TaskCommand where
  | open (stream task : Id) (parent : Option Id) («meta» : Meta)
  | assign (stream task assignee : Id) («meta» : Meta)
  | complete (stream task : Id) («meta» : Meta)
  deriving DecidableEq

inductive TaskEvent where
  | opened (actor stream task : Id) (parent : Option Id) («meta» : Meta)
  | assigned (actor stream task assignee : Id) («meta» : Meta)
  | completed (actor stream task : Id) («meta» : Meta)
  deriving DecidableEq

/-- A note a task event makes: what (`task`, `assigned`, `completed`), the task, and whom (the assignee, or `""`). -/
abbrev Note := String × String × String

def notes : TaskEvent → List Note
  | .opened _ _ k _ _ => [("task", k, "")]
  | .assigned _ _ k q _ => [("assigned", k, q)]
  | .completed _ _ k _ => [("completed", k, "")]

/-- The memory's step: the event's notes, appended. -/
def addNotes (st : List Note) (e : TaskEvent) : List Note := st ++ notes e

/-- Some note says `what` of task `k`. -/
def noted (w : List Note) (what k : String) : Bool := w.any fun n => n.1 == what && n.2.1 == k

/-- The tasks the notes say are completed, in order. -/
def completedTasks (w : List Note) : List String := w.filterMap fun n => if n.1 == "completed" then some n.2.1 else none

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

abbrev tasks : Layer where
  Cmd := TaskCommand
  Ev := TaskEvent
  toRequest
    | .opened a t k p m => (a, .open t k p m)
    | .assigned a t k q m => (a, .assign t k q m)
    | .completed a t k m => (a, .complete t k m)
  ofRequest
    | (a, .open t k p m) => .opened a t k p m
    | (a, .assign t k q m) => .assigned a t k q m
    | (a, .complete t k m) => .completed a t k m
  stream | .open t .. | .assign t .. | .complete t .. => t
  schema := [{ name := "task.open", event := "task.opened", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("task_id", .uuid), ("parent_task_id", .uuidOpt), ("meta", .metaOpt)] },
             { name := "task.assign", event := "task.assigned", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("task_id", .uuid), ("assignee_id", .uuid), ("meta", .metaOpt)] },
             { name := "task.complete", event := "task.completed", who := some "the task's assignee",
               fields := [("stream_id", .uuid), ("task_id", .uuid), ("meta", .metaOpt)] }]
  toVals
    | .open t k p m => ("task.open", [.s t, .s k, .uo p, .m m])
    | .assign t k q m => ("task.assign", [.s t, .s k, .s q, .m m])
    | .complete t k m => ("task.complete", [.s t, .s k, .m m])
  ofVals
    | "task.open", [.s t, .s k, .uo p, .m m] => some (.open t k p m)
    | "task.assign", [.s t, .s k, .s q, .m m] => some (.assign t k q m)
    | "task.complete", [.s t, .s k, .m m] => some (.complete t k m)
    | _, _ => none
  memory := foldMemory [] addNotes notesToJ notesFromJ notesFromJ_toJ
  readJ st := [("tasks", .arr (st.filterMap fun n => if n.1 == "task" then some (.str n.2.1) else none)),
               ("assigned", .arr (st.filterMap fun n => if n.1 == "assigned" then
                  some (.obj [("task_id", .str n.2.1), ("assignee_id", .str n.2.2)]) else none)),
               ("completed", .arr ((completedTasks st).map .str))]
  rules := [⟨"only_opener_can_open_tasks", ["task.open"], fun v _ e => match e with
               | .opened a .. => v.opener == some a | _ => true⟩,
            ⟨"task_id_must_be_new", ["task.open"], fun _ w e => match e with
               | .opened _ _ k _ _ => !noted w "task" k | _ => true⟩,
            ⟨"parent_task_must_exist", ["task.open"], fun _ w e => match e with
               | .opened _ _ _ (some p) _ => noted w "task" p | _ => true⟩,
            ⟨"only_opener_can_assign", ["task.assign"], fun v _ e => match e with
               | .assigned a .. => v.opener == some a | _ => true⟩,
            ⟨"task_must_exist", ["task.assign", "task.complete"], fun _ w e => match e with
               | .assigned _ _ k _ _ | .completed _ _ k _ => noted w "task" k | _ => true⟩,
            ⟨"task_is_assigned_once", ["task.assign"], fun _ w e => match e with
               | .assigned _ _ k _ _ => !noted w "assigned" k | _ => true⟩,
            ⟨"only_assignee_can_finish", ["task.complete"], fun _ w e => match e with
               | .completed a _ k _ => w.contains ("assigned", k, a) | _ => true⟩,
            ⟨"task_is_completed_once", ["task.complete"], fun _ w e => match e with
               | .completed _ _ k _ => !noted w "completed" k | _ => true⟩]

end Tasks
