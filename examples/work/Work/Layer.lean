-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Provenstream.Interface

/-!
# Work: a layer on the core

A basic task system. The stream's opener creates a work item and assigns it; the assignee asks any number of
preparers to prepare it, each of whom replies with its preparation, and may reply again while the item is undecided
(a later reply supersedes the preparer's earlier one); the assignee then completes or cancels the item, once.

- `work.create {stream_id, work_id, meta?}` → `work.created`: the opener creates an item, its id new on the stream.
- `work.assign {stream_id, work_id, assignee_id, meta?}` → `work.assigned`: the opener assigns an item to any
  principal (itself included), once.
- `work.ask {stream_id, work_id, preparer_id, meta?}` → `work.asked`: the assignee asks a principal other than itself
  to prepare the item, each once, while the item is undecided.
- `work.reply {stream_id, work_id, meta?}` → `work.replied`: an asked preparer replies with its preparation (in
  `meta`), while the item is undecided. It may reply again, so a composer can post a later screen; a reader takes a
  preparer's last reply as its preparation. A reply decides nothing.
- `work.complete {stream_id, work_id, meta?}` → `work.completed`, `work.cancel {stream_id, work_id, meta?}` →
  `work.cancelled`: the assignee decides the item, once; nothing about the item follows.

Every permission rests on the core's `v.opener`: nobody creates or assigns work but the opener, the assignee is whom
the opener named, the preparers are whom the assignee asked. The memory is the notes the events make (`notes`), in
order: `("work", k, "")`, `("assigned", k, assignee)`, `("asked", k, preparer)`, `("replied", k, preparer)`,
`("completed", k, "")`, `("cancelled", k, "")`. A read of a stream adds `work`, `assigned` (`{work_id, assignee_id}`),
`asked`, `replied` (`{work_id, preparer_id}`), `completed` and `cancelled`.
-/

namespace Work
open Provenstream Provenstream.Layer Provenstream.Wire

inductive WorkCommand where
  | create (stream work : Id) («meta» : Meta)
  | assign (stream work assignee : Id) («meta» : Meta)
  | ask (stream work preparer : Id) («meta» : Meta)
  | reply (stream work : Id) («meta» : Meta)
  | complete (stream work : Id) («meta» : Meta)
  | cancel (stream work : Id) («meta» : Meta)
  deriving DecidableEq

inductive WorkEvent where
  | created (actor stream work : Id) («meta» : Meta)
  | assigned (actor stream work assignee : Id) («meta» : Meta)
  | asked (actor stream work preparer : Id) («meta» : Meta)
  | replied (actor stream work : Id) («meta» : Meta)
  | completed (actor stream work : Id) («meta» : Meta)
  | cancelled (actor stream work : Id) («meta» : Meta)
  deriving DecidableEq

/-- A note a work event makes: what (`work`, `assigned`, `asked`, `replied`, `completed`, `cancelled`),
the item, and whom (the assignee or preparer, or `""`). -/
abbrev Note := String × String × String

def notes : WorkEvent → List Note
  | .created _ _ k _ => [("work", k, "")]
  | .assigned _ _ k q _ => [("assigned", k, q)]
  | .asked _ _ k p _ => [("asked", k, p)]
  | .replied a _ k _ => [("replied", k, a)]
  | .completed _ _ k _ => [("completed", k, "")]
  | .cancelled _ _ k _ => [("cancelled", k, "")]

/-- The memory's step: the event's notes, appended. -/
def addNotes (st : List Note) (e : WorkEvent) : List Note := st ++ notes e

/-- Some note says `what` of item `k`. -/
def noted (w : List Note) (what k : String) : Bool := w.any fun n => n.1 == what && n.2.1 == k

/-- The item `k` is decided: completed or cancelled. -/
def decided (w : List Note) (k : String) : Bool := noted w "completed" k || noted w "cancelled" k

/-- The items some note says `what` of, in order. -/
def itemsOf (w : List Note) (what : String) : List String := w.filterMap fun n => if n.1 == what then some n.2.1 else none

/-- The item and principal of each note saying `what`, as `{work_id, <who>_id}`. -/
def pairsOf (w : List Note) (what who : String) : J :=
  .arr (w.filterMap fun n => if n.1 == what then some (.obj [("work_id", .str n.2.1), (who, .str n.2.2)]) else none)

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

abbrev work : Layer where
  Cmd := WorkCommand
  Ev := WorkEvent
  toRequest
    | .created a t k m => (a, .create t k m)
    | .assigned a t k q m => (a, .assign t k q m)
    | .asked a t k p m => (a, .ask t k p m)
    | .replied a t k m => (a, .reply t k m)
    | .completed a t k m => (a, .complete t k m)
    | .cancelled a t k m => (a, .cancel t k m)
  ofRequest
    | (a, .create t k m) => .created a t k m
    | (a, .assign t k q m) => .assigned a t k q m
    | (a, .ask t k p m) => .asked a t k p m
    | (a, .reply t k m) => .replied a t k m
    | (a, .complete t k m) => .completed a t k m
    | (a, .cancel t k m) => .cancelled a t k m
  stream | .create t .. | .assign t .. | .ask t .. | .reply t .. | .complete t .. | .cancel t .. => t
  schema := [{ name := "work.create", event := "work.created", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("work_id", .uuid), ("meta", .metaOpt)] },
             { name := "work.assign", event := "work.assigned", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("work_id", .uuid), ("assignee_id", .uuid), ("meta", .metaOpt)] },
             { name := "work.ask", event := "work.asked", who := some "the item's assignee",
               fields := [("stream_id", .uuid), ("work_id", .uuid), ("preparer_id", .uuid), ("meta", .metaOpt)] },
             { name := "work.reply", event := "work.replied", who := some "a preparer the assignee asked",
               fields := [("stream_id", .uuid), ("work_id", .uuid), ("meta", .metaOpt)] },
             { name := "work.complete", event := "work.completed", who := some "the item's assignee",
               fields := [("stream_id", .uuid), ("work_id", .uuid), ("meta", .metaOpt)] },
             { name := "work.cancel", event := "work.cancelled", who := some "the item's assignee",
               fields := [("stream_id", .uuid), ("work_id", .uuid), ("meta", .metaOpt)] }]
  toVals
    | .create t k m => ("work.create", [.s t, .s k, .m m])
    | .assign t k q m => ("work.assign", [.s t, .s k, .s q, .m m])
    | .ask t k p m => ("work.ask", [.s t, .s k, .s p, .m m])
    | .reply t k m => ("work.reply", [.s t, .s k, .m m])
    | .complete t k m => ("work.complete", [.s t, .s k, .m m])
    | .cancel t k m => ("work.cancel", [.s t, .s k, .m m])
  ofVals
    | "work.create", [.s t, .s k, .m m] => some (.create t k m)
    | "work.assign", [.s t, .s k, .s q, .m m] => some (.assign t k q m)
    | "work.ask", [.s t, .s k, .s p, .m m] => some (.ask t k p m)
    | "work.reply", [.s t, .s k, .m m] => some (.reply t k m)
    | "work.complete", [.s t, .s k, .m m] => some (.complete t k m)
    | "work.cancel", [.s t, .s k, .m m] => some (.cancel t k m)
    | _, _ => none
  memory := foldMemory [] addNotes notesToJ notesFromJ notesFromJ_toJ
  readJ st := [("work", .arr ((itemsOf st "work").map .str)),
               ("assigned", pairsOf st "assigned" "assignee_id"),
               ("asked", pairsOf st "asked" "preparer_id"),
               ("replied", pairsOf st "replied" "preparer_id"),
               ("completed", .arr ((itemsOf st "completed").map .str)),
               ("cancelled", .arr ((itemsOf st "cancelled").map .str))]
  rules := [⟨"only_opener_can_create", ["work.create"], fun v _ e => match e with
               | .created a .. => v.opener == some a | _ => true⟩,
            ⟨"work_id_must_be_new", ["work.create"], fun _ w e => match e with
               | .created _ _ k _ => !noted w "work" k | _ => true⟩,
            ⟨"only_opener_can_assign", ["work.assign"], fun v _ e => match e with
               | .assigned a .. => v.opener == some a | _ => true⟩,
            ⟨"work_must_exist", ["work.assign", "work.ask", "work.reply", "work.complete", "work.cancel"],
             fun _ w e => match e with
               | .assigned _ _ k _ _ | .asked _ _ k _ _ | .replied _ _ k _ | .completed _ _ k _
               | .cancelled _ _ k _ => noted w "work" k
               | _ => true⟩,
            ⟨"work_is_assigned_once", ["work.assign"], fun _ w e => match e with
               | .assigned _ _ k _ _ => !noted w "assigned" k | _ => true⟩,
            ⟨"only_assignee_can_ask", ["work.ask"], fun _ w e => match e with
               | .asked a _ k _ _ => w.contains ("assigned", k, a) | _ => true⟩,
            ⟨"only_asked_preparers_can_reply", ["work.reply"], fun _ w e => match e with
               | .replied a _ k _ => w.contains ("asked", k, a) | _ => true⟩,
            ⟨"only_assignee_can_decide", ["work.complete", "work.cancel"], fun _ w e => match e with
               | .completed a _ k _ | .cancelled a _ k _ => w.contains ("assigned", k, a) | _ => true⟩,
            ⟨"work_must_be_undecided", ["work.ask", "work.reply"], fun _ w e => match e with
               | .asked _ _ k _ _ | .replied _ _ k _ => !decided w k | _ => true⟩,
            ⟨"preparer_must_not_be_the_assignee", ["work.ask"], fun _ _ e => match e with
               | .asked a _ _ p _ => a != p | _ => true⟩,
            ⟨"preparer_is_asked_once", ["work.ask"], fun _ w e => match e with
               | .asked _ _ k p _ => !w.contains ("asked", k, p) | _ => true⟩,
            ⟨"work_is_decided_once", ["work.complete", "work.cancel"], fun _ w e => match e with
               | .completed _ _ k _ | .cancelled _ _ k _ => !decided w k | _ => true⟩]

end Work
