-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Tasks.Layer

/-!
# The tasks layer's guarantees

Each holds of every valid log of the layer (`ValidX`), and follows from the rules that held when its events were
accepted (`ValidX.holdsNamed`), from the core's opener (`v.opener`), and from the core's theorems through `h.cores`.
Since every permission here rests on the opener, "nobody creates work but the opener" (`tasks_opened_by_opener`) and
"nobody assigns but the opener" (`assignees_named_by_opener`) are theorems of this layer, inherited by every layer on
top of it (`tests/tower`).
-/

namespace Tasks
open Provenstream Provenstream.Layer

/-! ## What the memory reads: the notes of the stream's task events -/

theorem foldl_addNotes (past : List TaskEvent) (st : List Note) : past.foldl addNotes st = st ++ past.flatMap notes := by
  induction past generalizing st with
  | nil => simp
  | cons e es ih => simp [ih, addNotes, List.append_assoc]

/-- What the layer's rules read of the stream's task events is their notes, in order. -/
@[simp] theorem read_notes (past : List TaskEvent) : past.foldl addNotes [] = past.flatMap notes := by
  simp [foldl_addNotes]

theorem noted_iff {past : List TaskEvent} {what k : String} :
    noted (past.flatMap notes) what k = true ↔ ∃ e ∈ past, ∃ q, (what, k, q) ∈ notes e := by
  simp only [noted, List.any_eq_true, List.mem_flatMap, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨f, k', q⟩, ⟨e, he, hn⟩, rfl, rfl⟩; exact ⟨e, he, q, hn⟩
  · rintro ⟨e, he, q, hn⟩; exact ⟨_, ⟨e, he, hn⟩, rfl, rfl⟩

theorem notes_cases {e : TaskEvent} {what k q : String} (h : (what, k, q) ∈ notes e) :
    (what = "task" ∧ q = "" ∧ ∃ a t p m, e = .opened a t k p m) ∨
    (what = "assigned" ∧ ∃ a t m, e = .assigned a t k q m) ∨
    (what = "completed" ∧ q = "" ∧ ∃ a t m, e = .completed a t k m) := by
  cases e <;> simp_all [notes]

/-- A note of the stream's task events is a note of a task event of that stream in the log. -/
theorem noted_mem {log : tasks.XLog} {t : Id} {what k : String} (h : noted ((evs log t).flatMap notes) what k = true) :
    ∃ e q, .inr e ∈ log ∧ tasks.evStream e = t ∧ (what, k, q) ∈ notes e := by
  obtain ⟨e, he, q, hn⟩ := noted_iff.mp h
  exact ⟨e, q, (mem_evs.mp he).1, (mem_evs.mp he).2, hn⟩

/-! ## Who opens, who assigns, who completes -/

/-- **Nobody creates work but the opener**: every `task.open` in a valid log is by the stream's opener. -/
theorem tasks_opened_by_opener {pre post : tasks.XLog} {a t k : Id} {p : Option Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.opened a t k p m) :: post)) : Past.opener (cores pre) t = some a := by
  have := h.holdsNamed "only_opener_can_open_tasks"
  dsimp only at this
  simpa using this

/-- **Nobody assigns but the opener**: every `task.assign` in a valid log is by the stream's opener, so every assignee
was named by the opener. -/
theorem assignees_named_by_opener {pre post : tasks.XLog} {a t k q : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.assigned a t k q m) :: post)) : Past.opener (cores pre) t = some a := by
  have := h.holdsNamed "only_opener_can_assign"
  dsimp only at this
  simpa using this

/-- **A task is completed only by its assignee**: before every `task.complete` by `a` in a valid log, the task was
assigned to `a` on the stream, by the stream's opener. -/
theorem completed_by_assignee {pre post : tasks.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.completed a t k m) :: post)) :
    ∃ o m', (.inr (TaskEvent.assigned o t k a m') : tasks.XEv) ∈ pre ∧ Past.opener (cores pre) t = some o := by
  have := h.holdsNamed "only_assignee_can_finish"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk, List.contains_iff_mem, List.mem_flatMap] at this
  obtain ⟨e, he, hn⟩ := this
  obtain ⟨hm, hs⟩ := mem_evs.mp he
  rcases notes_cases hn with ⟨hw, -⟩ | ⟨-, o, t', m', rfl⟩ | ⟨hw, -⟩
  · exact absurd hw (by decide)
  · simp only [Commands.evStream_mk] at hs
    subst hs
    obtain ⟨p1, p2, rfl⟩ := List.append_of_mem hm
    have hv : ValidX (p1 ++ .inr (TaskEvent.assigned o t' k a m') :: (p2 ++ .inr (.completed a t' k m) :: post)) := by
      simpa [List.append_assoc] using h
    have ho := assignees_named_by_opener hv
    refine ⟨o, m', hm, ?_⟩
    simpa [cores] using opener_stays ho (cores (.inr (TaskEvent.assigned o t' k a m') :: p2))
  · exact absurd hw (by decide)

/-! ## Each step once, in order -/

/-- A task is opened at most once per stream: its id is new when it is opened. -/
theorem opened_once {pre post : tasks.XLog} {a t k : Id} {p : Option Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.opened a t k p m) :: post)) :
    noted ((evs pre t).flatMap notes) "task" k = false := by
  have := h.holdsNamed "task_id_must_be_new"
  dsimp only at this
  simpa using this

/-- A task assigned was opened before. -/
theorem assigned_after_open {pre post : tasks.XLog} {a t k q : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.assigned a t k q m) :: post)) :
    ∃ a' p' m', (.inr (TaskEvent.opened a' t k p' m') : tasks.XEv) ∈ pre := by
  have := h.holdsNamed "task_must_exist"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk] at this
  obtain ⟨e, q', hm, hs, hn⟩ := noted_mem this
  rcases notes_cases hn with ⟨-, -, a', t', p', m', rfl⟩ | ⟨hw, -⟩ | ⟨hw, -⟩
  · simp only [Commands.evStream_mk] at hs; subst hs; exact ⟨a', p', m', hm⟩
  · exact absurd hw (by decide)
  · exact absurd hw (by decide)

/-- A task is assigned at most once. -/
theorem assigned_once {pre post : tasks.XLog} {a t k q : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.assigned a t k q m) :: post)) :
    noted ((evs pre t).flatMap notes) "assigned" k = false := by
  have := h.holdsNamed "task_is_assigned_once"
  dsimp only at this
  simpa using this

/-- A task completed was opened before. -/
theorem completed_after_open {pre post : tasks.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.completed a t k m) :: post)) :
    ∃ a' p' m', (.inr (TaskEvent.opened a' t k p' m') : tasks.XEv) ∈ pre := by
  have := h.holdsNamed "task_must_exist"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk] at this
  obtain ⟨e, q', hm, hs, hn⟩ := noted_mem this
  rcases notes_cases hn with ⟨-, -, a', t', p', m', rfl⟩ | ⟨hw, -⟩ | ⟨hw, -⟩
  · simp only [Commands.evStream_mk] at hs; subst hs; exact ⟨a', p', m', hm⟩
  · exact absurd hw (by decide)
  · exact absurd hw (by decide)

/-- A task is completed at most once. -/
theorem completed_once {pre post : tasks.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.completed a t k m) :: post)) :
    noted ((evs pre t).flatMap notes) "completed" k = false := by
  have := h.holdsNamed "task_is_completed_once"
  dsimp only at this
  simpa using this

/-! ## A child task and its parent -/

/-- **A child's parent is an earlier task of the same stream**: the `parent_task_id` of a task names a task whose
`task.opened` is on the same stream and was accepted before the child (the rule `parent_task_must_exist`). -/
theorem parent_is_earlier_task {pre post : tasks.XLog} {a t k p : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.opened a t k (some p) m) :: post)) :
    ∃ a' p' m', (.inr (TaskEvent.opened a' t p p' m') : tasks.XEv) ∈ pre := by
  have := h.holdsNamed "parent_task_must_exist"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk] at this
  obtain ⟨e, q', hm, hs, hn⟩ := noted_mem this
  rcases notes_cases hn with ⟨-, -, a', t', p', m', rfl⟩ | ⟨hw, -⟩ | ⟨hw, -⟩
  · simp only [Commands.evStream_mk] at hs; subst hs; exact ⟨a', p', m', hm⟩
  · exact absurd hw (by decide)
  · exact absurd hw (by decide)

/-- **No task is its own parent**: its id is new when it is opened (`task_id_must_be_new`), and its parent was opened
before it (`parent_task_must_exist`). -/
theorem parent_ne_self {pre post : tasks.XLog} {a t k p : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.opened a t k (some p) m) :: post)) : p ≠ k := by
  have hp := h.holdsNamed "parent_task_must_exist"
  dsimp only at hp
  have hk := opened_once h
  rintro rfl
  simp_all

/-- **The parent changes no other rule**: every rule of the layer but `parent_task_must_exist` holds of a child exactly
as of the same task without a parent, so every theorem drawn from those rules holds of children as of top-level
tasks. -/
theorem rules_ignore_parent (v : View) (w : List Note) (a t k : Id) (p : Option Id) (m : Meta) :
    ∀ r ∈ tasks.rules, r.reason ≠ "parent_task_must_exist" →
      r.holds v w (.opened a t k p m) = r.holds v w (.opened a t k none m) := by
  intro r hr hn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact absurd rfl hn

/-! ## The core's guarantees, here -/

/-- Only the opener closes a stream of tasks (`Layer.ValidX.close_by_opener`). -/
theorem tasks_close_by_opener {pre post : tasks.XLog} {a t : Id} {m : Meta}
    (h : ValidX (pre ++ .inl (Event.streamClosed a t m) :: post)) : Past.opener (cores pre) t = some a :=
  h.close_by_opener

/-- Nothing, of the core or of the layer, is appended to a stream after its close (`Layer.ValidX.close_final`). -/
theorem tasks_close_final {pre mid post : tasks.XLog} {a t : Id} {m : Meta} {x : tasks.XEv}
    (h : ValidX (pre ++ .inl (Event.streamClosed a t m) :: mid ++ x :: post)) : streamX x ≠ t := h.close_final

end Tasks
