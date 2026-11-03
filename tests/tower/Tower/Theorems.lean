-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Tower.Reviews
import Tasks.Theorems

/-!
# The tower's guarantees: the core's, layer A's and layer B's, at the top

A valid log of the top service (`reviews.service`: core events, task events and review events) projects to a valid
log of layer A (`h.base`) and to a valid core log (`h.base.cores`). So the top level still proves the core's theorems,
through the chain, and layer A's theorems, one level down; and layer B's own rules and guard give its own.
-/

namespace Tower
open Provenstream Provenstream.Layer Tasks

/-- The core's events two levels down. -/
abbrev core2 (log : reviews.XLog) : Log := bases (bases log)

/-- What the reviews' rules read of the stream's review events. -/
def approvedIn (past : List ReviewEvent) (k : Id) : Bool := past.any fun e => (reviewMarks e).contains ("approved", k)

theorem mem_completedTasks {w : List Note} {k : String} : k ∈ completedTasks w ↔ ∃ q, ("completed", k, q) ∈ w := by
  simp only [completedTasks, List.mem_filterMap]
  constructor
  · rintro ⟨⟨f, k', q⟩, hm, h⟩
    by_cases hf : f = "completed"
    · subst hf; simp at h; subst h; exact ⟨q, hm⟩
    · simp [hf] at h
  · rintro ⟨q, hq⟩; exact ⟨_, hq, by simp⟩

/-! ## Layer B's own -/

/-- **Only the opener approves**: every `review.approve` in a valid log is by the stream's opener, as the core's events
two levels down say. -/
theorem approved_by_opener {pre post : reviews.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (ReviewEvent.approved a t k m) :: post)) : Past.opener (core2 pre) t = some a := by
  have := h.holdsNamed "only_opener_can_approve"
  dsimp only at this
  simpa using this

/-- **Only a completed task is approved**: before every approval of `k`, layer A's events say `k` was completed on the
stream. -/
theorem approved_completed {pre post : reviews.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (ReviewEvent.approved a t k m) :: post)) :
    ∃ a' m', (.inr (TaskEvent.completed a' t k m') : tasks.XEv) ∈ bases pre := by
  have := h.holdsNamed "task_must_be_completed"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk] at this
  obtain ⟨e, q, hm, hs, hn⟩ := noted_mem this
  rcases notes_cases hn with ⟨hw, -⟩ | ⟨hw, -⟩ | ⟨-, -, a', t', m', rfl⟩
  · exact absurd hw (by decide)
  · exact absurd hw (by decide)
  · simp only [Commands.evStream_mk] at hs; subst hs; exact ⟨a', m', hm⟩

/-- An approved task was completed by its assignee, whom the opener named (layer A's `completed_by_assignee`, one level
down). -/
theorem approved_completed_by_assignee {pre post : reviews.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (ReviewEvent.approved a t k m) :: post)) :
    ∃ b m' o m'', (.inr (TaskEvent.completed b t k m') : tasks.XEv) ∈ bases pre ∧
      (.inr (TaskEvent.assigned o t k b m'') : tasks.XEv) ∈ bases pre ∧ Past.opener (core2 pre) t = some o := by
  obtain ⟨b, m', hc⟩ := approved_completed h
  obtain ⟨p1, p2, hp⟩ := List.append_of_mem hc
  have hA : ValidX (bases (pre ++ .inr (ReviewEvent.approved a t k m) :: post)) := h.base
  have hA' : ValidX (p1 ++ .inr (TaskEvent.completed b t k m') :: (p2 ++ bases post)) := by
    simpa [hp, List.append_assoc] using hA
  obtain ⟨o, m'', ho, hop⟩ := completed_by_assignee hA'
  refine ⟨b, m', o, m'', hc, by rw [hp]; simp [ho], ?_⟩
  have := opener_stays hop (cores ((.inr (TaskEvent.completed b t k m') : tasks.XEv) :: p2))
  simpa [core2, cores, hp] using this

/-- **A stream closes only after its reviews**: at every close in a valid log, every task layer A's events say was
completed on the stream was approved before the close (the guard on the core's `stream.close`, two levels down). -/
theorem close_after_reviews {pre post : reviews.XLog} {a t : Id} {m : Meta}
    (h : ValidX (pre ++ .inl (.inl (Event.streamClosed a t m)) :: post)) {k : Id} {b : Id} {m' : Meta}
    (hc : (.inr (TaskEvent.completed b t k m') : tasks.XEv) ∈ bases pre) :
    ∃ a' m'', (.inr (ReviewEvent.approved a' t k m'') : reviews.XEv) ∈ pre := by
  have := h.guardHoldsNamed "completed_tasks_must_be_approved_before_close"
  dsimp only at this
  simp only [read_notes, List.all_eq_true] at this
  have hk : k ∈ completedTasks ((evs (bases pre) t).flatMap notes) :=
    mem_completedTasks.mpr ⟨"", List.mem_flatMap.mpr ⟨_, mem_evs.mpr ⟨hc, rfl⟩, by simp [notes]⟩⟩
  have ha := this k (by simpa using hk)
  simp only [Memory.facts_read, List.any_eq_true] at ha
  obtain ⟨e, he, hm⟩ := ha
  obtain ⟨hin, hs⟩ := mem_evs.mp he
  cases e with
  | approved a' t' k' m'' =>
    simp only [reviewMarks, List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq, Prod.mk.injEq,
      true_and] at hm
    simp only [Commands.evStream_mk] at hs
    subst hm; subst hs
    exact ⟨a', m'', hin⟩

/-! ## The core's and layer A's, at the top -/

/-- **The core's theorem at the top: only the opener closes**, through `h.base` (a valid log of layer A) and layer A's
`ValidX.close_by_opener`. -/
theorem tower_close_by_opener {pre post : reviews.XLog} {a t : Id} {m : Meta}
    (h : ValidX (pre ++ .inl (.inl (Event.streamClosed a t m)) :: post)) : Past.opener (core2 pre) t = some a := by
  have hA : ValidX (bases pre ++ .inl (Event.streamClosed a t m) :: bases post) := by simpa using h.base
  exact hA.close_by_opener

/-- **Layer A's theorem, one level down**: every `task.open` inside a valid top-level log is by the stream's opener. -/
theorem tower_tasks_opened_by_opener {log : reviews.XLog} (h : ValidX log) {pre post : tasks.XLog} {a t k : Id}
    {p : Option Id} {m : Meta} (hl : bases log = pre ++ .inr (.opened a t k p m) :: post) :
    Past.opener (cores pre) t = some a := by
  have hA : ValidX (bases log) := h.base
  rw [hl] at hA
  exact tasks_opened_by_opener hA

/-- **Layer A's parents, one level down**: the parent a `task.open` inside a valid top-level log names is a task opened
earlier on the same stream (`parent_is_earlier_task`). -/
theorem tower_parent_is_earlier_task {log : reviews.XLog} (h : ValidX log) {pre post : tasks.XLog} {a t k p : Id}
    {m : Meta} (hl : bases log = pre ++ .inr (.opened a t k (some p) m) :: post) :
    ∃ a' p' m', (.inr (TaskEvent.opened a' t p p' m') : tasks.XEv) ∈ pre := by
  have hA : ValidX (bases log) := h.base
  rw [hl] at hA
  exact parent_is_earlier_task hA

/-- **The core's admission at the top**: every review event is on an open, unclosed stream, by the core's events two
levels down (`ValidX.admitted`; admission composes, `toBase_admits`). -/
theorem approve_admitted {pre post : reviews.XLog} {x : ReviewEvent} (h : ValidX (pre ++ .inr x :: post)) :
    Past.opened (core2 pre) (reviews.evStream x) = true ∧ Past.closed (core2 pre) (reviews.evStream x) = false := by
  have : (Past.view (core2 pre) (reviews.evStream x)).admits (evActor (L := reviews) x) = none := h.admitted
  simpa using View.admits_none.mp this

/-- **Nothing after a close, at every level**: a core close two levels down ends the stream for every layer. -/
theorem tower_close_final {pre mid post : reviews.XLog} {a t : Id} {m : Meta} {x : ReviewEvent}
    (h : ValidX (pre ++ .inl (.inl (Event.streamClosed a t m)) :: mid ++ .inr x :: post)) :
    reviews.evStream x ≠ t := by
  intro hs
  have h' : ValidX ((pre ++ .inl (.inl (Event.streamClosed a t m)) :: mid) ++ .inr x :: post) := by
    simpa [List.append_assoc] using h
  have hc := (approve_admitted h').2
  rw [hs] at hc
  simp [core2, Past.closed, closes, List.any_append] at hc

end Tower
