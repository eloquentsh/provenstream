-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Action.Layer

/-!
# The action layer's guarantees

Each holds of every valid log of the layer, and follows from the rules that held when its events were accepted. An answer comes
only from the opener or a named evaluator, never from whoever asked, and an action gets one. `mayRun` says what a broker may run: no
answer means no run, and a rejection stops an action unless its mode is `action_allowed`. The engine cannot see whether a broker obeys, so
nothing here says what ran.
-/

namespace Action
open Provenstream Provenstream.Layer

theorem foldl_addNotes (past : List ActionEvent) (st : List Note) : past.foldl addNotes st = st ++ past.flatMap notes := by
  induction past generalizing st with
  | nil => simp
  | cons e es ih => simp [ih, addNotes, List.append_assoc]

@[simp] theorem read_notes (past : List ActionEvent) : past.foldl addNotes [] = past.flatMap notes := by
  simp [foldl_addNotes]

theorem mem_notes_evs {log : actions.XLog} {t : Id} {n : Note} (h : n ∈ (evs log t).flatMap notes) :
    ∃ e, .inr e ∈ log ∧ actions.evStream e = t ∧ n ∈ notes e := by
  obtain ⟨e, he, hn⟩ := List.mem_flatMap.mp h
  exact ⟨e, (mem_evs.mp he).1, (mem_evs.mp he).2, hn⟩

theorem noted_iff {w : List Note} {what k : String} : noted w what k = true ↔ ∃ q, (what, k, q) ∈ w := by
  simp only [noted, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨f, k', q⟩, hm, rfl, rfl⟩; exact ⟨q, hm⟩
  · rintro ⟨q, hm⟩; exact ⟨_, hm, rfl, rfl⟩

theorem evaluator_note {e : ActionEvent} {x : String} (h : ("evaluator", "", x) ∈ notes e) :
    ∃ a t m, e = .evaluatorNamed a t x m := by
  cases e <;> simp_all [notes] <;> (split at h <;> simp_all)

/-- A note naming an evaluator came from a naming in the log. -/
theorem named_of_contains {pre : actions.XLog} {t x : Id}
    (h : ((evs pre t).flatMap notes).contains ("evaluator", "", x) = true) :
    ∃ o m', (.inr (ActionEvent.evaluatorNamed o t x m') : actions.XEv) ∈ pre := by
  obtain ⟨e, hm, hs, hn⟩ := mem_notes_evs (List.contains_iff_mem.mp h)
  obtain ⟨o, t', m', rfl⟩ := evaluator_note hn
  simp only [Commands.evStream_mk] at hs
  subst hs
  exact ⟨o, m', hm⟩

/-- **Every evaluator is named by the opener.** -/
theorem every_evaluator_is_named_by_the_opener {pre post : actions.XLog} {a t x : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.evaluatorNamed a t x m) :: post)) : Past.opener (cores pre) t = some a := by
  have := h.holdsNamed "only_opener_can_name_evaluators"
  dsimp only at this
  simpa using this

/-- **No evaluator is the opener at its naming.** -/
theorem no_evaluator_is_the_opener {pre post : actions.XLog} {a t x : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.evaluatorNamed a t x m) :: post)) : Past.opener (cores pre) t ≠ some x := by
  have := h.holdsNamed "evaluator_must_not_be_the_opener"
  dsimp only at this
  simpa using this

/-- **An evaluator is named once.** -/
theorem an_evaluator_is_named_once {pre post : actions.XLog} {a t x : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.evaluatorNamed a t x m) :: post)) :
    ("evaluator", "", x) ∉ (evs pre t).flatMap notes := by
  have := h.holdsNamed "evaluator_is_named_once"
  dsimp only at this
  simpa using this

/-- **An action id is new when it is asked about.** -/
theorem an_action_id_is_new {pre post : actions.XLog} {a t k : Id} {c f : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.evaluated a t k c f m) :: post)) :
    noted ((evs pre t).flatMap notes) "action" k = false := by
  have := h.holdsNamed "action_id_must_be_new"
  dsimp only at this
  simpa using this

/-- **Every context URL is pinned.** The proof sees the form of the pin and never the bytes. -/
theorem every_context_url_is_pinned {pre post : actions.XLog} {a t k : Id} {c f : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.evaluated a t k c f m) :: post)) : pinned c = true := by
  have := h.holdsNamed "context_url_must_be_pinned"
  dsimp only at this
  simpa using this

/-- **An approval names an action that was asked about.** -/
theorem an_approval_names_an_action {pre post : actions.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.approved a t k m) :: post)) :
    noted ((evs pre t).flatMap notes) "action" k = true := by
  have := h.holdsNamed "action_must_exist"
  dsimp only at this
  simpa using this

/-- **A rejection names an action that was asked about.** -/
theorem a_rejection_names_an_action {pre post : actions.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.rejected a t k m) :: post)) :
    noted ((evs pre t).flatMap notes) "action" k = true := by
  have := h.holdsNamed "action_must_exist"
  dsimp only at this
  simpa using this

/-- **Every approval is by the opener or a named evaluator.** -/
theorem every_approval_is_by_the_opener_or_an_evaluator {pre post : actions.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.approved a t k m) :: post)) :
    Past.opener (cores pre) t = some a ∨ ∃ o m', (.inr (ActionEvent.evaluatorNamed o t a m') : actions.XEv) ∈ pre := by
  have := h.holdsNamed "only_opener_or_evaluator_can_answer"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk, Bool.or_eq_true] at this
  rcases this with ho | he
  · exact Or.inl (by simpa using ho)
  · exact Or.inr (named_of_contains he)

/-- **Every rejection is by the opener or a named evaluator.** -/
theorem every_rejection_is_by_the_opener_or_an_evaluator {pre post : actions.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.rejected a t k m) :: post)) :
    Past.opener (cores pre) t = some a ∨ ∃ o m', (.inr (ActionEvent.evaluatorNamed o t a m') : actions.XEv) ∈ pre := by
  have := h.holdsNamed "only_opener_or_evaluator_can_answer"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk, Bool.or_eq_true] at this
  rcases this with ho | he
  · exact Or.inl (by simpa using ho)
  · exact Or.inr (named_of_contains he)

/-- **Whoever asked never approves.** -/
theorem the_asker_never_approves {pre post : actions.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.approved a t k m) :: post)) :
    ("action", k, a) ∉ (evs pre t).flatMap notes := by
  have := h.holdsNamed "asker_must_not_answer"
  dsimp only at this
  simpa using this

/-- **Whoever asked never rejects.** -/
theorem the_asker_never_rejects {pre post : actions.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.rejected a t k m) :: post)) :
    ("action", k, a) ∉ (evs pre t).flatMap notes := by
  have := h.holdsNamed "asker_must_not_answer"
  dsimp only at this
  simpa using this

/-- **An action is answered once**: at an approval it has no answer. -/
theorem an_approved_action_had_no_answer {pre post : actions.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.approved a t k m) :: post)) :
    answered ((evs pre t).flatMap notes) k = false := by
  have := h.holdsNamed "action_is_answered_once"
  dsimp only at this
  simpa using this

/-- **An action is answered once**: at a rejection it has no answer. -/
theorem a_rejected_action_had_no_answer {pre post : actions.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.rejected a t k m) :: post)) :
    answered ((evs pre t).flatMap notes) k = false := by
  have := h.holdsNamed "action_is_answered_once"
  dsimp only at this
  simpa using this

/-- **A rejected action is never approved**: after a rejection, no approval of that action is accepted on the stream. -/
theorem a_rejected_action_is_never_approved {pre mid post : actions.XLog} {a b t k : Id} {m m' : Meta}
    (h : ValidX (pre ++ .inr (.rejected a t k m) :: mid ++ .inr (.approved b t k m') :: post)) : False := by
  have hn := an_approved_action_had_no_answer h
  have hm : ("rejected", k, a) ∈ (evs (pre ++ .inr (.rejected a t k m) :: mid) t).flatMap notes :=
    List.mem_flatMap.mpr ⟨ActionEvent.rejected a t k m, mem_evs.mpr ⟨by simp, rfl⟩, by simp [notes]⟩
  have hr : noted ((evs (pre ++ .inr (.rejected a t k m) :: mid) t).flatMap notes) "rejected" k = true := noted_iff.mpr ⟨a, hm⟩
  have ha : answered ((evs (pre ++ .inr (.rejected a t k m) :: mid) t).flatMap notes) k = true := by
    simp only [answered, hr, Bool.or_true]
  rw [ha] at hn
  exact absurd hn (by decide)

/-! ## What may run -/

/-- **An action with no answer may not run**, in any mode. -/
theorem no_answer_no_run {w : List Note} {k : String} (h : answered w k = false) : mayRun w k = false := by
  simp only [answered, Bool.or_eq_false_iff] at h
  simp [mayRun, h.1, h.2]

/-- **An approved action may run**, in any mode. -/
theorem an_approved_action_may_run {w : List Note} {k : String} (h : noted w "approved" k = true) : mayRun w k = true := by
  simp [mayRun, h]

/-- **Without `action_allowed`, a rejection stops the action**: an action that was not approved and whose mode is not noted as
`action_allowed` may not run. -/
theorem a_rejection_stops_the_action_without_action_allowed {w : List Note} {k : String} (ha : noted w "approved" k = false)
    (hm : w.contains ("mode", k, actionAllowed) = false) : mayRun w k = false := by
  unfold mayRun
  rw [ha, hm]
  simp

/-- **In `action_allowed`, a rejection is overridden**, and it stays on the stream. -/
theorem action_allowed_overrides_a_rejection {w : List Note} {k : String} (hr : noted w "rejected" k = true)
    (hm : w.contains ("mode", k, actionAllowed) = true) : mayRun w k = true := by
  unfold mayRun
  rw [hr, hm]
  simp

/-- **A mode is fixed when the action is asked about**: the only notes of a mode come from `action.evaluate`, and its id is new then. -/
theorem a_mode_note_is_an_evaluation {e : ActionEvent} {k q : String} (h : ("mode", k, q) ∈ notes e) :
    ∃ a t c m, e = .evaluated a t k c q m := by
  cases e <;> simp_all [notes]

/-! ## The core's guarantees, here -/

/-- **Only the opener closes the stream** (`Layer.ValidX.close_by_opener`). -/
theorem only_the_opener_closes_the_stream {pre post : actions.XLog} {a t : Id} {m : Meta}
    (h : ValidX (pre ++ .inl (Event.streamClosed a t m) :: post)) : Past.opener (cores pre) t = some a :=
  h.close_by_opener

/-- **Nothing follows a close** (`Layer.ValidX.close_final`). -/
theorem nothing_follows_a_close {pre mid post : actions.XLog} {a t : Id} {m : Meta} {x : actions.XEv}
    (h : ValidX (pre ++ .inl (Event.streamClosed a t m) :: mid ++ x :: post)) : streamX x ≠ t := h.close_final

end Action
