-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Work.Layer

/-!
# The work layer's guarantees

Each holds of every valid log of the layer (`ValidX`), and follows from the rules that held when its events were
accepted (`ValidX.holdsNamed`), from the core's opener (`v.opener`), and from the core's theorems through `h.cores`.
Every permission rests on the opener: nobody creates or assigns work but the opener (`created_by_opener`,
`assigned_by_opener`), the assignee asks (`asked_by_assignee`), the asked reply (`replied_by_asked_preparer`), the
assignee decides (`completed_by_assignee`, `cancelled_by_assignee`), and nothing about an item follows its decision
(`decision_final`).
-/

namespace Work
open Provenstream Provenstream.Layer

/-! ## What the memory reads: the notes of the stream's work events -/

theorem foldl_addNotes (past : List WorkEvent) (st : List Note) : past.foldl addNotes st = st ++ past.flatMap notes := by
  induction past generalizing st with
  | nil => simp
  | cons e es ih => simp [ih, addNotes, List.append_assoc]

/-- What the layer's rules read of the stream's work events is their notes, in order. -/
@[simp] theorem read_notes (past : List WorkEvent) : past.foldl addNotes [] = past.flatMap notes := by
  simp [foldl_addNotes]

/-- A note of the stream's work events is a note of a work event of that stream in the log. -/
theorem mem_notes_evs {log : work.XLog} {t : Id} {n : Note} (h : n ∈ (evs log t).flatMap notes) :
    ∃ e, .inr e ∈ log ∧ work.evStream e = t ∧ n ∈ notes e := by
  obtain ⟨e, he, hn⟩ := List.mem_flatMap.mp h
  exact ⟨e, (mem_evs.mp he).1, (mem_evs.mp he).2, hn⟩

theorem noted_iff {w : List Note} {what k : String} : noted w what k = true ↔ ∃ q, (what, k, q) ∈ w := by
  simp only [noted, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨f, k', q⟩, hm, rfl, rfl⟩; exact ⟨q, hm⟩
  · rintro ⟨q, hm⟩; exact ⟨_, hm, rfl, rfl⟩

/-! What each kind of note says of the event that made it. -/

theorem work_note {e : WorkEvent} {k q : String} (h : ("work", k, q) ∈ notes e) : ∃ a t m, e = .created a t k m := by
  cases e <;> simp_all [notes]

theorem assigned_note {e : WorkEvent} {k q : String} (h : ("assigned", k, q) ∈ notes e) :
    ∃ a t m, e = .assigned a t k q m := by
  cases e <;> simp_all [notes]

theorem asked_note {e : WorkEvent} {k q : String} (h : ("asked", k, q) ∈ notes e) : ∃ a t m, e = .asked a t k q m := by
  cases e <;> simp_all [notes]

theorem replied_note {e : WorkEvent} {k q : String} (h : ("replied", k, q) ∈ notes e) : ∃ t m, e = .replied q t k m := by
  cases e <;> simp_all [notes]

theorem completed_note {e : WorkEvent} {k q : String} (h : ("completed", k, q) ∈ notes e) :
    ∃ a t m, e = .completed a t k m := by
  cases e <;> simp_all [notes]

theorem cancelled_note {e : WorkEvent} {k q : String} (h : ("cancelled", k, q) ∈ notes e) :
    ∃ a t m, e = .cancelled a t k m := by
  cases e <;> simp_all [notes]

/-- The stream's work events, before an event, were assigned `k` to `a` only by an `work.assigned` event in the log. -/
theorem assigned_of_contains {pre : work.XLog} {t k a : Id}
    (h : ((evs pre t).flatMap notes).contains ("assigned", k, a) = true) :
    ∃ o m', (.inr (WorkEvent.assigned o t k a m') : work.XEv) ∈ pre := by
  obtain ⟨e, hm, hs, hn⟩ := mem_notes_evs (List.contains_iff_mem.mp h)
  obtain ⟨o, t', m', rfl⟩ := assigned_note hn
  simp only [Commands.evStream_mk] at hs
  subst hs
  exact ⟨o, m', hm⟩

/-! ## Who creates, who assigns -/

/-- **Nobody creates work but the opener**: every `work.create` in a valid log is by the stream's opener. -/
theorem created_by_opener {pre post : work.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.created a t k m) :: post)) : Past.opener (cores pre) t = some a := by
  have := h.holdsNamed "only_opener_can_create"
  dsimp only at this
  simpa using this

/-- **Nobody assigns work but the opener**: every `work.assign` in a valid log is by the stream's opener, so every
assignee was named by the opener. -/
theorem assigned_by_opener {pre post : work.XLog} {a t k q : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.assigned a t k q m) :: post)) : Past.opener (cores pre) t = some a := by
  have := h.holdsNamed "only_opener_can_assign"
  dsimp only at this
  simpa using this

/-- An assignment of `k` to `a` in a valid log was made by the stream's opener, as the log before it says. -/
theorem assignment_by_opener {pre post : work.XLog} {o t k a : Id} {m' : Meta}
    (h : ValidX (pre ++ post)) (hm : (.inr (WorkEvent.assigned o t k a m') : work.XEv) ∈ pre) :
    Past.opener (cores pre) t = some o := by
  obtain ⟨p1, p2, rfl⟩ := List.append_of_mem hm
  have hv : ValidX (p1 ++ .inr (WorkEvent.assigned o t k a m') :: (p2 ++ post)) := by
    simpa [List.append_assoc] using h
  have ho := assigned_by_opener hv
  simpa [cores] using opener_stays ho (cores (.inr (WorkEvent.assigned o t k a m') :: p2))

/-! ## The assignee asks, the asked reply, the assignee decides -/

/-- **Only the assignee asks for preparations**: before every `work.ask` by `a` on item `k`, the item was assigned to
`a` on the stream, by the stream's opener. -/
theorem asked_by_assignee {pre post : work.XLog} {a t k p : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.asked a t k p m) :: post)) :
    ∃ o m', (.inr (WorkEvent.assigned o t k a m') : work.XEv) ∈ pre ∧ Past.opener (cores pre) t = some o := by
  have := h.holdsNamed "only_assignee_can_ask"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk] at this
  obtain ⟨o, m', hm⟩ := assigned_of_contains this
  exact ⟨o, m', hm, assignment_by_opener h hm⟩

/-- **Only the asked reply**: before every `work.reply` by `a` on item `k`, the item's assignee asked `a` to prepare
it. -/
theorem replied_by_asked_preparer {pre post : work.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.replied a t k m) :: post)) :
    ∃ b m', (.inr (WorkEvent.asked b t k a m') : work.XEv) ∈ pre ∧
      ∃ o m'', (.inr (WorkEvent.assigned o t k b m'') : work.XEv) ∈ pre ∧ Past.opener (cores pre) t = some o := by
  have := h.holdsNamed "only_asked_preparers_can_reply"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk] at this
  obtain ⟨e, hm, hs, hn⟩ := mem_notes_evs (List.contains_iff_mem.mp this)
  obtain ⟨b, t', m', rfl⟩ := asked_note hn
  simp only [Commands.evStream_mk] at hs
  subst hs
  refine ⟨b, m', hm, ?_⟩
  obtain ⟨p1, p2, rfl⟩ := List.append_of_mem hm
  have hv : ValidX (p1 ++ .inr (WorkEvent.asked b t' k a m') :: (p2 ++ .inr (.replied a t' k m) :: post)) := by
    simpa [List.append_assoc] using h
  obtain ⟨o, m'', hm2, ho⟩ := asked_by_assignee hv
  refine ⟨o, m'', List.mem_append_left _ hm2, ?_⟩
  simpa [cores] using opener_stays ho (cores (.inr (WorkEvent.asked b t' k a m') :: p2))

/-- **Only the assignee completes**: before every `work.complete` by `a` on item `k`, the item was assigned to `a`, by
the opener. -/
theorem completed_by_assignee {pre post : work.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.completed a t k m) :: post)) :
    ∃ o m', (.inr (WorkEvent.assigned o t k a m') : work.XEv) ∈ pre ∧ Past.opener (cores pre) t = some o := by
  have := h.holdsNamed "only_assignee_can_decide"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk] at this
  obtain ⟨o, m', hm⟩ := assigned_of_contains this
  exact ⟨o, m', hm, assignment_by_opener h hm⟩

/-- **Only the assignee cancels**: before every `work.cancel` by `a` on item `k`, the item was assigned to `a`, by the
opener. -/
theorem cancelled_by_assignee {pre post : work.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.cancelled a t k m) :: post)) :
    ∃ o m', (.inr (WorkEvent.assigned o t k a m') : work.XEv) ∈ pre ∧ Past.opener (cores pre) t = some o := by
  have := h.holdsNamed "only_assignee_can_decide"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk] at this
  obtain ⟨o, m', hm⟩ := assigned_of_contains this
  exact ⟨o, m', hm, assignment_by_opener h hm⟩

/-- **A preparer is never the assignee**: every `work.ask` names a preparer other than its actor, the assignee. -/
theorem preparer_ne_assignee {pre post : work.XLog} {a t k p : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.asked a t k p m) :: post)) : p ≠ a := by
  have := h.holdsNamed "preparer_must_not_be_the_assignee"
  dsimp only at this
  simp only [bne_iff_ne, ne_eq] at this
  exact fun hpa => this hpa.symm

/-! ## Each step once, in order -/

/-- An item is created at most once per stream: its id is new when it is created. -/
theorem created_once {pre post : work.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.created a t k m) :: post)) : noted ((evs pre t).flatMap notes) "work" k = false := by
  have := h.holdsNamed "work_id_must_be_new"
  dsimp only at this
  simpa using this

/-- Whatever is said of an item after its creation names a created item: the item of every `work.assign`, `work.ask`,
`work.reply`, `work.complete` and `work.cancel` was created earlier on the same stream. -/
theorem item_created {pre post : work.XLog} {x : WorkEvent} {t k : Id}
    (h : ValidX (pre ++ .inr x :: post)) (hs : work.evStream x = t)
    (hk : match x with
      | .assigned _ _ k' _ _ | .asked _ _ k' _ _ | .replied _ _ k' _ | .completed _ _ k' _
      | .cancelled _ _ k' _ => k' = k
      | .created .. => False) :
    ∃ a m, (.inr (WorkEvent.created a t k m) : work.XEv) ∈ pre := by
  subst hs
  have := h.holdsNamed "work_must_exist"
  dsimp only at this
  simp only [read_notes] at this
  have hn : noted ((evs pre (work.evStream x)).flatMap notes) "work" k = true := by
    cases x <;> simp_all
  obtain ⟨q, hq⟩ := noted_iff.mp hn
  obtain ⟨e, hm, hs', hn'⟩ := mem_notes_evs hq
  obtain ⟨a, t', m, rfl⟩ := work_note hn'
  simp only [Commands.evStream_mk] at hs'
  subst hs'
  exact ⟨a, m, hm⟩

/-- An item is assigned at most once. -/
theorem assigned_once {pre post : work.XLog} {a t k q : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.assigned a t k q m) :: post)) : noted ((evs pre t).flatMap notes) "assigned" k = false := by
  have := h.holdsNamed "work_is_assigned_once"
  dsimp only at this
  simpa using this

/-- A preparer is asked at most once per item. -/
theorem asked_once {pre post : work.XLog} {a t k p : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.asked a t k p m) :: post)) :
    ∀ b m', (.inr (WorkEvent.asked b t k p m') : work.XEv) ∉ pre := by
  have := h.holdsNamed "preparer_is_asked_once"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at this
  intro b m' hm
  have hx : ((evs pre t).flatMap notes).contains ("asked", k, p) = true :=
    List.contains_iff_mem.mpr (List.mem_flatMap.mpr ⟨_, mem_evs.mpr ⟨hm, rfl⟩, by simp [notes]⟩)
  rw [hx] at this
  exact Bool.noConfusion this

/-- A preparer replies at most once per item. -/
theorem replied_once {pre post : work.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.replied a t k m) :: post)) :
    ∀ m', (.inr (WorkEvent.replied a t k m') : work.XEv) ∉ pre := by
  have := h.holdsNamed "preparer_replies_once"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at this
  intro m' hm
  have hx : ((evs pre t).flatMap notes).contains ("replied", k, a) = true :=
    List.contains_iff_mem.mpr (List.mem_flatMap.mpr ⟨_, mem_evs.mpr ⟨hm, rfl⟩, by simp [notes]⟩)
  rw [hx] at this
  exact Bool.noConfusion this

/-! ## A decision is final -/

/-- The item a work event is about. -/
def item : WorkEvent → Id
  | .created _ _ k _ | .assigned _ _ k _ _ | .asked _ _ k _ _ | .replied _ _ k _ | .completed _ _ k _
  | .cancelled _ _ k _ => k

/-- Whether a work event decides its item: a completion or a cancellation. -/
def decides : WorkEvent → Bool
  | .completed .. | .cancelled .. => true
  | _ => false

/-- A decision's note says its item is decided. -/
theorem decided_of_decides {d : WorkEvent} (hd : decides d = true) {w1 w2 : List Note} :
    decided (w1 ++ notes d ++ w2) (item d) = true := by
  cases d <;> simp_all [decides, decided, item, noted, notes]

/-- Once an item is decided, its notes say so in every extension. -/
theorem decided_mono {w1 w2 : List Note} {k : String} (h : decided w1 k = true) : decided (w1 ++ w2) k = true := by
  simp only [decided, noted, List.any_append, Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl h)

/-- **An item is decided once**: before every `work.complete` or `work.cancel` of `k`, `k` was not decided. -/
theorem decided_once {pre post : work.XLog} {d : WorkEvent} (hd : decides d = true)
    (h : ValidX (pre ++ .inr d :: post)) : decided ((evs pre (work.evStream d)).flatMap notes) (item d) = false := by
  have := h.holdsNamed "work_is_decided_once"
  dsimp only at this
  cases d <;> simp_all [decides, item]

/-- No work event about an item is accepted once the stream's notes say the item exists, is assigned and is decided:
not a creation (`work_id_must_be_new`), not an assignment (`work_is_assigned_once`), not an ask or a reply
(`work_must_be_undecided`), and not another decision (`work_is_decided_once`). -/
theorem no_event_once_decided {pre post : work.XLog} {x : WorkEvent}
    (h : ValidX (pre ++ .inr x :: post))
    (hex : noted ((evs pre (work.evStream x)).flatMap notes) "work" (item x) = true)
    (has : noted ((evs pre (work.evStream x)).flatMap notes) "assigned" (item x) = true)
    (hdec : decided ((evs pre (work.evStream x)).flatMap notes) (item x) = true) : False := by
  cases x with
  | created a t k m =>
    have := h.holdsNamed "work_id_must_be_new"
    dsimp only at this
    simp_all [item]
  | assigned a t k q m =>
    have := h.holdsNamed "work_is_assigned_once"
    dsimp only at this
    simp_all [item]
  | asked a t k p m =>
    have := h.holdsNamed "work_must_be_undecided"
    dsimp only at this
    simp_all [item]
  | replied a t k m =>
    have := h.holdsNamed "work_must_be_undecided"
    dsimp only at this
    simp_all [item]
  | completed a t k m =>
    have := h.holdsNamed "work_is_decided_once"
    dsimp only at this
    simp_all [item]
  | cancelled a t k m =>
    have := h.holdsNamed "work_is_decided_once"
    dsimp only at this
    simp_all [item]

/-- A decision was accepted: its item existed and was assigned, as the notes before it say. -/
theorem decision_admitted {pre post : work.XLog} {d : WorkEvent} (hd : decides d = true)
    (h : ValidX (pre ++ .inr d :: post)) :
    noted ((evs pre (work.evStream d)).flatMap notes) "work" (item d) = true ∧
    noted ((evs pre (work.evStream d)).flatMap notes) "assigned" (item d) = true := by
  have h1 := h.holdsNamed "work_must_exist"
  have h2 := h.holdsNamed "only_assignee_can_decide"
  dsimp only at h1 h2
  simp only [read_notes] at h1 h2
  cases d <;> simp only [decides, Bool.false_eq_true] at hd <;>
    (simp only [item] at h1 h2 ⊢; exact ⟨h1, noted_iff.mpr ⟨_, List.contains_iff_mem.mp h2⟩⟩)

/-- **A decision is final**: after an item is completed or cancelled, no work event about it is accepted on the
stream (`no_event_once_decided`). -/
theorem decision_final {pre mid post : work.XLog} {d x : WorkEvent} (hd : decides d = true)
    (h : ValidX (pre ++ .inr d :: mid ++ .inr x :: post))
    (hs : work.evStream x = work.evStream d) (hk : item x = item d) : False := by
  -- `::` binds tighter than `++`: `h` is on `(pre ++ .inr d :: mid) ++ .inr x :: post`
  have hd' : ValidX (pre ++ .inr d :: (mid ++ .inr x :: post)) := by simpa [List.append_assoc] using h
  have hw : (evs (pre ++ .inr d :: mid) (work.evStream x)).flatMap notes =
      (evs pre (work.evStream d)).flatMap notes ++ notes d ++ (evs mid (work.evStream d)).flatMap notes := by
    rw [hs]; simp [evs_append, evs_cons_inr, List.flatMap_append, List.flatMap_cons, List.append_assoc]
  obtain ⟨hex, has⟩ := decision_admitted hd hd'
  refine no_event_once_decided h ?_ ?_ ?_ <;> rw [hw, hk]
  · simp only [noted, List.any_append, Bool.or_eq_true]; exact Or.inl (Or.inl (by simpa [noted] using hex))
  · simp only [noted, List.any_append, Bool.or_eq_true]; exact Or.inl (Or.inl (by simpa [noted] using has))
  · exact decided_of_decides hd

/-! ## The core's guarantees, here -/

/-- Only the opener closes a stream of work (`Layer.ValidX.close_by_opener`). -/
theorem work_close_by_opener {pre post : work.XLog} {a t : Id} {m : Meta}
    (h : ValidX (pre ++ .inl (Event.streamClosed a t m) :: post)) : Past.opener (cores pre) t = some a :=
  h.close_by_opener

/-- Nothing, of the core or of the layer, is appended to a stream after its close (`Layer.ValidX.close_final`). -/
theorem work_close_final {pre mid post : work.XLog} {a t : Id} {m : Meta} {x : work.XEv}
    (h : ValidX (pre ++ .inl (Event.streamClosed a t m) :: mid ++ x :: post)) : streamX x ≠ t := h.close_final

end Work
