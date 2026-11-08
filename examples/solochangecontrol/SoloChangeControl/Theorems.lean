-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import SoloChangeControl.Layer

/-!
# The solo change control layer's guarantees

Each holds of every valid log of the layer (`ValidX`), and follows from the rules that held when its events were
accepted (`ValidX.holdsNamed`), from the core's opener (`v.opener`), and from the core's theorems through `h.cores`.
Named as the sentence each proves. Every permission rests on the opener: the opener creates, branches, pulls and
decides (`every_change_is_created_by_the_opener`, `every_branch_is_by_the_opener`, `the_pull_is_by_the_opener`,
`the_merge_is_by_the_opener`, `the_abandon_is_by_the_opener`); the developers are whom the opener branched
(`every_push_is_by_a_branched_developer`); the three roles never meet (`roles_are_disjoint`); no revision is named
twice on a change (`revisions_are_distinct`); the pull cuts off incoming work
(`nothing_is_branched_or_pushed_after_the_pull`); nothing about a change follows its decision
(`nothing_follows_a_decision`). And one theorem of acceptance rather than of valid logs: the opener's merge of an
undecided change at a new revision is accepted whatever else has or has not happened
(`the_creator_can_always_merge`).
-/

namespace SoloChangeControl
open Provenstream Provenstream.Layer

/-! ## What the memory reads: the notes of the stream's change events -/

theorem foldl_addNotes (past : List ChangeEvent) (st : List Note) : past.foldl addNotes st = st ++ past.flatMap notes := by
  induction past generalizing st with
  | nil => simp
  | cons e es ih => simp [ih, addNotes, List.append_assoc]

/-- What the layer's rules read of the stream's change events is their notes, in order. -/
@[simp] theorem read_notes (past : List ChangeEvent) : past.foldl addNotes [] = past.flatMap notes := by
  simp [foldl_addNotes]

/-- A note of the stream's change events is a note of a change event of that stream in the log. -/
theorem mem_notes_evs {log : solo.XLog} {t : Id} {n : Note} (h : n ∈ (evs log t).flatMap notes) :
    ∃ e, .inr e ∈ log ∧ solo.evStream e = t ∧ n ∈ notes e := by
  obtain ⟨e, he, hn⟩ := List.mem_flatMap.mp h
  exact ⟨e, (mem_evs.mp he).1, (mem_evs.mp he).2, hn⟩

theorem noted_iff {w : List Note} {what k : String} : noted w what k = true ↔ ∃ q, (what, k, q) ∈ w := by
  simp only [noted, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨f, k', q⟩, hm, rfl, rfl⟩; exact ⟨q, hm⟩
  · rintro ⟨q, hm⟩; exact ⟨_, hm, rfl, rfl⟩

/-- Once noted, noted in every extension. -/
theorem noted_mono {w1 w2 : List Note} {what k : String} (h : noted w1 what k = true) :
    noted (w1 ++ w2) what k = true := by
  simp only [noted, List.any_append, Bool.or_eq_true]; exact Or.inl h

/-! What each kind of note says of the event that made it. -/

/-- A note of a change's harness revision: the change has one, and the note names it. -/
@[simp] theorem mem_harnessNotes {k : String} {r : Option String} {n : Note} :
    n ∈ harnessNotes k r ↔ ∃ v, r = some v ∧ n = ("harness", k, v) := by
  cases r <;> simp [harnessNotes]

theorem change_note {e : ChangeEvent} {k q : String} (h : ("change", k, q) ∈ notes e) :
    ∃ a t r m, e = .created a t k q r m := by
  cases e <;> simp_all [notes]

theorem developer_note {e : ChangeEvent} {k q : String} (h : ("developer", k, q) ∈ notes e) :
    ∃ a t u m, e = .branched a t k q u m := by
  cases e <;> simp_all [notes]

theorem reviewer_note {e : ChangeEvent} {k q : String} (h : ("reviewer", k, q) ∈ notes e) :
    ∃ t u s m, e = .reviewed q t k u s m := by
  cases e <;> simp_all [notes]

theorem pulled_note {e : ChangeEvent} {k q : String} (h : ("pulled", k, q) ∈ notes e) : ∃ a t m, e = .pulled a t k m := by
  cases e <;> simp_all [notes]

/-- The stream's change events before an event, noted developer `d` of `k` only by a `change.branched` event in the
log. -/
theorem branched_of_contains {pre : solo.XLog} {t k d : Id}
    (h : ((evs pre t).flatMap notes).contains ("developer", k, d) = true) :
    ∃ o u m', (.inr (ChangeEvent.branched o t k d u m') : solo.XEv) ∈ pre := by
  obtain ⟨e, hm, hs, hn⟩ := mem_notes_evs (List.contains_iff_mem.mp h)
  obtain ⟨o, t', u, m', rfl⟩ := developer_note hn
  simp only [Commands.evStream_mk] at hs
  subst hs
  exact ⟨o, u, m', hm⟩

/-- The stream's change events before an event, noted reviewer `r` of `k` only by a `change.reviewed` event in the
log. -/
theorem reviewed_of_contains {pre : solo.XLog} {t k r : Id}
    (h : ((evs pre t).flatMap notes).contains ("reviewer", k, r) = true) :
    ∃ u s m', (.inr (ChangeEvent.reviewed r t k u s m') : solo.XEv) ∈ pre := by
  obtain ⟨e, hm, hs, hn⟩ := mem_notes_evs (List.contains_iff_mem.mp h)
  obtain ⟨t', u, s, m', rfl⟩ := reviewer_note hn
  simp only [Commands.evStream_mk] at hs
  subst hs
  exact ⟨u, s, m', hm⟩

/-- A note of an event of stream `t` in the log is among the notes the memory reads after it. -/
theorem contains_of_mem (pre : solo.XLog) (t : Id) (e : ChangeEvent) (n : Note)
    (hm : (.inr e : solo.XEv) ∈ pre) (hs : solo.evStream e = t) (hn : n ∈ notes e) :
    ((evs pre t).flatMap notes).contains n = true :=
  List.contains_iff_mem.mpr (List.mem_flatMap.mpr ⟨_, mem_evs.mpr ⟨hm, hs⟩, hn⟩)

/-- Two members of a list, one before the other, or the other before the one. -/
theorem mem_mem_split {α : Type} {l : List α} {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hne : x ≠ y) :
    (∃ l1 l2 l3, l = l1 ++ x :: l2 ++ y :: l3) ∨ (∃ l1 l2 l3, l = l1 ++ y :: l2 ++ x :: l3) := by
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hx
  rcases List.mem_append.mp hy with hy1 | hy2
  · obtain ⟨m1, m2, rfl⟩ := List.append_of_mem hy1
    exact Or.inr ⟨m1, m2, l2, by simp [List.append_assoc]⟩
  · rcases List.mem_cons.mp hy2 with rfl | hy2
    · exact absurd rfl hne
    · obtain ⟨m1, m2, rfl⟩ := List.append_of_mem hy2
      exact Or.inl ⟨l1, m1, m2, by simp [List.append_assoc]⟩

/-! ## Who creates, who branches, who pulls, who decides: the opener -/

/-- **Every change is created by the opener**: every `change.create` in a valid log is by the stream's opener. -/
theorem every_change_is_created_by_the_opener {pre post : solo.XLog} {a t k : Id} {u : String} {r : Option String}
    {m : Meta} (h : ValidX (pre ++ .inr (.created a t k u r m) :: post)) : Past.opener (cores pre) t = some a := by
  have := h.holdsNamed "only_opener_can_create"
  dsimp only at this
  simpa using this

/-- **Every branch is by the opener**: every `change.branch` in a valid log is by the stream's opener, so every
developer was named by the opener. -/
theorem every_branch_is_by_the_opener {pre post : solo.XLog} {a t k d : Id} {u : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.branched a t k d u m) :: post)) : Past.opener (cores pre) t = some a := by
  have := h.holdsNamed "only_opener_can_branch"
  dsimp only at this
  simpa using this

/-- A branch of `k` to `d` in a valid log was made by the stream's opener, as the log before it says. -/
theorem branch_by_opener {pre post : solo.XLog} {o t k d : Id} {u : String} {m' : Meta}
    (h : ValidX (pre ++ post)) (hm : (.inr (ChangeEvent.branched o t k d u m') : solo.XEv) ∈ pre) :
    Past.opener (cores pre) t = some o := by
  obtain ⟨p1, p2, rfl⟩ := List.append_of_mem hm
  have hv : ValidX (p1 ++ .inr (ChangeEvent.branched o t k d u m') :: (p2 ++ post)) := by
    simpa [List.append_assoc] using h
  have ho := every_branch_is_by_the_opener hv
  simpa [cores] using opener_stays ho (cores (.inr (ChangeEvent.branched o t k d u m') :: p2))

/-- **Every push is by a branched developer**: before every `change.push` by `d` on change `k`, the opener branched
`k` to `d`. -/
theorem every_push_is_by_a_branched_developer {pre post : solo.XLog} {d t k : Id} {u : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.pushed d t k u m) :: post)) :
    ∃ o u' m', (.inr (ChangeEvent.branched o t k d u' m') : solo.XEv) ∈ pre ∧ Past.opener (cores pre) t = some o := by
  have := h.holdsNamed "only_branched_developers_can_push"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk] at this
  obtain ⟨o, u', m', hm⟩ := branched_of_contains this
  exact ⟨o, u', m', hm, branch_by_opener h hm⟩

/-- **The pull is by the opener.** -/
theorem the_pull_is_by_the_opener {pre post : solo.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.pulled a t k m) :: post)) : Past.opener (cores pre) t = some a := by
  have := h.holdsNamed "only_opener_can_pull"
  dsimp only at this
  simpa using this

/-- **The merge is by the opener.** -/
theorem the_merge_is_by_the_opener {pre post : solo.XLog} {a t k : Id} {u : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.merged a t k u m) :: post)) : Past.opener (cores pre) t = some a := by
  have := h.holdsNamed "only_opener_can_decide"
  dsimp only at this
  simpa using this

/-- **The abandon is by the opener.** -/
theorem the_abandon_is_by_the_opener {pre post : solo.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.abandoned a t k m) :: post)) : Past.opener (cores pre) t = some a := by
  have := h.holdsNamed "only_opener_can_decide"
  dsimp only at this
  simpa using this

/-! ## The roles are disjoint -/

/-- **No developer is the opener**: every `change.branch` names a developer other than the stream's opener, who
never changes, so the opener of the whole log is not it. -/
theorem no_developer_is_the_opener {pre post : solo.XLog} {o t k d : Id} {u : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.branched o t k d u m) :: post)) :
    Past.opener (cores (pre ++ .inr (.branched o t k d u m) :: post)) t ≠ some d := by
  have h6 := h.holdsNamed "developer_must_not_be_the_opener"
  dsimp only at h6
  have ho := every_branch_is_by_the_opener h
  simp only [Past.view_opener, bne_iff_ne, ne_eq] at h6
  have : Past.opener (cores (pre ++ .inr (.branched o t k d u m) :: post)) t = some o := by
    simpa [cores] using opener_stays ho (cores (.inr (ChangeEvent.branched o t k d u m) :: post))
  rw [this]; intro hc; exact h6 (ho.trans hc)

/-- **No reviewer is the opener**: every `change.review` is by a principal other than the stream's opener. -/
theorem no_reviewer_is_the_opener {pre post : solo.XLog} {r t k : Id} {u s : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.reviewed r t k u s m) :: post)) : Past.opener (cores pre) t ≠ some r := by
  have := h.holdsNamed "reviewer_must_not_be_the_opener"
  dsimp only at this
  simpa using this

/-- **No developer is a reviewer**: no valid log branches change `k` to `d` and has `d` review `k`, in either order
(`reviewer_must_not_be_a_developer` refuses the review after the branch, `developer_must_not_be_a_reviewer` the branch
after the review). -/
theorem no_developer_is_a_reviewer {log : solo.XLog} (h : ValidX log) {o t k d : Id} {u u' s : String} {m m' : Meta}
    (hb : (.inr (ChangeEvent.branched o t k d u m) : solo.XEv) ∈ log)
    (hr : (.inr (ChangeEvent.reviewed d t k u' s m') : solo.XEv) ∈ log) : False := by
  rcases mem_mem_split hb hr (by simp) with ⟨l1, l2, l3, rfl⟩ | ⟨l1, l2, l3, rfl⟩
  · -- the branch first: the review reads the developer note
    have hv : ValidX ((l1 ++ .inr (ChangeEvent.branched o t k d u m) :: l2) ++ .inr (ChangeEvent.reviewed d t k u' s m') :: l3) := by
      simpa [List.append_assoc] using h
    have := hv.holdsNamed "reviewer_must_not_be_a_developer"
    dsimp only at this
    simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at this
    rw [contains_of_mem _ t (.branched o t k d u m) ("developer", k, d) (by simp) (by simp) (by simp [notes])] at this
    exact Bool.noConfusion this
  · -- the review first: the branch reads the reviewer note
    have hv : ValidX ((l1 ++ .inr (ChangeEvent.reviewed d t k u' s m') :: l2) ++ .inr (ChangeEvent.branched o t k d u m) :: l3) := by
      simpa [List.append_assoc] using h
    have := hv.holdsNamed "developer_must_not_be_a_reviewer"
    dsimp only at this
    simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at this
    rw [contains_of_mem _ t (.reviewed d t k u' s m') ("reviewer", k, d) (by simp) (by simp) (by simp [notes])] at this
    exact Bool.noConfusion this

/-- **The roles are disjoint**: a developer of a change is neither the stream's opener nor ever a reviewer of that
change, and a reviewer is not the opener (`no_developer_is_the_opener`, `no_developer_is_a_reviewer`,
`no_reviewer_is_the_opener`). -/
theorem roles_are_disjoint {log : solo.XLog} (h : ValidX log) {o t k d : Id} {u : String} {m : Meta}
    (hb : (.inr (ChangeEvent.branched o t k d u m) : solo.XEv) ∈ log) :
    Past.opener (cores log) t ≠ some d ∧ ∀ u' s m', (.inr (ChangeEvent.reviewed d t k u' s m') : solo.XEv) ∉ log := by
  refine ⟨?_, fun u' s m' hr => no_developer_is_a_reviewer h hb hr⟩
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hb
  exact no_developer_is_the_opener h

/-! ## Each step once, every change created -/

/-- **A change is created once** per stream: its id is new when it is created. -/
theorem a_change_is_created_once {pre post : solo.XLog} {a t k : Id} {u : String} {r : Option String} {m : Meta}
    (h : ValidX (pre ++ .inr (.created a t k u r m) :: post)) :
    noted ((evs pre t).flatMap notes) "change" k = false := by
  have := h.holdsNamed "change_id_must_be_new"
  dsimp only at this
  simpa using this

/-- The change a change event is about. -/
def item : ChangeEvent → Id
  | .created _ _ k _ _ _ | .branched _ _ k _ _ _ | .pushed _ _ k _ _ | .pulled _ _ k _ | .reviewed _ _ k _ _ _
  | .merged _ _ k _ _ | .abandoned _ _ k _ => k

/-- **Every event names a created change**: the change of every `change.branch`, `change.push`, `change.pull`,
`change.review`, `change.merge` and `change.abandon` was created earlier on the same stream. -/
theorem every_event_names_a_created_change {pre post : solo.XLog} {x : ChangeEvent} {t : Id}
    (h : ValidX (pre ++ .inr x :: post)) (hs : solo.evStream x = t)
    (hx : match x with | .created .. => False | _ => True) :
    ∃ a u r m, (.inr (ChangeEvent.created a t (item x) u r m) : solo.XEv) ∈ pre := by
  subst hs
  have := h.holdsNamed "change_must_exist"
  dsimp only at this
  simp only [read_notes] at this
  have hn : noted ((evs pre (solo.evStream x)).flatMap notes) "change" (item x) = true := by
    cases x <;> simp_all [item]
  obtain ⟨q, hq⟩ := noted_iff.mp hn
  obtain ⟨e, hm, hs', hn'⟩ := mem_notes_evs hq
  obtain ⟨a, t', r, m, rfl⟩ := change_note hn'
  simp only [Commands.evStream_mk] at hs'
  subst hs'
  exact ⟨a, q, r, m, hm⟩

/-- **A developer is branched once** per change. -/
theorem a_developer_is_branched_once {pre post : solo.XLog} {a t k d : Id} {u : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.branched a t k d u m) :: post)) :
    ∀ o u' m', (.inr (ChangeEvent.branched o t k d u' m') : solo.XEv) ∉ pre := by
  have := h.holdsNamed "developer_is_branched_once"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at this
  intro o u' m' hm
  rw [contains_of_mem pre t (.branched o t k d u' m') ("developer", k, d) hm (by simp) (by simp [notes])] at this
  exact Bool.noConfusion this

/-- **A change is pulled once.** -/
theorem a_change_is_pulled_once {pre post : solo.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.pulled a t k m) :: post)) :
    ∀ a' m', (.inr (ChangeEvent.pulled a' t k m') : solo.XEv) ∉ pre := by
  have := h.holdsNamed "change_is_pulled_once"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at this
  intro a' m' hm
  have hx : noted ((evs pre t).flatMap notes) "pulled" k = true :=
    noted_iff.mpr ⟨"", List.contains_iff_mem.mp
      (contains_of_mem pre t (.pulled a' t k m') ("pulled", k, "") hm (by simp) (by simp [notes]))⟩
  rw [hx] at this
  exact Bool.noConfusion this

/-! ## The revisions of a change are distinct -/

/-- The revision a change event names of its change, if it names one. -/
def revisionOf : ChangeEvent → Option (Id × String)
  | .created _ _ k u _ _ | .branched _ _ k _ u _ | .pushed _ _ k u _ | .reviewed _ _ k u _ _ | .merged _ _ k u _ =>
    some (k, u)
  | .pulled .. | .abandoned .. => none

/-- An event's revision note is among its notes. -/
theorem revision_note {x : ChangeEvent} {k u : String} (hx : revisionOf x = some (k, u)) :
    ∃ what, namesRevision what = true ∧ (what, k, u) ∈ notes x := by
  cases x with
  | created a t k' u' r m =>
    simp only [revisionOf, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨"change", rfl, by simp [notes]⟩
  | _ => simp_all [revisionOf, notes, namesRevision]

/-- An event naming a revision of `k` is about `k`. -/
theorem item_of_revision {x : ChangeEvent} {k u : String} (hx : revisionOf x = some (k, u)) : item x = k := by
  cases x <;> simp_all [revisionOf, item]

/-- After an event naming a revision of `k`, the stream's notes say `k` is a change: the event created it, or
`change_must_exist` held for it. -/
theorem change_noted_after {l1 l2 post : solo.XLog} {x : ChangeEvent} {k u : String}
    (h : ValidX (l1 ++ .inr x :: (l2 ++ post))) (hx : revisionOf x = some (k, u)) :
    noted ((evs (l1 ++ .inr x :: l2) (solo.evStream x)).flatMap notes) "change" k = true := by
  have hw : (evs (l1 ++ .inr x :: l2) (solo.evStream x)).flatMap notes =
      (evs l1 (solo.evStream x)).flatMap notes ++ (notes x ++ (evs l2 (solo.evStream x)).flatMap notes) := by
    simp [evs_append, evs_cons_inr, List.flatMap_append, List.flatMap_cons]
  rw [hw]
  cases x with
  | created a t k' u' r m =>
    simp only [revisionOf, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    simp [noted, notes]
  | pulled => simp [revisionOf] at hx
  | abandoned => simp [revisionOf] at hx
  | _ =>
    have h3 := h.holdsNamed "change_must_exist"
    dsimp only at h3
    simp only [read_notes] at h3
    simp only [revisionOf, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, -⟩ := hx
    exact noted_mono h3

/-- **Revisions are distinct**: no two events of a valid log, one before the other, name the same revision of the
same change on the same stream. So the starting revision, each branch revision, and every pushed, reviewed and
merged revision of a change are pairwise distinct. -/
theorem revisions_are_distinct {l1 l2 l3 : solo.XLog} {x y : ChangeEvent} {k u : String}
    (h : ValidX (l1 ++ .inr x :: l2 ++ .inr y :: l3)) (hs : solo.evStream y = solo.evStream x)
    (hx : revisionOf x = some (k, u)) (hy : revisionOf y = some (k, u)) : False := by
  -- `::` binds tighter than `++`: `h` is on `(l1 ++ .inr x :: l2) ++ .inr y :: l3`
  obtain ⟨what, hw, hn⟩ := revision_note hx
  have hnamed : revisionNamed ((evs (l1 ++ .inr x :: l2) (solo.evStream y)).flatMap notes) k u = true := by
    simp only [revisionNamed, List.any_eq_true]
    exact ⟨(what, k, u), List.contains_iff_mem.mp
      (contains_of_mem (l1 ++ .inr x :: l2) (solo.evStream y) x (what, k, u) (by simp) hs.symm hn), by simp [hw]⟩
  have hk : noted ((evs (l1 ++ .inr x :: l2) (solo.evStream y)).flatMap notes) "change" k = true := by
    rw [hs]; exact change_noted_after (by simpa [List.append_assoc] using h) hx
  cases y with
  | created a t k' u' r m =>
    -- a creation of `k` after an event naming a revision of `k`: `k` was already created
    have h2 := h.holdsNamed "change_id_must_be_new"
    dsimp only at h2
    simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at h2
    simp only [Commands.evStream_mk] at hk
    simp only [revisionOf, Option.some.injEq, Prod.mk.injEq] at hy
    rw [hy.1, hk] at h2
    exact Bool.noConfusion h2
  | pulled => simp [revisionOf] at hy
  | abandoned => simp [revisionOf] at hy
  | _ =>
    have h4 := h.holdsNamed "revisions_must_be_unique"
    dsimp only at h4
    simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at h4
    simp only [Commands.evStream_mk] at hnamed
    simp only [revisionOf, Option.some.injEq, Prod.mk.injEq] at hy
    rw [hy.1, hy.2, hnamed] at h4
    exact Bool.noConfusion h4

/-- **The merged revision is none of the others**: before every `change.merge` of `k` at `u`, no note of `k` named
`u`: not its starting revision, not a branch revision, not a pushed or a reviewed one. -/
theorem the_merged_revision_is_none_of_the_others {pre post : solo.XLog} {a t k : Id} {u : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.merged a t k u m) :: post)) :
    revisionNamed ((evs pre t).flatMap notes) k u = false := by
  have := h.holdsNamed "revisions_must_be_unique"
  dsimp only at this
  simpa using this

/-- **No reviewed revision is a developer's**: no valid log has a push and a review of the same change naming the
same revision, in either order. -/
theorem no_reviewed_revision_is_a_developers {log : solo.XLog} (h : ValidX log) {d r t k : Id} {u s : String}
    {m m' : Meta} (hp : (.inr (ChangeEvent.pushed d t k u m) : solo.XEv) ∈ log)
    (hr : (.inr (ChangeEvent.reviewed r t k u s m') : solo.XEv) ∈ log) : False := by
  rcases mem_mem_split hp hr (by simp) with ⟨l1, l2, l3, rfl⟩ | ⟨l1, l2, l3, rfl⟩
  · exact revisions_are_distinct h rfl (x := .pushed d t k u m) rfl rfl
  · exact revisions_are_distinct h rfl (x := .reviewed r t k u s m') rfl rfl

/-- **No pushed revision is a branch revision**: no valid log hands a developer a revision and has a developer push
that revision, in either order. -/
theorem no_pushed_revision_is_the_branch_revision {log : solo.XLog} (h : ValidX log) {o d d' t k : Id} {u : String}
    {m m' : Meta} (hb : (.inr (ChangeEvent.branched o t k d u m) : solo.XEv) ∈ log)
    (hp : (.inr (ChangeEvent.pushed d' t k u m') : solo.XEv) ∈ log) : False := by
  rcases mem_mem_split hb hp (by simp) with ⟨l1, l2, l3, rfl⟩ | ⟨l1, l2, l3, rfl⟩
  · exact revisions_are_distinct h rfl (x := .branched o t k d u m) rfl rfl
  · exact revisions_are_distinct h rfl (x := .pushed d' t k u m') rfl rfl

/-! ## The pull cuts off incoming work -/

/-- Whether a change event brings work in: a branch or a push. -/
def incoming : ChangeEvent → Bool
  | .branched .. | .pushed .. => true
  | _ => false

/-- **Nothing is branched or pushed after the pull**: after `change.pull` of `k`, no `change.branch` or `change.push`
of `k` is accepted on the stream. -/
theorem nothing_is_branched_or_pushed_after_the_pull {pre mid post : solo.XLog} {a t k : Id} {m : Meta} {x : ChangeEvent}
    (h : ValidX (pre ++ .inr (.pulled a t k m) :: mid ++ .inr x :: post)) (hs : solo.evStream x = t)
    (hk : item x = k) (hx : incoming x = true) : False := by
  have hv : ValidX ((pre ++ .inr (ChangeEvent.pulled a t k m) :: mid) ++ .inr x :: post) := by
    simpa [List.append_assoc] using h
  have h9 := hv.holdsNamed "change_must_not_be_pulled"
  dsimp only at h9
  simp only [read_notes] at h9
  have hp : noted ((evs (pre ++ .inr (ChangeEvent.pulled a t k m) :: mid) (solo.evStream x)).flatMap notes) "pulled" k = true :=
    noted_iff.mpr ⟨"", List.contains_iff_mem.mp (contains_of_mem (pre ++ .inr (ChangeEvent.pulled a t k m) :: mid)
      (solo.evStream x) (.pulled a t k m) ("pulled", k, "") (by simp) (by simp [hs]) (by simp [notes]))⟩
  cases x <;> simp_all [incoming, item]

/-! ## A decision is final -/

/-- Whether a change event decides its change: a merge or an abandon. -/
def decides : ChangeEvent → Bool
  | .merged .. | .abandoned .. => true
  | _ => false

/-- A decision's note says its change is decided. -/
theorem decided_of_decides {d : ChangeEvent} (hd : decides d = true) {w1 w2 : List Note} :
    decided (w1 ++ notes d ++ w2) (item d) = true := by
  cases d <;> simp_all [decides, decided, item, noted, notes]

/-- **A change is decided once**: before every `change.merge` or `change.abandon` of `k`, `k` was not decided. -/
theorem a_change_is_decided_once {pre post : solo.XLog} {d : ChangeEvent} (hd : decides d = true)
    (h : ValidX (pre ++ .inr d :: post)) : decided ((evs pre (solo.evStream d)).flatMap notes) (item d) = false := by
  have := h.holdsNamed "change_is_decided_once"
  dsimp only at this
  cases d <;> simp_all [decides, item]

/-- No change event about a change is accepted once the stream's notes say the change exists and is decided: not a
creation (`change_id_must_be_new`), not a branch, push, pull or review (`change_must_be_undecided`), and not another
decision (`change_is_decided_once`). -/
theorem no_event_once_decided {pre post : solo.XLog} {x : ChangeEvent}
    (h : ValidX (pre ++ .inr x :: post))
    (hex : noted ((evs pre (solo.evStream x)).flatMap notes) "change" (item x) = true)
    (hdec : decided ((evs pre (solo.evStream x)).flatMap notes) (item x) = true) : False := by
  cases x with
  | created a t k u r m =>
    have := h.holdsNamed "change_id_must_be_new"
    dsimp only at this
    simp_all [item]
  | merged a t k u m =>
    have := h.holdsNamed "change_is_decided_once"
    dsimp only at this
    simp_all [item]
  | abandoned a t k m =>
    have := h.holdsNamed "change_is_decided_once"
    dsimp only at this
    simp_all [item]
  | _ =>
    have := h.holdsNamed "change_must_be_undecided"
    dsimp only at this
    simp_all [item]

/-- A decision was accepted: its change existed, as the notes before it say. -/
theorem decision_admitted {pre post : solo.XLog} {d : ChangeEvent} (hd : decides d = true)
    (h : ValidX (pre ++ .inr d :: post)) :
    noted ((evs pre (solo.evStream d)).flatMap notes) "change" (item d) = true := by
  have h3 := h.holdsNamed "change_must_exist"
  dsimp only at h3
  simp only [read_notes] at h3
  cases d <;> simp only [decides, Bool.false_eq_true] at hd <;> simpa [item] using h3

/-- **Nothing follows a decision**: after a change is merged or abandoned, no change event about it is accepted on
the stream (`no_event_once_decided`). -/
theorem nothing_follows_a_decision {pre mid post : solo.XLog} {d x : ChangeEvent} (hd : decides d = true)
    (h : ValidX (pre ++ .inr d :: mid ++ .inr x :: post))
    (hs : solo.evStream x = solo.evStream d) (hk : item x = item d) : False := by
  -- `::` binds tighter than `++`: `h` is on `(pre ++ .inr d :: mid) ++ .inr x :: post`
  have hd' : ValidX (pre ++ .inr d :: (mid ++ .inr x :: post)) := by simpa [List.append_assoc] using h
  have hw : (evs (pre ++ .inr d :: mid) (solo.evStream x)).flatMap notes =
      (evs pre (solo.evStream d)).flatMap notes ++ notes d ++ (evs mid (solo.evStream d)).flatMap notes := by
    rw [hs]; simp [evs_append, evs_cons_inr, List.flatMap_append, List.flatMap_cons, List.append_assoc]
  have hex := decision_admitted hd hd'
  refine no_event_once_decided h ?_ ?_ <;> rw [hw, hk]
  · simp only [noted, List.any_append, Bool.or_eq_true]; exact Or.inl (Or.inl (by simpa [noted] using hex))
  · exact decided_of_decides hd

/-! ## The creator can always merge -/

/-- **The creator can always merge**: a theorem of acceptance, not of valid logs. After any valid log in which stream
`t` is open and not closed with opener `a`, change `k` is created on it and not decided, and revision `u` is not yet
named on `k`, the service accepts `a`'s `change.merge` of `k` at `u`, whatever else has or has not happened: no pull,
no push, no review, nothing from anyone else, and no earlier event of `a`'s own beyond the creation. These six
hypotheses are everything the merge's rules read (`change_must_exist`, `revisions_must_be_unique`,
`only_opener_can_decide`, `change_is_decided_once`) together with the core's admission (`stream_must_exist`,
`stream_must_be_open`); the request's fresh list is empty, as every layer request's is. The host refuses a malformed
URL before the engine sees it, so `u` is taken as a well-formed URL. -/
theorem the_creator_can_always_merge {pre : solo.XLog} (h : ValidX pre) {a t k : Id} {u : String} {m : Meta}
    (hopen : Past.opened (cores pre) t = true) (hclosed : Past.closed (cores pre) t = false)
    (hopener : Past.opener (cores pre) t = some a)
    (hk : noted ((evs pre t).flatMap notes) "change" k = true)
    (hu : revisionNamed ((evs pre t).flatMap notes) k u = false)
    (hdec : decided ((evs pre t).flatMap notes) k = false) :
    solo.service.respond pre (.inr (a, .merge t k u m, [])) = .accepted (.inr (.merged a t k u m)) := by
  refine Service.respond_accepted_iff.mpr ⟨rfl, ?_⟩
  have hv : ValidX (pre ++ [.inr (.merged a t k u m)]) := by
    refine (ValidX.snoc_inr_iff h).mpr ⟨?_, ?_, ?_, ?_⟩
    · show (Past.view (cores pre) t).admits a = none
      exact View.admits_none.mpr ⟨by simpa using hopen, by simpa using hclosed⟩
    · rfl
    · intro r hr
      simp only [solo, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        | rfl <;> simp [hopener, hk, hu, hdec, Past.view]
    · intro r hr
      simp at hr
  exact (Service.Valid.inv hv).2

/-! ## The core's guarantees, here -/

/-- **Only the opener closes the stream** of changes (`Layer.ValidX.close_by_opener`). -/
theorem only_the_opener_closes_the_stream {pre post : solo.XLog} {a t : Id} {m : Meta}
    (h : ValidX (pre ++ .inl (Event.streamClosed a t m) :: post)) : Past.opener (cores pre) t = some a :=
  h.close_by_opener

/-- **Nothing follows a close**: nothing, of the core or of the layer, is appended to a stream after its close
(`Layer.ValidX.close_final`). -/
theorem nothing_follows_a_close {pre mid post : solo.XLog} {a t : Id} {m : Meta} {x : solo.XEv}
    (h : ValidX (pre ++ .inl (Event.streamClosed a t m) :: mid ++ x :: post)) : streamX x ≠ t := h.close_final

end SoloChangeControl
