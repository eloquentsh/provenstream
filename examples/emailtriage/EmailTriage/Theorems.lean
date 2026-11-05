-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import EmailTriage.Layer

/-!
# The inbound email triage layer's guarantees

Each holds of every valid log of the layer (`ValidX`), and follows from the rules that held when its events were
accepted (`ValidX.holdsNamed`), from the core's opener (`v.opener`), and from the core's theorems through `h.cores`.
Named as the sentence each proves. Every permission rests on the opener: the opener creates, asks and decides
(`every_triage_is_created_by_the_opener`, `every_ask_is_by_the_opener`, `the_reply_is_by_the_opener`,
`the_ignore_is_by_the_opener`); the advisers are whom the opener asked (`every_advice_is_by_an_asked_adviser`), and
each advises once (`an_adviser_advises_once`); the three roles never meet (`roles_are_disjoint`); the first review
cuts off asks and advice (`nothing_is_asked_or_advised_after_the_review`); nothing about a triage follows its decision
(`nothing_follows_a_decision`). And one theorem of acceptance rather than of valid logs: the opener's ignore of an
undecided triage is accepted whatever else has or has not happened (`the_creator_can_always_ignore`).
-/

namespace EmailTriage
open Provenstream Provenstream.Layer

/-! ## What the memory reads: the notes of the stream's triage events -/

theorem foldl_addNotes (past : List TriageEvent) (st : List Note) : past.foldl addNotes st = st ++ past.flatMap notes := by
  induction past generalizing st with
  | nil => simp
  | cons e es ih => simp [ih, addNotes, List.append_assoc]

@[simp] theorem read_notes (past : List TriageEvent) : past.foldl addNotes [] = past.flatMap notes := by
  simp [foldl_addNotes]

theorem mem_notes_evs {log : inbound.XLog} {t : Id} {n : Note} (h : n ∈ (evs log t).flatMap notes) :
    ∃ e, .inr e ∈ log ∧ inbound.evStream e = t ∧ n ∈ notes e := by
  obtain ⟨e, he, hn⟩ := List.mem_flatMap.mp h
  exact ⟨e, (mem_evs.mp he).1, (mem_evs.mp he).2, hn⟩

theorem noted_iff {w : List Note} {what k : String} : noted w what k = true ↔ ∃ q, (what, k, q) ∈ w := by
  simp only [noted, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨f, k', q⟩, hm, rfl, rfl⟩; exact ⟨q, hm⟩
  · rintro ⟨q, hm⟩; exact ⟨_, hm, rfl, rfl⟩

theorem noted_mono {w1 w2 : List Note} {what k : String} (h : noted w1 what k = true) :
    noted (w1 ++ w2) what k = true := by
  simp only [noted, List.any_append, Bool.or_eq_true]; exact Or.inl h

theorem triage_note {e : TriageEvent} {k q : String} (h : ("triage", k, q) ∈ notes e) :
    ∃ a t m, e = .created a t k q m := by
  cases e <;> simp_all [notes]

theorem adviser_note {e : TriageEvent} {k q : String} (h : ("adviser", k, q) ∈ notes e) :
    ∃ a t m, e = .asked a t k q m := by
  cases e <;> simp_all [notes]

theorem advice_note {e : TriageEvent} {k q : String} (h : ("advice", k, q) ∈ notes e) :
    ∃ t v m, e = .advised q t k v m := by
  cases e <;> simp_all [notes]

theorem reviewer_note {e : TriageEvent} {k q : String} (h : ("reviewer", k, q) ∈ notes e) :
    ∃ t v m, e = .reviewed q t k v m := by
  cases e <;> simp_all [notes]

theorem asked_of_contains {pre : inbound.XLog} {t k d : Id}
    (h : ((evs pre t).flatMap notes).contains ("adviser", k, d) = true) :
    ∃ o m', (.inr (TriageEvent.asked o t k d m') : inbound.XEv) ∈ pre := by
  obtain ⟨e, hm, hs, hn⟩ := mem_notes_evs (List.contains_iff_mem.mp h)
  obtain ⟨o, t', m', rfl⟩ := adviser_note hn
  simp only [Commands.evStream_mk] at hs
  subst hs
  exact ⟨o, m', hm⟩

theorem contains_of_mem (pre : inbound.XLog) (t : Id) (e : TriageEvent) (n : Note)
    (hm : (.inr e : inbound.XEv) ∈ pre) (hs : inbound.evStream e = t) (hn : n ∈ notes e) :
    ((evs pre t).flatMap notes).contains n = true :=
  List.contains_iff_mem.mpr (List.mem_flatMap.mpr ⟨_, mem_evs.mpr ⟨hm, hs⟩, hn⟩)

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

/-! ## Who creates, who asks, who decides: the opener -/

theorem every_triage_is_created_by_the_opener {pre post : inbound.XLog} {a t k : Id} {u : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.created a t k u m) :: post)) : Past.opener (cores pre) t = some a := by
  have := h.holdsNamed "only_opener_can_create"
  dsimp only at this
  simpa using this

theorem every_ask_is_by_the_opener {pre post : inbound.XLog} {a t k d : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.asked a t k d m) :: post)) : Past.opener (cores pre) t = some a := by
  have := h.holdsNamed "only_opener_can_ask"
  dsimp only at this
  simpa using this

theorem ask_by_opener {pre post : inbound.XLog} {o t k d : Id} {m' : Meta}
    (h : ValidX (pre ++ post)) (hm : (.inr (TriageEvent.asked o t k d m') : inbound.XEv) ∈ pre) :
    Past.opener (cores pre) t = some o := by
  obtain ⟨p1, p2, rfl⟩ := List.append_of_mem hm
  have hv : ValidX (p1 ++ .inr (TriageEvent.asked o t k d m') :: (p2 ++ post)) := by
    simpa [List.append_assoc] using h
  have ho := every_ask_is_by_the_opener hv
  simpa [cores] using opener_stays ho (cores (.inr (TriageEvent.asked o t k d m') :: p2))

/-- **Every advice is by an asked adviser**: before every `triage.advise` by `d` on `k`, the opener asked `d`. -/
theorem every_advice_is_by_an_asked_adviser {pre post : inbound.XLog} {d t k : Id} {v : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.advised d t k v m) :: post)) :
    ∃ o m', (.inr (TriageEvent.asked o t k d m') : inbound.XEv) ∈ pre ∧ Past.opener (cores pre) t = some o := by
  have := h.holdsNamed "only_asked_advisers_can_advise"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk] at this
  obtain ⟨o, m', hm⟩ := asked_of_contains this
  exact ⟨o, m', hm, ask_by_opener h hm⟩

theorem the_reply_is_by_the_opener {pre post : inbound.XLog} {a t k e : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.replied a t k e m) :: post)) : Past.opener (cores pre) t = some a := by
  have := h.holdsNamed "only_opener_can_decide"
  dsimp only at this
  simpa using this

theorem the_ignore_is_by_the_opener {pre post : inbound.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.ignored a t k m) :: post)) : Past.opener (cores pre) t = some a := by
  have := h.holdsNamed "only_opener_can_decide"
  dsimp only at this
  simpa using this

/-! ## The roles are disjoint -/

theorem no_adviser_is_the_opener {pre post : inbound.XLog} {o t k d : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.asked o t k d m) :: post)) :
    Past.opener (cores (pre ++ .inr (.asked o t k d m) :: post)) t ≠ some d := by
  have h6 := h.holdsNamed "adviser_must_not_be_the_opener"
  dsimp only at h6
  have ho := every_ask_is_by_the_opener h
  simp only [Past.view_opener, bne_iff_ne, ne_eq] at h6
  have : Past.opener (cores (pre ++ .inr (.asked o t k d m) :: post)) t = some o := by
    simpa [cores] using opener_stays ho (cores (.inr (TriageEvent.asked o t k d m) :: post))
  rw [this]; intro hc; exact h6 (ho.trans hc)

theorem no_reviewer_is_the_opener {pre post : inbound.XLog} {r t k : Id} {v : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.reviewed r t k v m) :: post)) : Past.opener (cores pre) t ≠ some r := by
  have := h.holdsNamed "reviewer_must_not_be_the_opener"
  dsimp only at this
  simpa using this

/-- **No adviser is a reviewer**: no valid log asks `d` on triage `k` and has `d` review `k`, in either order. -/
theorem no_adviser_is_a_reviewer {log : inbound.XLog} (h : ValidX log) {o t k d : Id} {v : String} {m m' : Meta}
    (hb : (.inr (TriageEvent.asked o t k d m) : inbound.XEv) ∈ log)
    (hr : (.inr (TriageEvent.reviewed d t k v m') : inbound.XEv) ∈ log) : False := by
  rcases mem_mem_split hb hr (by simp) with ⟨l1, l2, l3, rfl⟩ | ⟨l1, l2, l3, rfl⟩
  · have hv : ValidX ((l1 ++ .inr (TriageEvent.asked o t k d m) :: l2) ++ .inr (TriageEvent.reviewed d t k v m') :: l3) := by
      simpa [List.append_assoc] using h
    have := hv.holdsNamed "reviewer_must_not_be_an_adviser"
    dsimp only at this
    simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at this
    rw [contains_of_mem _ t (.asked o t k d m) ("adviser", k, d) (by simp) (by simp) (by simp [notes])] at this
    exact Bool.noConfusion this
  · have hv : ValidX ((l1 ++ .inr (TriageEvent.reviewed d t k v m') :: l2) ++ .inr (TriageEvent.asked o t k d m) :: l3) := by
      simpa [List.append_assoc] using h
    have := hv.holdsNamed "adviser_must_not_be_a_reviewer"
    dsimp only at this
    simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at this
    rw [contains_of_mem _ t (.reviewed d t k v m') ("reviewer", k, d) (by simp) (by simp) (by simp [notes])] at this
    exact Bool.noConfusion this

theorem roles_are_disjoint {log : inbound.XLog} (h : ValidX log) {o t k d : Id} {m : Meta}
    (hb : (.inr (TriageEvent.asked o t k d m) : inbound.XEv) ∈ log) :
    Past.opener (cores log) t ≠ some d ∧ ∀ v m', (.inr (TriageEvent.reviewed d t k v m') : inbound.XEv) ∉ log := by
  refine ⟨?_, fun v m' hr => no_adviser_is_a_reviewer h hb hr⟩
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hb
  exact no_adviser_is_the_opener h

/-! ## Each step once, every triage created -/

theorem a_triage_is_created_once {pre post : inbound.XLog} {a t k : Id} {u : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.created a t k u m) :: post)) :
    noted ((evs pre t).flatMap notes) "triage" k = false := by
  have := h.holdsNamed "triage_id_must_be_new"
  dsimp only at this
  simpa using this

def item : TriageEvent → Id
  | .created _ _ k _ _ | .asked _ _ k _ _ | .advised _ _ k _ _ | .reviewed _ _ k _ _ | .replied _ _ k _ _
  | .ignored _ _ k _ => k

theorem every_event_names_a_created_triage {pre post : inbound.XLog} {x : TriageEvent} {t : Id}
    (h : ValidX (pre ++ .inr x :: post)) (hs : inbound.evStream x = t)
    (hx : match x with | .created .. => False | _ => True) :
    ∃ a u m, (.inr (TriageEvent.created a t (item x) u m) : inbound.XEv) ∈ pre := by
  subst hs
  have := h.holdsNamed "triage_must_exist"
  dsimp only at this
  simp only [read_notes] at this
  have hn : noted ((evs pre (inbound.evStream x)).flatMap notes) "triage" (item x) = true := by
    cases x <;> simp_all [item]
  obtain ⟨q, hq⟩ := noted_iff.mp hn
  obtain ⟨e, hm, hs', hn'⟩ := mem_notes_evs hq
  obtain ⟨a, t', m, rfl⟩ := triage_note hn'
  simp only [Commands.evStream_mk] at hs'
  subst hs'
  exact ⟨a, q, m, hm⟩

theorem an_adviser_is_asked_once {pre post : inbound.XLog} {a t k d : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.asked a t k d m) :: post)) :
    ∀ o m', (.inr (TriageEvent.asked o t k d m') : inbound.XEv) ∉ pre := by
  have := h.holdsNamed "adviser_is_asked_once"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at this
  intro o m' hm
  rw [contains_of_mem pre t (.asked o t k d m') ("adviser", k, d) hm (by simp) (by simp [notes])] at this
  exact Bool.noConfusion this

/-- **An adviser advises once** per triage: before every `triage.advise` by `d` on `k`, `d` had not advised on `k`. -/
theorem an_adviser_advises_once {pre post : inbound.XLog} {d t k : Id} {v : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.advised d t k v m) :: post)) :
    ∀ v' m', (.inr (TriageEvent.advised d t k v' m') : inbound.XEv) ∉ pre := by
  have := h.holdsNamed "adviser_advises_once"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at this
  intro v' m' hm
  rw [contains_of_mem pre t (.advised d t k v' m') ("advice", k, d) hm (by simp) (by simp [notes])] at this
  exact Bool.noConfusion this

/-! ## The first review cuts off asks and advice -/

def incoming : TriageEvent → Bool
  | .asked .. | .advised .. => true
  | _ => false

/-- **Nothing is asked or advised after the review**: after `triage.review` of `k`, no `triage.ask` or `triage.advise`
of `k` is accepted on the stream. -/
theorem nothing_is_asked_or_advised_after_the_review {pre mid post : inbound.XLog} {a t k : Id} {v : String}
    {m : Meta} {x : TriageEvent}
    (h : ValidX (pre ++ .inr (.reviewed a t k v m) :: mid ++ .inr x :: post)) (hs : inbound.evStream x = t)
    (hk : item x = k) (hx : incoming x = true) : False := by
  have hv : ValidX ((pre ++ .inr (TriageEvent.reviewed a t k v m) :: mid) ++ .inr x :: post) := by
    simpa [List.append_assoc] using h
  have h9 := hv.holdsNamed "triage_must_not_be_reviewed"
  dsimp only at h9
  simp only [read_notes] at h9
  have hp : noted ((evs (pre ++ .inr (TriageEvent.reviewed a t k v m) :: mid) (inbound.evStream x)).flatMap notes) "reviewer" k = true :=
    noted_iff.mpr ⟨a, List.contains_iff_mem.mp (contains_of_mem (pre ++ .inr (TriageEvent.reviewed a t k v m) :: mid)
      (inbound.evStream x) (.reviewed a t k v m) ("reviewer", k, a) (by simp) (by simp [hs]) (by simp [notes]))⟩
  cases x <;> simp_all [incoming, item]

/-! ## A decision is final -/

def decides : TriageEvent → Bool
  | .replied .. | .ignored .. => true
  | _ => false

theorem decided_of_decides {d : TriageEvent} (hd : decides d = true) {w1 w2 : List Note} :
    decided (w1 ++ notes d ++ w2) (item d) = true := by
  cases d <;> simp_all [decides, decided, item, noted, notes]

theorem a_triage_is_decided_once {pre post : inbound.XLog} {d : TriageEvent} (hd : decides d = true)
    (h : ValidX (pre ++ .inr d :: post)) : decided ((evs pre (inbound.evStream d)).flatMap notes) (item d) = false := by
  have := h.holdsNamed "triage_is_decided_once"
  dsimp only at this
  cases d <;> simp_all [decides, item]

theorem no_event_once_decided {pre post : inbound.XLog} {x : TriageEvent}
    (h : ValidX (pre ++ .inr x :: post))
    (hex : noted ((evs pre (inbound.evStream x)).flatMap notes) "triage" (item x) = true)
    (hdec : decided ((evs pre (inbound.evStream x)).flatMap notes) (item x) = true) : False := by
  cases x with
  | created a t k u m =>
    have := h.holdsNamed "triage_id_must_be_new"
    dsimp only at this
    simp_all [item]
  | replied a t k e m =>
    have := h.holdsNamed "triage_is_decided_once"
    dsimp only at this
    simp_all [item]
  | ignored a t k m =>
    have := h.holdsNamed "triage_is_decided_once"
    dsimp only at this
    simp_all [item]
  | _ =>
    have := h.holdsNamed "triage_must_be_undecided"
    dsimp only at this
    simp_all [item]

theorem decision_admitted {pre post : inbound.XLog} {d : TriageEvent} (hd : decides d = true)
    (h : ValidX (pre ++ .inr d :: post)) :
    noted ((evs pre (inbound.evStream d)).flatMap notes) "triage" (item d) = true := by
  have h3 := h.holdsNamed "triage_must_exist"
  dsimp only at h3
  simp only [read_notes] at h3
  cases d <;> simp only [decides, Bool.false_eq_true] at hd <;> simpa [item] using h3

/-- **Nothing follows a decision**: after a triage is replied or ignored, no triage event about it is accepted. -/
theorem nothing_follows_a_decision {pre mid post : inbound.XLog} {d x : TriageEvent} (hd : decides d = true)
    (h : ValidX (pre ++ .inr d :: mid ++ .inr x :: post))
    (hs : inbound.evStream x = inbound.evStream d) (hk : item x = item d) : False := by
  have hd' : ValidX (pre ++ .inr d :: (mid ++ .inr x :: post)) := by simpa [List.append_assoc] using h
  have hw : (evs (pre ++ .inr d :: mid) (inbound.evStream x)).flatMap notes =
      (evs pre (inbound.evStream d)).flatMap notes ++ notes d ++ (evs mid (inbound.evStream d)).flatMap notes := by
    rw [hs]; simp [evs_append, evs_cons_inr, List.flatMap_append, List.flatMap_cons, List.append_assoc]
  have hex := decision_admitted hd hd'
  refine no_event_once_decided h ?_ ?_ <;> rw [hw, hk]
  · simp only [noted, List.any_append, Bool.or_eq_true]; exact Or.inl (Or.inl (by simpa [noted] using hex))
  · exact decided_of_decides hd

/-! ## The creator can always ignore -/

/-- **The creator can always ignore**: a theorem of acceptance. After any valid log in which stream `t` is open and
not closed with opener `a`, and triage `k` is created on it and not decided, the service accepts `a`'s `triage.ignore`
of `k`, whatever else has or has not happened. These five hypotheses are everything the ignore's rules read
(`triage_must_exist`, `only_opener_can_decide`, `triage_is_decided_once`) together with the core's admission. -/
theorem the_creator_can_always_ignore {pre : inbound.XLog} (h : ValidX pre) {a t k : Id} {m : Meta}
    (hopen : Past.opened (cores pre) t = true) (hclosed : Past.closed (cores pre) t = false)
    (hopener : Past.opener (cores pre) t = some a)
    (hk : noted ((evs pre t).flatMap notes) "triage" k = true)
    (hdec : decided ((evs pre t).flatMap notes) k = false) :
    inbound.service.respond pre (.inr (a, .ignore t k m, [])) = .accepted (.inr (.ignored a t k m)) := by
  refine Service.respond_accepted_iff.mpr ⟨rfl, ?_⟩
  have hv : ValidX (pre ++ [.inr (.ignored a t k m)]) := by
    refine (ValidX.snoc_inr_iff h).mpr ⟨?_, ?_, ?_, ?_⟩
    · show (Past.view (cores pre) t).admits a = none
      exact View.admits_none.mpr ⟨by simpa using hopen, by simpa using hclosed⟩
    · rfl
    · intro r hr
      simp only [inbound, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        <;> simp [hopener, hk, hdec, Past.view]
    · intro r hr
      simp at hr
  exact (Service.Valid.inv hv).2

/-! ## The core's guarantees, here -/

theorem only_the_opener_closes_the_stream {pre post : inbound.XLog} {a t : Id} {m : Meta}
    (h : ValidX (pre ++ .inl (Event.streamClosed a t m) :: post)) : Past.opener (cores pre) t = some a :=
  h.close_by_opener

theorem nothing_follows_a_close {pre mid post : inbound.XLog} {a t : Id} {m : Meta} {x : inbound.XEv}
    (h : ValidX (pre ++ .inl (Event.streamClosed a t m) :: mid ++ x :: post)) : streamX x ≠ t := h.close_final

end EmailTriage
