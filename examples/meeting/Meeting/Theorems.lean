-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Meeting.Layer

/-!
# The meeting layer's guarantees

Each holds of every valid log of the layer (`ValidX`), and follows from the rules that held when its events were
accepted (`ValidX.holdsNamed`), from the core's opener (`v.opener`), and from the core's theorems through `h.cores`.
Named as the sentence each proves. Every permission rests on the opener: the opener creates, solicits and decides
(`every_meeting_is_created_by_the_opener`, `every_solicitation_is_by_the_opener`, `the_send_is_by_the_opener`,
`the_discard_is_by_the_opener`); the drafters are whom the opener solicited (`every_draft_is_by_a_solicited_drafter`);
the three roles never meet (`roles_are_disjoint`); no URL a drafter or composer names is named twice on a meeting
(`urls_are_distinct`); the first compose cuts off drafting (`nothing_is_solicited_or_drafted_after_the_compose`);
nothing about a meeting follows its decision (`nothing_follows_a_decision`). Every composed URL carries a pin
(`every_composed_url_is_pinned`), and so does every sent URL, which is the latest composed one
(`every_sent_file_is_pinned`). The proof sees the form of the pin and never the bytes. And one theorem of acceptance: the opener's send of an
undecided meeting at its latest composed URL is accepted (`the_creator_can_always_send`).
-/

namespace Meeting
open Provenstream Provenstream.Layer

/-! ## What the memory reads: the notes of the stream's meeting events -/

theorem foldl_addNotes (past : List MeetingEvent) (st : List Note) : past.foldl addNotes st = st ++ past.flatMap notes := by
  induction past generalizing st with
  | nil => simp
  | cons e es ih => simp [ih, addNotes, List.append_assoc]

/-- What the layer's rules read of the stream's meeting events is their notes, in order. -/
@[simp] theorem read_notes (past : List MeetingEvent) : past.foldl addNotes [] = past.flatMap notes := by
  simp [foldl_addNotes]

/-- A note of the stream's meeting events is a note of a meeting event of that stream in the log. -/
theorem mem_notes_evs {log : meetings.XLog} {t : Id} {n : Note} (h : n ∈ (evs log t).flatMap notes) :
    ∃ e, .inr e ∈ log ∧ meetings.evStream e = t ∧ n ∈ notes e := by
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

theorem meeting_note {e : MeetingEvent} {k q : String} (h : ("meeting", k, q) ∈ notes e) :
    ∃ a t m, e = .created a t k m := by
  cases e <;> simp_all [notes]

theorem drafter_note {e : MeetingEvent} {k q : String} (h : ("drafter", k, q) ∈ notes e) :
    ∃ a t m, e = .solicited a t k q m := by
  cases e <;> simp_all [notes]

theorem composer_note {e : MeetingEvent} {k q : String} (h : ("composer", k, q) ∈ notes e) :
    ∃ t u x s m, e = .composed q t k u x s m := by
  cases e <;> simp_all [notes]

theorem composed_note {e : MeetingEvent} {k q : String} (h : ("composed", k, q) ∈ notes e) :
    ∃ a t x s m, e = .composed a t k q x s m := by
  cases e <;> simp_all [notes]

/-- The stream's meeting events before an event, noted drafter `d` of `k` only by an `meeting.solicited` event in the
log. -/
theorem solicited_of_contains {pre : meetings.XLog} {t k d : Id}
    (h : ((evs pre t).flatMap notes).contains ("drafter", k, d) = true) :
    ∃ o m', (.inr (MeetingEvent.solicited o t k d m') : meetings.XEv) ∈ pre := by
  obtain ⟨e, hm, hs, hn⟩ := mem_notes_evs (List.contains_iff_mem.mp h)
  obtain ⟨o, t', m', rfl⟩ := drafter_note hn
  simp only [Commands.evStream_mk] at hs
  subst hs
  exact ⟨o, m', hm⟩

/-- The stream's meeting events before an event, noted composer `r` of `k` only by an `meeting.composed` event in the
log. -/
theorem composed_of_contains {pre : meetings.XLog} {t k r : Id}
    (h : ((evs pre t).flatMap notes).contains ("composer", k, r) = true) :
    ∃ u x s m', (.inr (MeetingEvent.composed r t k u x s m') : meetings.XEv) ∈ pre := by
  obtain ⟨e, hm, hs, hn⟩ := mem_notes_evs (List.contains_iff_mem.mp h)
  obtain ⟨t', u, x, s, m', rfl⟩ := composer_note hn
  simp only [Commands.evStream_mk] at hs
  subst hs
  exact ⟨u, x, s, m', hm⟩

/-- A note of an event of stream `t` in the log is among the notes the memory reads after it. -/
theorem contains_of_mem (pre : meetings.XLog) (t : Id) (e : MeetingEvent) (n : Note)
    (hm : (.inr e : meetings.XEv) ∈ pre) (hs : meetings.evStream e = t) (hn : n ∈ notes e) :
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

/-! ## Who creates, who solicits, who decides: the opener -/

/-- **Every meeting is created by the opener**: every `meeting.create` in a valid log is by the stream's opener. -/
theorem every_meeting_is_created_by_the_opener {pre post : meetings.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.created a t k m) :: post)) : Past.opener (cores pre) t = some a := by
  have := h.holdsNamed "only_opener_can_create"
  dsimp only at this
  simpa using this

/-- **Every solicitation is by the opener**: every `meeting.solicit` in a valid log is by the stream's opener, so every
drafter was named by the opener. -/
theorem every_solicitation_is_by_the_opener {pre post : meetings.XLog} {a t k d : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.solicited a t k d m) :: post)) : Past.opener (cores pre) t = some a := by
  have := h.holdsNamed "only_opener_can_solicit"
  dsimp only at this
  simpa using this

/-- A solicitation of `d` on `k` in a valid log was made by the stream's opener, as the log before it says. -/
theorem solicitation_by_opener {pre post : meetings.XLog} {o t k d : Id} {m' : Meta}
    (h : ValidX (pre ++ post)) (hm : (.inr (MeetingEvent.solicited o t k d m') : meetings.XEv) ∈ pre) :
    Past.opener (cores pre) t = some o := by
  obtain ⟨p1, p2, rfl⟩ := List.append_of_mem hm
  have hv : ValidX (p1 ++ .inr (MeetingEvent.solicited o t k d m') :: (p2 ++ post)) := by
    simpa [List.append_assoc] using h
  have ho := every_solicitation_is_by_the_opener hv
  simpa [cores] using opener_stays ho (cores (.inr (MeetingEvent.solicited o t k d m') :: p2))

/-- **Every draft is by a solicited drafter**: before every `meeting.draft` by `d` on meeting `k`, the opener solicited
`d` on `k`. -/
theorem every_draft_is_by_a_solicited_drafter {pre post : meetings.XLog} {d t k : Id} {u : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.drafted d t k u m) :: post)) :
    ∃ o m', (.inr (MeetingEvent.solicited o t k d m') : meetings.XEv) ∈ pre ∧ Past.opener (cores pre) t = some o := by
  have := h.holdsNamed "only_solicited_drafters_can_draft"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk] at this
  obtain ⟨o, m', hm⟩ := solicited_of_contains this
  exact ⟨o, m', hm, solicitation_by_opener h hm⟩

/-- **The send is by the opener.** -/
theorem the_send_is_by_the_opener {pre post : meetings.XLog} {a t k : Id} {u : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.sent a t k u m) :: post)) : Past.opener (cores pre) t = some a := by
  have := h.holdsNamed "only_opener_can_decide"
  dsimp only at this
  simpa using this

/-- **The discard is by the opener.** -/
theorem the_discard_is_by_the_opener {pre post : meetings.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.discarded a t k m) :: post)) : Past.opener (cores pre) t = some a := by
  have := h.holdsNamed "only_opener_can_decide"
  dsimp only at this
  simpa using this

/-! ## The roles are disjoint -/

/-- **No drafter is the opener**: every `meeting.solicit` names a drafter other than the stream's opener, who never
changes, so the opener of the whole log is not it. -/
theorem no_drafter_is_the_opener {pre post : meetings.XLog} {o t k d : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.solicited o t k d m) :: post)) :
    Past.opener (cores (pre ++ .inr (.solicited o t k d m) :: post)) t ≠ some d := by
  have h6 := h.holdsNamed "drafter_must_not_be_the_opener"
  dsimp only at h6
  have ho := every_solicitation_is_by_the_opener h
  simp only [Past.view_opener, bne_iff_ne, ne_eq] at h6
  have : Past.opener (cores (pre ++ .inr (.solicited o t k d m) :: post)) t = some o := by
    simpa [cores] using opener_stays ho (cores (.inr (MeetingEvent.solicited o t k d m) :: post))
  rw [this]; intro hc; exact h6 (ho.trans hc)

/-- **No composer is the opener**: every `meeting.compose` is by a principal other than the stream's opener. -/
theorem no_composer_is_the_opener {pre post : meetings.XLog} {r t k : Id} {u x s : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.composed r t k u x s m) :: post)) : Past.opener (cores pre) t ≠ some r := by
  have := h.holdsNamed "composer_must_not_be_the_opener"
  dsimp only at this
  simpa using this

/-- **No drafter is a composer**: no valid log solicits `d` on meeting `k` and has `d` compose `k`, in either order
(`composer_must_not_be_a_drafter` refuses the compose after the solicitation, `drafter_must_not_be_a_composer` the
solicitation after the compose). -/
theorem no_drafter_is_a_composer {log : meetings.XLog} (h : ValidX log) {o t k d : Id} {u' x s : String} {m m' : Meta}
    (hb : (.inr (MeetingEvent.solicited o t k d m) : meetings.XEv) ∈ log)
    (hr : (.inr (MeetingEvent.composed d t k u' x s m') : meetings.XEv) ∈ log) : False := by
  rcases mem_mem_split hb hr (by simp) with ⟨l1, l2, l3, rfl⟩ | ⟨l1, l2, l3, rfl⟩
  · -- the solicitation first: the compose reads the drafter note
    have hv : ValidX ((l1 ++ .inr (MeetingEvent.solicited o t k d m) :: l2) ++ .inr (MeetingEvent.composed d t k u' x s m') :: l3) := by
      simpa [List.append_assoc] using h
    have := hv.holdsNamed "composer_must_not_be_a_drafter"
    dsimp only at this
    simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at this
    rw [contains_of_mem _ t (.solicited o t k d m) ("drafter", k, d) (by simp) (by simp) (by simp [notes])] at this
    exact Bool.noConfusion this
  · -- the compose first: the solicitation reads the composer note
    have hv : ValidX ((l1 ++ .inr (MeetingEvent.composed d t k u' x s m') :: l2) ++ .inr (MeetingEvent.solicited o t k d m) :: l3) := by
      simpa [List.append_assoc] using h
    have := hv.holdsNamed "drafter_must_not_be_a_composer"
    dsimp only at this
    simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at this
    rw [contains_of_mem _ t (.composed d t k u' x s m') ("composer", k, d) (by simp) (by simp) (by simp [notes])] at this
    exact Bool.noConfusion this

/-- **The roles are disjoint**: a drafter of a meeting is neither the stream's opener nor ever a composer of that
meeting, and a composer is not the opener (`no_drafter_is_the_opener`, `no_drafter_is_a_composer`,
`no_composer_is_the_opener`). -/
theorem roles_are_disjoint {log : meetings.XLog} (h : ValidX log) {o t k d : Id} {m : Meta}
    (hb : (.inr (MeetingEvent.solicited o t k d m) : meetings.XEv) ∈ log) :
    Past.opener (cores log) t ≠ some d ∧ ∀ u' x s m', (.inr (MeetingEvent.composed d t k u' x s m') : meetings.XEv) ∉ log := by
  refine ⟨?_, fun u' x s m' hr => no_drafter_is_a_composer h hb hr⟩
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hb
  exact no_drafter_is_the_opener h

/-! ## Each step once, every meeting created -/

/-- **A meeting is created once** per stream: its id is new when it is created. -/
theorem an_meeting_is_created_once {pre post : meetings.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.created a t k m) :: post)) :
    noted ((evs pre t).flatMap notes) "meeting" k = false := by
  have := h.holdsNamed "meeting_id_must_be_new"
  dsimp only at this
  simpa using this

/-- The meeting a meeting event is about. -/
def item : MeetingEvent → Id
  | .created _ _ k _ | .solicited _ _ k _ _ | .drafted _ _ k _ _ | .composed _ _ k _ _ _ _
  | .sent _ _ k _ _ | .discarded _ _ k _ => k

/-- **Every event names a created meeting**: the meeting of every `meeting.solicit`, `meeting.draft`, `meeting.compose`,
`meeting.send` and `meeting.discard` was created earlier on the same stream. -/
theorem every_event_names_a_created_meeting {pre post : meetings.XLog} {x : MeetingEvent} {t : Id}
    (h : ValidX (pre ++ .inr x :: post)) (hs : meetings.evStream x = t)
    (hx : match x with | .created .. => False | _ => True) :
    ∃ a m, (.inr (MeetingEvent.created a t (item x) m) : meetings.XEv) ∈ pre := by
  subst hs
  have := h.holdsNamed "meeting_must_exist"
  dsimp only at this
  simp only [read_notes] at this
  have hn : noted ((evs pre (meetings.evStream x)).flatMap notes) "meeting" (item x) = true := by
    cases x <;> simp_all [item]
  obtain ⟨q, hq⟩ := noted_iff.mp hn
  obtain ⟨e, hm, hs', hn'⟩ := mem_notes_evs hq
  obtain ⟨a, t', m, rfl⟩ := meeting_note hn'
  simp only [Commands.evStream_mk] at hs'
  subst hs'
  exact ⟨a, m, hm⟩

/-- **A drafter is solicited once** per meeting. -/
theorem a_drafter_is_solicited_once {pre post : meetings.XLog} {a t k d : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.solicited a t k d m) :: post)) :
    ∀ o m', (.inr (MeetingEvent.solicited o t k d m') : meetings.XEv) ∉ pre := by
  have := h.holdsNamed "drafter_is_solicited_once"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at this
  intro o m' hm
  rw [contains_of_mem pre t (.solicited o t k d m') ("drafter", k, d) hm (by simp) (by simp [notes])] at this
  exact Bool.noConfusion this

/-! ## The URLs of a meeting are distinct -/

/-- The URL a draft or a compose names of its meeting. A send repeats a composed one by design. -/
def urlOf : MeetingEvent → Option (Id × String)
  | .drafted _ _ k u _ | .composed _ _ k u _ _ _ => some (k, u)
  | .created .. | .solicited .. | .sent .. | .discarded .. => none

/-- An event's URL note is among its notes. -/
theorem url_note {x : MeetingEvent} {k u : String} (hx : urlOf x = some (k, u)) :
    ∃ what, namesUrl what = true ∧ (what, k, u) ∈ notes x := by
  cases x <;> simp_all [urlOf, notes, namesUrl]

/-- After an event naming a URL of `k`, the stream's notes say `k` is a meeting: `meeting_must_exist` held for it. -/
theorem meeting_noted_after {l1 l2 post : meetings.XLog} {x : MeetingEvent} {k u : String}
    (h : ValidX (l1 ++ .inr x :: (l2 ++ post))) (hx : urlOf x = some (k, u)) :
    noted ((evs (l1 ++ .inr x :: l2) (meetings.evStream x)).flatMap notes) "meeting" k = true := by
  have hw : (evs (l1 ++ .inr x :: l2) (meetings.evStream x)).flatMap notes =
      (evs l1 (meetings.evStream x)).flatMap notes ++ (notes x ++ (evs l2 (meetings.evStream x)).flatMap notes) := by
    simp [evs_append, evs_cons_inr, List.flatMap_append, List.flatMap_cons]
  rw [hw]
  cases x with
  | created => simp [urlOf] at hx
  | solicited => simp [urlOf] at hx
  | sent => simp [urlOf] at hx
  | discarded => simp [urlOf] at hx
  | _ =>
    have h3 := h.holdsNamed "meeting_must_exist"
    dsimp only at h3
    simp only [read_notes] at h3
    simp only [urlOf, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, -⟩ := hx
    exact noted_mono h3

/-- **The URLs are distinct**: no two events of a valid log, one before the other, name the same draft or composed
URL of the same meeting on the same stream. -/
theorem urls_are_distinct {l1 l2 l3 : meetings.XLog} {x y : MeetingEvent} {k u : String}
    (h : ValidX (l1 ++ .inr x :: l2 ++ .inr y :: l3)) (hs : meetings.evStream y = meetings.evStream x)
    (hx : urlOf x = some (k, u)) (hy : urlOf y = some (k, u)) : False := by
  obtain ⟨what, hw, hn⟩ := url_note hx
  have hnamed : urlNamed ((evs (l1 ++ .inr x :: l2) (meetings.evStream y)).flatMap notes) k u = true := by
    simp only [urlNamed, List.any_eq_true]
    exact ⟨(what, k, u), List.contains_iff_mem.mp
      (contains_of_mem (l1 ++ .inr x :: l2) (meetings.evStream y) x (what, k, u) (by simp) hs.symm hn), by simp [hw]⟩
  cases y with
  | created => simp [urlOf] at hy
  | solicited => simp [urlOf] at hy
  | sent => simp [urlOf] at hy
  | discarded => simp [urlOf] at hy
  | _ =>
    have h4 := h.holdsNamed "urls_must_be_unique"
    dsimp only at h4
    simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at h4
    simp only [Commands.evStream_mk] at hnamed
    simp only [urlOf, Option.some.injEq, Prod.mk.injEq] at hy
    rw [hy.1, hy.2, hnamed] at h4
    exact Bool.noConfusion h4

/-- **No composed file is a drafter's**: no valid log has a draft and a compose of the same meeting naming the
same URL, in either order. -/
theorem no_composed_url_is_a_drafters {log : meetings.XLog} (h : ValidX log) {d r t k : Id} {u x s : String}
    {m m' : Meta} (hp : (.inr (MeetingEvent.drafted d t k u m) : meetings.XEv) ∈ log)
    (hr : (.inr (MeetingEvent.composed r t k u x s m') : meetings.XEv) ∈ log) : False := by
  rcases mem_mem_split hp hr (by simp) with ⟨l1, l2, l3, rfl⟩ | ⟨l1, l2, l3, rfl⟩
  · exact urls_are_distinct h rfl (x := .drafted d t k u m) rfl rfl
  · exact urls_are_distinct h rfl (x := .composed r t k u x s m') rfl rfl

/-! ## Every composed URL carries a pin, and every sent file is one of them -/

/-- **Every composed URL is pinned**: the URL of every `meeting.compose` in a valid log carries a pin. -/
theorem every_composed_url_is_pinned {pre post : meetings.XLog} {a t k : Id} {u x s : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.composed a t k u x s m) :: post)) : pinned u = true := by
  have := h.holdsNamed "composed_url_must_be_pinned"
  dsimp only at this
  simpa using this

/-- What the fold behind `lastComposed` finds is its start, or a composed note of `k`. -/
theorem lastComposed_foldl (w : List Note) (k u : String) (acc : Option String)
    (h : w.foldl (fun acc n => if n.1 == "composed" && n.2.1 == k then some n.2.2 else acc) acc = some u) :
    acc = some u ∨ ("composed", k, u) ∈ w := by
  induction w generalizing acc with
  | nil => exact Or.inl (by simpa using h)
  | cons n ns ih =>
    simp only [List.foldl_cons] at h
    rcases ih _ h with h1 | h1
    · by_cases hc : n.1 == "composed" && n.2.1 == k
      · simp only [hc, ite_true, Option.some.injEq] at h1
        right
        obtain ⟨f, k', q⟩ := n
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        subst h1
        exact List.mem_cons_self
      · simp only [hc, Bool.false_eq_true, ite_false] at h1
        exact Or.inl h1
    · exact Or.inr (List.mem_cons_of_mem _ h1)

/-- The latest composed URL is a composed note. -/
theorem mem_of_lastComposed {w : List Note} {k u : String} (h : lastComposed w k = some u) :
    ("composed", k, u) ∈ w := by
  rcases lastComposed_foldl w k u none h with h1 | h1
  · cases h1
  · exact h1

/-- **The sent file was composed**: before every `meeting.send` of `k` at `u`, a compose of `k` named `u`. -/
theorem the_sent_file_was_composed {pre post : meetings.XLog} {a t k : Id} {u : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.sent a t k u m) :: post)) :
    ∃ r x s m', (.inr (MeetingEvent.composed r t k u x s m') : meetings.XEv) ∈ pre := by
  have := h.holdsNamed "sent_must_be_the_latest_composed"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk, beq_iff_eq] at this
  obtain ⟨e, hm, hs, hn⟩ := mem_notes_evs (mem_of_lastComposed this)
  obtain ⟨r, t', x, s, m', rfl⟩ := composed_note hn
  simp only [Commands.evStream_mk] at hs
  subst hs
  exact ⟨r, x, s, m', hm⟩

/-- **Every sent file is pinned**: the URL of every `meeting.send` in a valid log is the URL of a compose, and it carries a
pin. Whoever reads the URL checks the bytes against that pin. The proof cannot see them. -/
theorem every_sent_file_is_pinned {pre post : meetings.XLog} {a t k : Id} {u : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.sent a t k u m) :: post)) : pinned u = true := by
  obtain ⟨r, x, s, m', hm⟩ := the_sent_file_was_composed h
  obtain ⟨p1, p2, rfl⟩ := List.append_of_mem hm
  have hv : ValidX (p1 ++ .inr (MeetingEvent.composed r t k u x s m') :: (p2 ++ .inr (MeetingEvent.sent a t k u m) :: post)) := by
    simpa [List.append_assoc] using h
  exact every_composed_url_is_pinned hv

/-! ## The first composed file cuts off drafting -/

/-- Whether a meeting event brings a draft in: a solicitation or a draft. -/
def incoming : MeetingEvent → Bool
  | .solicited .. | .drafted .. => true
  | _ => false

/-- **Nothing is solicited or drafted after the compose**: after `meeting.compose` of `k`, no `meeting.solicit` or
`meeting.draft` of `k` is accepted on the stream. -/
theorem nothing_is_solicited_or_drafted_after_the_compose {pre mid post : meetings.XLog} {a t k : Id} {u y s : String}
    {m : Meta} {x : MeetingEvent}
    (h : ValidX (pre ++ .inr (.composed a t k u y s m) :: mid ++ .inr x :: post)) (hs : meetings.evStream x = t)
    (hk : item x = k) (hx : incoming x = true) : False := by
  have hv : ValidX ((pre ++ .inr (MeetingEvent.composed a t k u y s m) :: mid) ++ .inr x :: post) := by
    simpa [List.append_assoc] using h
  have h9 := hv.holdsNamed "meeting_must_not_be_composed"
  dsimp only at h9
  simp only [read_notes] at h9
  have hp : noted ((evs (pre ++ .inr (MeetingEvent.composed a t k u y s m) :: mid) (meetings.evStream x)).flatMap notes) "composed" k = true :=
    noted_iff.mpr ⟨u, List.contains_iff_mem.mp (contains_of_mem (pre ++ .inr (MeetingEvent.composed a t k u y s m) :: mid)
      (meetings.evStream x) (.composed a t k u y s m) ("composed", k, u) (by simp) (by simp [hs]) (by simp [notes]))⟩
  cases x <;> simp_all [incoming, item]

/-! ## A decision is final -/

/-- Whether a meeting event decides its meeting: a send or a discard. -/
def decides : MeetingEvent → Bool
  | .sent .. | .discarded .. => true
  | _ => false

/-- A decision's note says its meeting is decided. -/
theorem decided_of_decides {d : MeetingEvent} (hd : decides d = true) {w1 w2 : List Note} :
    decided (w1 ++ notes d ++ w2) (item d) = true := by
  cases d <;> simp_all [decides, decided, item, noted, notes]

/-- **A meeting is decided once**: before every `meeting.send` or `meeting.discard` of `k`, `k` was not decided. -/
theorem an_meeting_is_decided_once {pre post : meetings.XLog} {d : MeetingEvent} (hd : decides d = true)
    (h : ValidX (pre ++ .inr d :: post)) : decided ((evs pre (meetings.evStream d)).flatMap notes) (item d) = false := by
  have := h.holdsNamed "meeting_is_decided_once"
  dsimp only at this
  cases d <;> simp_all [decides, item]

/-- No meeting event about a meeting is accepted once the stream's notes say the meeting exists and is decided: not a
creation (`meeting_id_must_be_new`), not a solicitation, draft or compose (`meeting_must_be_undecided`), and not another
decision (`meeting_is_decided_once`). -/
theorem no_event_once_decided {pre post : meetings.XLog} {x : MeetingEvent}
    (h : ValidX (pre ++ .inr x :: post))
    (hex : noted ((evs pre (meetings.evStream x)).flatMap notes) "meeting" (item x) = true)
    (hdec : decided ((evs pre (meetings.evStream x)).flatMap notes) (item x) = true) : False := by
  cases x with
  | created a t k m =>
    have := h.holdsNamed "meeting_id_must_be_new"
    dsimp only at this
    simp_all [item]
  | sent a t k u m =>
    have := h.holdsNamed "meeting_is_decided_once"
    dsimp only at this
    simp_all [item]
  | discarded a t k m =>
    have := h.holdsNamed "meeting_is_decided_once"
    dsimp only at this
    simp_all [item]
  | _ =>
    have := h.holdsNamed "meeting_must_be_undecided"
    dsimp only at this
    simp_all [item]

/-- A decision was accepted: its meeting existed, as the notes before it say. -/
theorem decision_admitted {pre post : meetings.XLog} {d : MeetingEvent} (hd : decides d = true)
    (h : ValidX (pre ++ .inr d :: post)) :
    noted ((evs pre (meetings.evStream d)).flatMap notes) "meeting" (item d) = true := by
  have h3 := h.holdsNamed "meeting_must_exist"
  dsimp only at h3
  simp only [read_notes] at h3
  cases d <;> simp only [decides, Bool.false_eq_true] at hd <;> simpa [item] using h3

/-- **Nothing follows a decision**: after a meeting is sent or discarded, no meeting event about it is accepted on the
stream (`no_event_once_decided`). -/
theorem nothing_follows_a_decision {pre mid post : meetings.XLog} {d x : MeetingEvent} (hd : decides d = true)
    (h : ValidX (pre ++ .inr d :: mid ++ .inr x :: post))
    (hs : meetings.evStream x = meetings.evStream d) (hk : item x = item d) : False := by
  -- `::` binds tighter than `++`: `h` is on `(pre ++ .inr d :: mid) ++ .inr x :: post`
  have hd' : ValidX (pre ++ .inr d :: (mid ++ .inr x :: post)) := by simpa [List.append_assoc] using h
  have hw : (evs (pre ++ .inr d :: mid) (meetings.evStream x)).flatMap notes =
      (evs pre (meetings.evStream d)).flatMap notes ++ notes d ++ (evs mid (meetings.evStream d)).flatMap notes := by
    rw [hs]; simp [evs_append, evs_cons_inr, List.flatMap_append, List.flatMap_cons, List.append_assoc]
  have hex := decision_admitted hd hd'
  refine no_event_once_decided h ?_ ?_ <;> rw [hw, hk]
  · simp only [noted, List.any_append, Bool.or_eq_true]; exact Or.inl (Or.inl (by simpa [noted] using hex))
  · exact decided_of_decides hd

/-! ## The creator can always send -/

/-- **The creator can always send**: a theorem of acceptance, not of valid logs. After any valid log in which stream
`t` is open and not closed with opener `a`, meeting `k` is created on it and not decided, and `u` is the URL of its latest
compose, the service accepts `a`'s `meeting.send` of `k` at `u`, whatever else has or has not happened. These six
hypotheses are everything the send's rules read, together with the core's admission. -/
theorem the_creator_can_always_send {pre : meetings.XLog} (h : ValidX pre) {a t k : Id} {u : String} {m : Meta}
    (hopen : Past.opened (cores pre) t = true) (hclosed : Past.closed (cores pre) t = false)
    (hopener : Past.opener (cores pre) t = some a)
    (hk : noted ((evs pre t).flatMap notes) "meeting" k = true)
    (hu : lastComposed ((evs pre t).flatMap notes) k = some u)
    (hdec : decided ((evs pre t).flatMap notes) k = false) :
    meetings.service.respond pre (.inr (a, .send t k u m, [])) = .accepted (.inr (.sent a t k u m)) := by
  refine Service.respond_accepted_iff.mpr ⟨rfl, ?_⟩
  have hv : ValidX (pre ++ [.inr (.sent a t k u m)]) := by
    refine (ValidX.snoc_inr_iff h).mpr ⟨?_, ?_, ?_, ?_⟩
    · show (Past.view (cores pre) t).admits a = none
      exact View.admits_none.mpr ⟨by simpa using hopen, by simpa using hclosed⟩
    · rfl
    · intro r hr
      simp only [meetings, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        <;> simp [hopener, hk, hu, hdec, Past.view]
    · intro r hr
      simp at hr
  exact (Service.Valid.inv hv).2

/-! ## The core's guarantees, here -/

/-- **Only the opener closes the stream** of meetings (`Layer.ValidX.close_by_opener`). -/
theorem only_the_opener_closes_the_stream {pre post : meetings.XLog} {a t : Id} {m : Meta}
    (h : ValidX (pre ++ .inl (Event.streamClosed a t m) :: post)) : Past.opener (cores pre) t = some a :=
  h.close_by_opener

/-- **Nothing follows a close**: nothing, of the core or of the layer, is appended to a stream after its close
(`Layer.ValidX.close_final`). -/
theorem nothing_follows_a_close {pre mid post : meetings.XLog} {a t : Id} {m : Meta} {x : meetings.XEv}
    (h : ValidX (pre ++ .inl (Event.streamClosed a t m) :: mid ++ x :: post)) : streamX x ≠ t := h.close_final

end Meeting
