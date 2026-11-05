-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Email.Layer

/-!
# The email layer's guarantees

Each holds of every valid log of the layer (`ValidX`), and follows from the rules that held when its events were
accepted (`ValidX.holdsNamed`), from the core's opener (`v.opener`), and from the core's theorems through `h.cores`.
Named as the sentence each proves. Every permission rests on the opener: the opener creates, solicits and decides
(`every_email_is_created_by_the_opener`, `every_solicitation_is_by_the_opener`, `the_send_is_by_the_opener`,
`the_discard_is_by_the_opener`); the drafters are whom the opener solicited (`every_draft_is_by_a_solicited_drafter`);
the three roles never meet (`roles_are_disjoint`); no `.eml` is named twice on an email (`emls_are_distinct`); the first
composed draft cuts off drafting (`nothing_is_solicited_or_drafted_after_the_compose`); nothing about an email follows
its decision (`nothing_follows_a_decision`). And one theorem of acceptance rather than of valid logs: the opener's send
of an undecided email at a new `.eml` is accepted whatever else has or has not happened (`the_creator_can_always_send`).
-/

namespace Email
open Provenstream Provenstream.Layer

/-! ## What the memory reads: the notes of the stream's email events -/

theorem foldl_addNotes (past : List EmailEvent) (st : List Note) : past.foldl addNotes st = st ++ past.flatMap notes := by
  induction past generalizing st with
  | nil => simp
  | cons e es ih => simp [ih, addNotes, List.append_assoc]

/-- What the layer's rules read of the stream's email events is their notes, in order. -/
@[simp] theorem read_notes (past : List EmailEvent) : past.foldl addNotes [] = past.flatMap notes := by
  simp [foldl_addNotes]

/-- A note of the stream's email events is a note of an email event of that stream in the log. -/
theorem mem_notes_evs {log : outbound.XLog} {t : Id} {n : Note} (h : n ∈ (evs log t).flatMap notes) :
    ∃ e, .inr e ∈ log ∧ outbound.evStream e = t ∧ n ∈ notes e := by
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

/-- A note of an email's replied-to message: the email is a reply, and the note names the message. -/
@[simp] theorem mem_replyNotes {k : String} {r : Option String} {n : Note} :
    n ∈ replyNotes k r ↔ ∃ v, r = some v ∧ n = ("reply_to", k, v) := by
  cases r <;> simp [replyNotes]

theorem email_note {e : EmailEvent} {k q : String} (h : ("email", k, q) ∈ notes e) :
    ∃ a t r m, e = .created a t k r m := by
  cases e <;> simp_all [notes]

theorem drafter_note {e : EmailEvent} {k q : String} (h : ("drafter", k, q) ∈ notes e) :
    ∃ a t m, e = .solicited a t k q m := by
  cases e <;> simp_all [notes]

theorem composer_note {e : EmailEvent} {k q : String} (h : ("composer", k, q) ∈ notes e) :
    ∃ t u s m, e = .composed q t k u s m := by
  cases e <;> simp_all [notes]

theorem composed_note {e : EmailEvent} {k q : String} (h : ("composed", k, q) ∈ notes e) :
    ∃ a t s m, e = .composed a t k q s m := by
  cases e <;> simp_all [notes]

/-- The stream's email events before an event, noted drafter `d` of `k` only by an `email.solicited` event in the
log. -/
theorem solicited_of_contains {pre : outbound.XLog} {t k d : Id}
    (h : ((evs pre t).flatMap notes).contains ("drafter", k, d) = true) :
    ∃ o m', (.inr (EmailEvent.solicited o t k d m') : outbound.XEv) ∈ pre := by
  obtain ⟨e, hm, hs, hn⟩ := mem_notes_evs (List.contains_iff_mem.mp h)
  obtain ⟨o, t', m', rfl⟩ := drafter_note hn
  simp only [Commands.evStream_mk] at hs
  subst hs
  exact ⟨o, m', hm⟩

/-- The stream's email events before an event, noted composer `r` of `k` only by an `email.composed` event in the
log. -/
theorem composed_of_contains {pre : outbound.XLog} {t k r : Id}
    (h : ((evs pre t).flatMap notes).contains ("composer", k, r) = true) :
    ∃ u s m', (.inr (EmailEvent.composed r t k u s m') : outbound.XEv) ∈ pre := by
  obtain ⟨e, hm, hs, hn⟩ := mem_notes_evs (List.contains_iff_mem.mp h)
  obtain ⟨t', u, s, m', rfl⟩ := composer_note hn
  simp only [Commands.evStream_mk] at hs
  subst hs
  exact ⟨u, s, m', hm⟩

/-- A note of an event of stream `t` in the log is among the notes the memory reads after it. -/
theorem contains_of_mem (pre : outbound.XLog) (t : Id) (e : EmailEvent) (n : Note)
    (hm : (.inr e : outbound.XEv) ∈ pre) (hs : outbound.evStream e = t) (hn : n ∈ notes e) :
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

/-- **Every email is created by the opener**: every `email.create` in a valid log is by the stream's opener. -/
theorem every_email_is_created_by_the_opener {pre post : outbound.XLog} {a t k : Id} {r : Option String} {m : Meta}
    (h : ValidX (pre ++ .inr (.created a t k r m) :: post)) : Past.opener (cores pre) t = some a := by
  have := h.holdsNamed "only_opener_can_create"
  dsimp only at this
  simpa using this

/-- **Every solicitation is by the opener**: every `email.solicit` in a valid log is by the stream's opener, so every
drafter was named by the opener. -/
theorem every_solicitation_is_by_the_opener {pre post : outbound.XLog} {a t k d : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.solicited a t k d m) :: post)) : Past.opener (cores pre) t = some a := by
  have := h.holdsNamed "only_opener_can_solicit"
  dsimp only at this
  simpa using this

/-- A solicitation of `d` on `k` in a valid log was made by the stream's opener, as the log before it says. -/
theorem solicitation_by_opener {pre post : outbound.XLog} {o t k d : Id} {m' : Meta}
    (h : ValidX (pre ++ post)) (hm : (.inr (EmailEvent.solicited o t k d m') : outbound.XEv) ∈ pre) :
    Past.opener (cores pre) t = some o := by
  obtain ⟨p1, p2, rfl⟩ := List.append_of_mem hm
  have hv : ValidX (p1 ++ .inr (EmailEvent.solicited o t k d m') :: (p2 ++ post)) := by
    simpa [List.append_assoc] using h
  have ho := every_solicitation_is_by_the_opener hv
  simpa [cores] using opener_stays ho (cores (.inr (EmailEvent.solicited o t k d m') :: p2))

/-- **Every draft is by a solicited drafter**: before every `email.draft` by `d` on email `k`, the opener solicited
`d` on `k`. -/
theorem every_draft_is_by_a_solicited_drafter {pre post : outbound.XLog} {d t k : Id} {u : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.drafted d t k u m) :: post)) :
    ∃ o m', (.inr (EmailEvent.solicited o t k d m') : outbound.XEv) ∈ pre ∧ Past.opener (cores pre) t = some o := by
  have := h.holdsNamed "only_solicited_drafters_can_draft"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk] at this
  obtain ⟨o, m', hm⟩ := solicited_of_contains this
  exact ⟨o, m', hm, solicitation_by_opener h hm⟩

/-- **The send is by the opener.** -/
theorem the_send_is_by_the_opener {pre post : outbound.XLog} {a t k : Id} {u : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.sent a t k u m) :: post)) : Past.opener (cores pre) t = some a := by
  have := h.holdsNamed "only_opener_can_decide"
  dsimp only at this
  simpa using this

/-- **The discard is by the opener.** -/
theorem the_discard_is_by_the_opener {pre post : outbound.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.discarded a t k m) :: post)) : Past.opener (cores pre) t = some a := by
  have := h.holdsNamed "only_opener_can_decide"
  dsimp only at this
  simpa using this

/-! ## The roles are disjoint -/

/-- **No drafter is the opener**: every `email.solicit` names a drafter other than the stream's opener, who never
changes, so the opener of the whole log is not it. -/
theorem no_drafter_is_the_opener {pre post : outbound.XLog} {o t k d : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.solicited o t k d m) :: post)) :
    Past.opener (cores (pre ++ .inr (.solicited o t k d m) :: post)) t ≠ some d := by
  have h6 := h.holdsNamed "drafter_must_not_be_the_opener"
  dsimp only at h6
  have ho := every_solicitation_is_by_the_opener h
  simp only [Past.view_opener, bne_iff_ne, ne_eq] at h6
  have : Past.opener (cores (pre ++ .inr (.solicited o t k d m) :: post)) t = some o := by
    simpa [cores] using opener_stays ho (cores (.inr (EmailEvent.solicited o t k d m) :: post))
  rw [this]; intro hc; exact h6 (ho.trans hc)

/-- **No composer is the opener**: every `email.compose` is by a principal other than the stream's opener. -/
theorem no_composer_is_the_opener {pre post : outbound.XLog} {r t k : Id} {u s : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.composed r t k u s m) :: post)) : Past.opener (cores pre) t ≠ some r := by
  have := h.holdsNamed "composer_must_not_be_the_opener"
  dsimp only at this
  simpa using this

/-- **No drafter is a composer**: no valid log solicits `d` on email `k` and has `d` compose `k`, in either order
(`composer_must_not_be_a_drafter` refuses the compose after the solicitation, `drafter_must_not_be_a_composer` the
solicitation after the compose). -/
theorem no_drafter_is_a_composer {log : outbound.XLog} (h : ValidX log) {o t k d : Id} {u' s : String} {m m' : Meta}
    (hb : (.inr (EmailEvent.solicited o t k d m) : outbound.XEv) ∈ log)
    (hr : (.inr (EmailEvent.composed d t k u' s m') : outbound.XEv) ∈ log) : False := by
  rcases mem_mem_split hb hr (by simp) with ⟨l1, l2, l3, rfl⟩ | ⟨l1, l2, l3, rfl⟩
  · -- the solicitation first: the compose reads the drafter note
    have hv : ValidX ((l1 ++ .inr (EmailEvent.solicited o t k d m) :: l2) ++ .inr (EmailEvent.composed d t k u' s m') :: l3) := by
      simpa [List.append_assoc] using h
    have := hv.holdsNamed "composer_must_not_be_a_drafter"
    dsimp only at this
    simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at this
    rw [contains_of_mem _ t (.solicited o t k d m) ("drafter", k, d) (by simp) (by simp) (by simp [notes])] at this
    exact Bool.noConfusion this
  · -- the compose first: the solicitation reads the composer note
    have hv : ValidX ((l1 ++ .inr (EmailEvent.composed d t k u' s m') :: l2) ++ .inr (EmailEvent.solicited o t k d m) :: l3) := by
      simpa [List.append_assoc] using h
    have := hv.holdsNamed "drafter_must_not_be_a_composer"
    dsimp only at this
    simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at this
    rw [contains_of_mem _ t (.composed d t k u' s m') ("composer", k, d) (by simp) (by simp) (by simp [notes])] at this
    exact Bool.noConfusion this

/-- **The roles are disjoint**: a drafter of an email is neither the stream's opener nor ever a composer of that
email, and a composer is not the opener (`no_drafter_is_the_opener`, `no_drafter_is_a_composer`,
`no_composer_is_the_opener`). -/
theorem roles_are_disjoint {log : outbound.XLog} (h : ValidX log) {o t k d : Id} {m : Meta}
    (hb : (.inr (EmailEvent.solicited o t k d m) : outbound.XEv) ∈ log) :
    Past.opener (cores log) t ≠ some d ∧ ∀ u' s m', (.inr (EmailEvent.composed d t k u' s m') : outbound.XEv) ∉ log := by
  refine ⟨?_, fun u' s m' hr => no_drafter_is_a_composer h hb hr⟩
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hb
  exact no_drafter_is_the_opener h

/-! ## Each step once, every email created -/

/-- **An email is created once** per stream: its id is new when it is created. -/
theorem an_email_is_created_once {pre post : outbound.XLog} {a t k : Id} {r : Option String} {m : Meta}
    (h : ValidX (pre ++ .inr (.created a t k r m) :: post)) :
    noted ((evs pre t).flatMap notes) "email" k = false := by
  have := h.holdsNamed "email_id_must_be_new"
  dsimp only at this
  simpa using this

/-- The email an email event is about. -/
def item : EmailEvent → Id
  | .created _ _ k _ _ | .solicited _ _ k _ _ | .drafted _ _ k _ _ | .composed _ _ k _ _ _
  | .sent _ _ k _ _ | .discarded _ _ k _ => k

/-- **Every event names a created email**: the email of every `email.solicit`, `email.draft`, `email.compose`,
`email.send` and `email.discard` was created earlier on the same stream. -/
theorem every_event_names_a_created_email {pre post : outbound.XLog} {x : EmailEvent} {t : Id}
    (h : ValidX (pre ++ .inr x :: post)) (hs : outbound.evStream x = t)
    (hx : match x with | .created .. => False | _ => True) :
    ∃ a r m, (.inr (EmailEvent.created a t (item x) r m) : outbound.XEv) ∈ pre := by
  subst hs
  have := h.holdsNamed "email_must_exist"
  dsimp only at this
  simp only [read_notes] at this
  have hn : noted ((evs pre (outbound.evStream x)).flatMap notes) "email" (item x) = true := by
    cases x <;> simp_all [item]
  obtain ⟨q, hq⟩ := noted_iff.mp hn
  obtain ⟨e, hm, hs', hn'⟩ := mem_notes_evs hq
  obtain ⟨a, t', r, m, rfl⟩ := email_note hn'
  simp only [Commands.evStream_mk] at hs'
  subst hs'
  exact ⟨a, r, m, hm⟩

/-- **A drafter is solicited once** per email. -/
theorem a_drafter_is_solicited_once {pre post : outbound.XLog} {a t k d : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.solicited a t k d m) :: post)) :
    ∀ o m', (.inr (EmailEvent.solicited o t k d m') : outbound.XEv) ∉ pre := by
  have := h.holdsNamed "drafter_is_solicited_once"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at this
  intro o m' hm
  rw [contains_of_mem pre t (.solicited o t k d m') ("drafter", k, d) hm (by simp) (by simp [notes])] at this
  exact Bool.noConfusion this

/-! ## The .eml files of an email are distinct -/

/-- The `.eml` an email event names of its email, if it names one. -/
def emlOf : EmailEvent → Option (Id × String)
  | .created _ _ k (some u) _ | .drafted _ _ k u _ | .composed _ _ k u _ _ | .sent _ _ k u _ => some (k, u)
  | .created _ _ _ none _ | .solicited .. | .discarded .. => none

/-- An event's `.eml` note is among its notes. -/
theorem eml_note {x : EmailEvent} {k u : String} (hx : emlOf x = some (k, u)) :
    ∃ what, namesEml what = true ∧ (what, k, u) ∈ notes x := by
  cases x with
  | created a t k' r m =>
    cases r with
    | none => simp [emlOf] at hx
    | some v =>
      simp only [emlOf, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨"reply_to", rfl, by simp [notes]⟩
  | _ => simp_all [emlOf, notes, namesEml]

/-- An event naming an `.eml` of `k` is about `k`. -/
theorem item_of_eml {x : EmailEvent} {k u : String} (hx : emlOf x = some (k, u)) : item x = k := by
  cases x with
  | created a t k' r m => cases r <;> simp_all [emlOf, item]
  | _ => simp_all [emlOf, item]

/-- After an event naming an `.eml` of `k`, the stream's notes say `k` is an email: the event created it, or
`email_must_exist` held for it. -/
theorem email_noted_after {l1 l2 post : outbound.XLog} {x : EmailEvent} {k u : String}
    (h : ValidX (l1 ++ .inr x :: (l2 ++ post))) (hx : emlOf x = some (k, u)) :
    noted ((evs (l1 ++ .inr x :: l2) (outbound.evStream x)).flatMap notes) "email" k = true := by
  have hw : (evs (l1 ++ .inr x :: l2) (outbound.evStream x)).flatMap notes =
      (evs l1 (outbound.evStream x)).flatMap notes ++ (notes x ++ (evs l2 (outbound.evStream x)).flatMap notes) := by
    simp [evs_append, evs_cons_inr, List.flatMap_append, List.flatMap_cons]
  rw [hw]
  cases x with
  | created a t k' r m =>
    cases r with
    | none => simp [emlOf] at hx
    | some v =>
      simp only [emlOf, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      simp [noted, notes]
  | solicited => simp [emlOf] at hx
  | discarded => simp [emlOf] at hx
  | _ =>
    have h3 := h.holdsNamed "email_must_exist"
    dsimp only at h3
    simp only [read_notes] at h3
    simp only [emlOf, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, -⟩ := hx
    exact noted_mono h3

/-- **The .eml files are distinct**: no two events of a valid log, one before the other, name the same `.eml` of the
same email on the same stream. So the message replied to, every draft, every composed draft and the sent message of
an email are pairwise distinct. -/
theorem emls_are_distinct {l1 l2 l3 : outbound.XLog} {x y : EmailEvent} {k u : String}
    (h : ValidX (l1 ++ .inr x :: l2 ++ .inr y :: l3)) (hs : outbound.evStream y = outbound.evStream x)
    (hx : emlOf x = some (k, u)) (hy : emlOf y = some (k, u)) : False := by
  -- `::` binds tighter than `++`: `h` is on `(l1 ++ .inr x :: l2) ++ .inr y :: l3`
  obtain ⟨what, hw, hn⟩ := eml_note hx
  have hnamed : emlNamed ((evs (l1 ++ .inr x :: l2) (outbound.evStream y)).flatMap notes) k u = true := by
    simp only [emlNamed, List.any_eq_true]
    exact ⟨(what, k, u), List.contains_iff_mem.mp
      (contains_of_mem (l1 ++ .inr x :: l2) (outbound.evStream y) x (what, k, u) (by simp) hs.symm hn), by simp [hw]⟩
  have hk : noted ((evs (l1 ++ .inr x :: l2) (outbound.evStream y)).flatMap notes) "email" k = true := by
    rw [hs]; exact email_noted_after (by simpa [List.append_assoc] using h) hx
  cases y with
  | created a t k' r m =>
    -- a creation of `k` after an event naming an `.eml` of `k`: `k` was already created
    have h2 := h.holdsNamed "email_id_must_be_new"
    dsimp only at h2
    simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at h2
    simp only [Commands.evStream_mk] at hk
    cases r with
    | none => simp [emlOf] at hy
    | some v =>
      simp only [emlOf, Option.some.injEq, Prod.mk.injEq] at hy
      rw [hy.1, hk] at h2
      exact Bool.noConfusion h2
  | solicited => simp [emlOf] at hy
  | discarded => simp [emlOf] at hy
  | _ =>
    have h4 := h.holdsNamed "eml_urls_must_be_unique"
    dsimp only at h4
    simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at h4
    simp only [Commands.evStream_mk] at hnamed
    simp only [emlOf, Option.some.injEq, Prod.mk.injEq] at hy
    rw [hy.1, hy.2, hnamed] at h4
    exact Bool.noConfusion h4

/-- **The sent message is none of the others**: before every `email.send` of `k` at `u`, no note of `k` named `u`:
not the message replied to, not a draft, not a composed draft. -/
theorem the_sent_message_is_none_of_the_others {pre post : outbound.XLog} {a t k : Id} {u : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.sent a t k u m) :: post)) :
    emlNamed ((evs pre t).flatMap notes) k u = false := by
  have := h.holdsNamed "eml_urls_must_be_unique"
  dsimp only at this
  simpa using this

/-- **No composed draft is a drafter's**: no valid log has a draft and a composed draft of the same email naming the
same `.eml`, in either order. -/
theorem no_composed_draft_is_a_drafters {log : outbound.XLog} (h : ValidX log) {d r t k : Id} {u s : String}
    {m m' : Meta} (hp : (.inr (EmailEvent.drafted d t k u m) : outbound.XEv) ∈ log)
    (hr : (.inr (EmailEvent.composed r t k u s m') : outbound.XEv) ∈ log) : False := by
  rcases mem_mem_split hp hr (by simp) with ⟨l1, l2, l3, rfl⟩ | ⟨l1, l2, l3, rfl⟩
  · exact emls_are_distinct h rfl (x := .drafted d t k u m) rfl rfl
  · exact emls_are_distinct h rfl (x := .composed r t k u s m') rfl rfl

/-- **No draft is the message replied to**: no valid log creates an email in reply to a message and has a drafter
hand that message in as a draft, in either order. -/
theorem no_draft_is_the_message_replied_to {log : outbound.XLog} (h : ValidX log) {o d t k : Id} {u : String}
    {m m' : Meta} (hb : (.inr (EmailEvent.created o t k (some u) m) : outbound.XEv) ∈ log)
    (hp : (.inr (EmailEvent.drafted d t k u m') : outbound.XEv) ∈ log) : False := by
  rcases mem_mem_split hb hp (by simp) with ⟨l1, l2, l3, rfl⟩ | ⟨l1, l2, l3, rfl⟩
  · exact emls_are_distinct h rfl (x := .created o t k (some u) m) rfl rfl
  · exact emls_are_distinct h rfl (x := .drafted d t k u m') rfl rfl

/-! ## The first composed draft cuts off drafting -/

/-- Whether an email event brings a draft in: a solicitation or a draft. -/
def incoming : EmailEvent → Bool
  | .solicited .. | .drafted .. => true
  | _ => false

/-- **Nothing is solicited or drafted after the compose**: after `email.compose` of `k`, no `email.solicit` or
`email.draft` of `k` is accepted on the stream. -/
theorem nothing_is_solicited_or_drafted_after_the_compose {pre mid post : outbound.XLog} {a t k : Id} {u s : String}
    {m : Meta} {x : EmailEvent}
    (h : ValidX (pre ++ .inr (.composed a t k u s m) :: mid ++ .inr x :: post)) (hs : outbound.evStream x = t)
    (hk : item x = k) (hx : incoming x = true) : False := by
  have hv : ValidX ((pre ++ .inr (EmailEvent.composed a t k u s m) :: mid) ++ .inr x :: post) := by
    simpa [List.append_assoc] using h
  have h9 := hv.holdsNamed "email_must_not_be_composed"
  dsimp only at h9
  simp only [read_notes] at h9
  have hp : noted ((evs (pre ++ .inr (EmailEvent.composed a t k u s m) :: mid) (outbound.evStream x)).flatMap notes) "composed" k = true :=
    noted_iff.mpr ⟨u, List.contains_iff_mem.mp (contains_of_mem (pre ++ .inr (EmailEvent.composed a t k u s m) :: mid)
      (outbound.evStream x) (.composed a t k u s m) ("composed", k, u) (by simp) (by simp [hs]) (by simp [notes]))⟩
  cases x <;> simp_all [incoming, item]

/-! ## A decision is final -/

/-- Whether an email event decides its email: a send or a discard. -/
def decides : EmailEvent → Bool
  | .sent .. | .discarded .. => true
  | _ => false

/-- A decision's note says its email is decided. -/
theorem decided_of_decides {d : EmailEvent} (hd : decides d = true) {w1 w2 : List Note} :
    decided (w1 ++ notes d ++ w2) (item d) = true := by
  cases d <;> simp_all [decides, decided, item, noted, notes]

/-- **An email is decided once**: before every `email.send` or `email.discard` of `k`, `k` was not decided. -/
theorem an_email_is_decided_once {pre post : outbound.XLog} {d : EmailEvent} (hd : decides d = true)
    (h : ValidX (pre ++ .inr d :: post)) : decided ((evs pre (outbound.evStream d)).flatMap notes) (item d) = false := by
  have := h.holdsNamed "email_is_decided_once"
  dsimp only at this
  cases d <;> simp_all [decides, item]

/-- No email event about an email is accepted once the stream's notes say the email exists and is decided: not a
creation (`email_id_must_be_new`), not a solicitation, draft or compose (`email_must_be_undecided`), and not another
decision (`email_is_decided_once`). -/
theorem no_event_once_decided {pre post : outbound.XLog} {x : EmailEvent}
    (h : ValidX (pre ++ .inr x :: post))
    (hex : noted ((evs pre (outbound.evStream x)).flatMap notes) "email" (item x) = true)
    (hdec : decided ((evs pre (outbound.evStream x)).flatMap notes) (item x) = true) : False := by
  cases x with
  | created a t k r m =>
    have := h.holdsNamed "email_id_must_be_new"
    dsimp only at this
    simp_all [item]
  | sent a t k u m =>
    have := h.holdsNamed "email_is_decided_once"
    dsimp only at this
    simp_all [item]
  | discarded a t k m =>
    have := h.holdsNamed "email_is_decided_once"
    dsimp only at this
    simp_all [item]
  | _ =>
    have := h.holdsNamed "email_must_be_undecided"
    dsimp only at this
    simp_all [item]

/-- A decision was accepted: its email existed, as the notes before it say. -/
theorem decision_admitted {pre post : outbound.XLog} {d : EmailEvent} (hd : decides d = true)
    (h : ValidX (pre ++ .inr d :: post)) :
    noted ((evs pre (outbound.evStream d)).flatMap notes) "email" (item d) = true := by
  have h3 := h.holdsNamed "email_must_exist"
  dsimp only at h3
  simp only [read_notes] at h3
  cases d <;> simp only [decides, Bool.false_eq_true] at hd <;> simpa [item] using h3

/-- **Nothing follows a decision**: after an email is sent or discarded, no email event about it is accepted on the
stream (`no_event_once_decided`). -/
theorem nothing_follows_a_decision {pre mid post : outbound.XLog} {d x : EmailEvent} (hd : decides d = true)
    (h : ValidX (pre ++ .inr d :: mid ++ .inr x :: post))
    (hs : outbound.evStream x = outbound.evStream d) (hk : item x = item d) : False := by
  -- `::` binds tighter than `++`: `h` is on `(pre ++ .inr d :: mid) ++ .inr x :: post`
  have hd' : ValidX (pre ++ .inr d :: (mid ++ .inr x :: post)) := by simpa [List.append_assoc] using h
  have hw : (evs (pre ++ .inr d :: mid) (outbound.evStream x)).flatMap notes =
      (evs pre (outbound.evStream d)).flatMap notes ++ notes d ++ (evs mid (outbound.evStream d)).flatMap notes := by
    rw [hs]; simp [evs_append, evs_cons_inr, List.flatMap_append, List.flatMap_cons, List.append_assoc]
  have hex := decision_admitted hd hd'
  refine no_event_once_decided h ?_ ?_ <;> rw [hw, hk]
  · simp only [noted, List.any_append, Bool.or_eq_true]; exact Or.inl (Or.inl (by simpa [noted] using hex))
  · exact decided_of_decides hd

/-! ## The creator can always send -/

/-- **The creator can always send**: a theorem of acceptance, not of valid logs. After any valid log in which stream
`t` is open and not closed with opener `a`, email `k` is created on it and not decided, and the `.eml` `u` is not yet
named on `k`, the service accepts `a`'s `email.send` of `k` at `u`, whatever else has or has not happened: no draft, no
composed draft, nothing from anyone else, and no earlier event of `a`'s own beyond the creation. These six hypotheses
are everything the send's rules read (`email_must_exist`, `eml_urls_must_be_unique`, `only_opener_can_decide`,
`email_is_decided_once`) together with the core's admission (`stream_must_exist`, `stream_must_be_open`); the request's
fresh list is empty, as every layer request's is. The host refuses a malformed URL before the engine sees it, so `u` is
taken as a well-formed `.eml` URL. -/
theorem the_creator_can_always_send {pre : outbound.XLog} (h : ValidX pre) {a t k : Id} {u : String} {m : Meta}
    (hopen : Past.opened (cores pre) t = true) (hclosed : Past.closed (cores pre) t = false)
    (hopener : Past.opener (cores pre) t = some a)
    (hk : noted ((evs pre t).flatMap notes) "email" k = true)
    (hu : emlNamed ((evs pre t).flatMap notes) k u = false)
    (hdec : decided ((evs pre t).flatMap notes) k = false) :
    outbound.service.respond pre (.inr (a, .send t k u m, [])) = .accepted (.inr (.sent a t k u m)) := by
  refine Service.respond_accepted_iff.mpr ⟨rfl, ?_⟩
  have hv : ValidX (pre ++ [.inr (.sent a t k u m)]) := by
    refine (ValidX.snoc_inr_iff h).mpr ⟨?_, ?_, ?_, ?_⟩
    · show (Past.view (cores pre) t).admits a = none
      exact View.admits_none.mpr ⟨by simpa using hopen, by simpa using hclosed⟩
    · rfl
    · intro r hr
      simp only [outbound, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        <;> simp [hopener, hk, hu, hdec, Past.view]
    · intro r hr
      simp at hr
  exact (Service.Valid.inv hv).2

/-! ## The core's guarantees, here -/

/-- **Only the opener closes the stream** of emails (`Layer.ValidX.close_by_opener`). -/
theorem only_the_opener_closes_the_stream {pre post : outbound.XLog} {a t : Id} {m : Meta}
    (h : ValidX (pre ++ .inl (Event.streamClosed a t m) :: post)) : Past.opener (cores pre) t = some a :=
  h.close_by_opener

/-- **Nothing follows a close**: nothing, of the core or of the layer, is appended to a stream after its close
(`Layer.ValidX.close_final`). -/
theorem nothing_follows_a_close {pre mid post : outbound.XLog} {a t : Id} {m : Meta} {x : outbound.XEv}
    (h : ValidX (pre ++ .inl (Event.streamClosed a t m) :: mid ++ x :: post)) : streamX x ≠ t := h.close_final

end Email
