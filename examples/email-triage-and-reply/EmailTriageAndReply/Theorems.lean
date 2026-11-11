-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import EmailTriageAndReply.Layer

/-!
# The email triage and reply layer's guarantees

Each holds of every valid log of the layer (`ValidX`). Each follows from the rules that held when its events were
accepted, from the core's opener (`v.opener`), and from the core's theorems through `h.cores`. Each is named as the
sentence it proves.

The owner of every email and every triage is the stream's opener. Creating and requesting need the opener's
authority, so a delegate creates for the opener, not for itself.

`EmailTriageAndReply.Principals` holds the declarations and the delegations. A principal is declared once, as a person
or as an agent, and never the opener (`a_principal_is_declared_once`, `no_person_is_an_agent`,
`the_opener_is_never_declared`). Only persons delegate (`every_delegator_is_a_person`), and only declared principals
are delegates (`every_delegate_is_declared`). A delegation adds exactly its pair and lasts for the stream's life (`a_delegation_adds_exactly_its_pair`,
`a_delegation_is_permanent`). Each delegate has one delegator (`each_delegate_has_one_delegator`).

`EmailTriageAndReply.Authority` holds what a delegate may do. A delegate of the owner acts with the owner's authority
(`a_delegate_acts_for_its_delegator`), except that an agent makes no terminal decision
(`an_agent_delegate_has_no_terminal_authority`, `a_person_delegate_has_terminal_authority`). Every act is by the
owner or a delegate of the owner (`every_act_is_by_the_owner_or_a_delegate`), and every terminal decision by
the owner or a person delegate (`every_terminal_decision_is_by_the_owner_or_a_person_delegate`). No agent
makes a terminal decision (`no_agent_makes_a_terminal_decision`). A delegate's authority rests on the owner's own
delegation, never on a chain (`no_act_rests_on_a_chain`). Every solicited preparer and every asked adviser was
declared first (`Email.every_solicited_preparer_was_declared`, `Triage.every_asked_adviser_was_declared`).

`EmailTriageAndReply.Email` and `EmailTriageAndReply.Triage` hold the items' theorems. A preparer never drafts its own
email, and an adviser never considers its own triage. Soliciting, preparing, asking and advising go on after a draft
or a consideration until the decision. A deferral closes a triage as the other decisions do. The reply rule's
theorems are in `EmailTriageAndReply.Reply`.

A rule is found by its name (`ValidX.holdsNamed`). The name `only_owner_or_person_delegates_can_decide` occurs twice:
once for the email decisions and once for the triage decisions. For the triage's, the search starts after the
twenty-three principal and email rules (`holdsNamedFrom`).
-/

namespace EmailTriageAndReply
open Provenstream Provenstream.Layer

/-! ## What the memory reads: the notes of the stream's events -/

theorem foldl_addNotes (past : List MailEvent) (st : List Note) : past.foldl addNotes st = st ++ past.flatMap notes := by
  induction past generalizing st with
  | nil => simp
  | cons e es ih => simp [ih, addNotes, List.append_assoc]

/-- What the layer's rules read of the stream's events is their notes, in order. -/
@[simp] theorem read_notes (past : List MailEvent) : past.foldl addNotes [] = past.flatMap notes := by
  simp [foldl_addNotes]

/-- A note of the stream's events is a note of an event of that stream in the log. -/
theorem mem_notes_evs {log : mailbox.XLog} {t : Id} {n : Note} (h : n ∈ (evs log t).flatMap notes) :
    ∃ e, .inr e ∈ log ∧ mailbox.evStream e = t ∧ n ∈ notes e := by
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

/-- A note of an event of stream `t` in the log is among the notes the memory reads after it. -/
theorem contains_of_mem (pre : mailbox.XLog) (t : Id) (e : MailEvent) (n : Note)
    (hm : (.inr e : mailbox.XEv) ∈ pre) (hs : mailbox.evStream e = t) (hn : n ∈ notes e) :
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

/-- **The rule named `n` among the rules after the first `i` held** for a layer event of a valid log. The triage
rules start at 23, after the principals' seven and the email's sixteen. -/
theorem holdsNamedFrom {pre post : mailbox.XLog} {x : MailEvent} (h : ValidX (pre ++ .inr x :: post)) (n : String)
    (i : Nat) {r : Layer.Rule coreBase.View mailbox.memory.V MailEvent}
    (hr : (mailbox.rules.drop i).find? (·.reason == n) = some r := by rfl) :
    r.holds (coreBase.view (bases pre) (mailbox.evStream x)) (mailbox.memory.read (evs pre (mailbox.evStream x))) x
      = true :=
  h.holds (List.mem_of_mem_drop (List.mem_of_find?_eq_some hr))

/-- A note of an email's replied-to message: the email is a reply, and the note names the message. -/
@[simp] theorem mem_replyNotes {k : String} {r : Option String} {n : Note} :
    n ∈ replyNotes k r ↔ ∃ v, r = some v ∧ n = ("reply_to", k, v) := by
  cases r <;> simp [replyNotes]

/-- The opener of a prefix is the opener of the whole log. -/
theorem opener_of_prefix {pre post : mailbox.XLog} {t a : Id} (h : Past.opener (cores pre) t = some a) :
    Past.opener (cores (pre ++ post)) t = some a := by
  simpa [cores] using opener_stays h (cores post)

/-! # Principals: declarations and delegations -/

namespace Principals

theorem delegate_note {e : MailEvent} {o d : String} (h : ("delegate", o, d) ∈ notes e) :
    ∃ t m, e = .principal (.delegated o t d m) := by
  rcases e with e | e | e <;> cases e <;> simp_all [notes, principalNotes, emailNotes, triageNotes]

theorem invited_note {e : MailEvent} {p q : String} (h : ("invited", p, q) ∈ notes e) :
    ∃ a t m, e = .principal (.invited a t p m) := by
  rcases e with e | e | e <;> cases e <;> simp_all [notes, principalNotes, emailNotes, triageNotes]

theorem summoned_note {e : MailEvent} {p q : String} (h : ("summoned", p, q) ∈ notes e) :
    ∃ a t m, e = .principal (.summoned a t p m) := by
  rcases e with e | e | e <;> cases e <;> simp_all [notes, principalNotes, emailNotes, triageNotes]

/-- The notes of a stream call `p` invited only after an `principal.invite` of `p` on it. -/
theorem invited_of_noted {pre : mailbox.XLog} {t p : Id} (h : noted ((evs pre t).flatMap notes) "invited" p = true) :
    ∃ a m, (.inr (MailEvent.principal (.invited a t p m)) : mailbox.XEv) ∈ pre := by
  obtain ⟨q, hq⟩ := noted_iff.mp h
  obtain ⟨e, hm, hs, hn⟩ := mem_notes_evs hq
  obtain ⟨a, t', m, rfl⟩ := invited_note hn
  simp only [Commands.evStream_mk] at hs
  subst hs
  exact ⟨a, m, hm⟩

/-- The notes of a stream call `p` summoned only after a `principal.summon` of `p` on it. -/
theorem summoned_of_noted {pre : mailbox.XLog} {t p : Id}
    (h : noted ((evs pre t).flatMap notes) "summoned" p = true) :
    ∃ a m, (.inr (MailEvent.principal (.summoned a t p m)) : mailbox.XEv) ∈ pre := by
  obtain ⟨q, hq⟩ := noted_iff.mp h
  obtain ⟨e, hm, hs, hn⟩ := mem_notes_evs hq
  obtain ⟨a, t', m, rfl⟩ := summoned_note hn
  simp only [Commands.evStream_mk] at hs
  subst hs
  exact ⟨a, m, hm⟩

/-! ## A principal is declared once, as a person or an agent, and never the opener -/

/-- The principal a principal event declares: an invited person or a summoned agent. -/
def declares : PrincipalEvent → Option Id
  | .invited _ _ p _ | .summoned _ _ p _ => some p
  | _ => none

theorem declaration_noted {x : PrincipalEvent} {p : Id} (hx : declares x = some p) :
    ∃ what, (what = "invited" ∨ what = "summoned") ∧ (what, p, "") ∈ notes (.principal x) := by
  cases x <;> simp_all [declares, notes, principalNotes]

/-- **A principal is declared once**: no valid log declares one principal twice on a stream, as a person or an agent,
in any combination. -/
theorem a_principal_is_declared_once {l1 l2 l3 : mailbox.XLog} {x y : PrincipalEvent} {p : Id}
    (h : ValidX (l1 ++ .inr (.principal x) :: l2 ++ .inr (.principal y) :: l3))
    (hs : mailbox.evStream (.principal y) = mailbox.evStream (.principal x))
    (hx : declares x = some p) (hy : declares y = some p) : False := by
  have hnew := h.holdsNamed "principal_must_be_new"
  dsimp only at hnew
  obtain ⟨what, hw, hn⟩ := declaration_noted hx
  have hc := contains_of_mem (l1 ++ .inr (.principal x) :: l2) (mailbox.evStream (.principal y)) (.principal x)
    (what, p, "") (by simp) hs.symm hn
  have hnoted : noted ((evs (l1 ++ .inr (.principal x) :: l2) (mailbox.evStream (.principal y))).flatMap notes) what p
      = true := noted_iff.mpr ⟨"", List.contains_iff_mem.mp hc⟩
  cases y <;> simp [declares] at hy <;> subst hy <;> simp only [read_notes, isNew] at hnew <;>
    simp only [Commands.evStream_mk] at hnoted <;> rcases hw with rfl | rfl <;> simp_all

/-- **No person is an agent**: no valid log invites and summons one principal on a stream. -/
theorem no_person_is_an_agent {log : mailbox.XLog} (h : ValidX log) {a a' t p : Id} {m m' : Meta}
    (hi : (.inr (MailEvent.principal (.invited a t p m)) : mailbox.XEv) ∈ log)
    (hs : (.inr (MailEvent.principal (.summoned a' t p m')) : mailbox.XEv) ∈ log) : False := by
  rcases mem_mem_split hi hs (by simp) with ⟨l1, l2, l3, rfl⟩ | ⟨l1, l2, l3, rfl⟩
  · exact a_principal_is_declared_once h rfl (x := .invited a t p m) (y := .summoned a' t p m') rfl rfl
  · exact a_principal_is_declared_once h rfl (x := .summoned a' t p m') (y := .invited a t p m) rfl rfl

/-- **The opener is never declared**: every invite and summon names a principal other than the stream's opener. -/
theorem the_opener_is_never_declared {pre post : mailbox.XLog} {x : PrincipalEvent} {p : Id}
    (h : ValidX (pre ++ .inr (.principal x) :: post)) (hx : declares x = some p) :
    Past.opener (cores pre) (mailbox.evStream (.principal x)) ≠ some p := by
  have hnew := h.holdsNamed "principal_must_be_new"
  dsimp only at hnew
  cases x <;> simp [declares] at hx <;> subst hx <;> simp_all [isNew]

/-- **Only the opener or a delegate of the opener declares**: every invite and summon is by the opener or a delegate
of the opener. -/
theorem every_declaration_is_by_the_opener_or_a_delegate {pre post : mailbox.XLog} {x : PrincipalEvent} {p : Id}
    (h : ValidX (pre ++ .inr (.principal x) :: post)) (hx : declares x = some p) :
    ∃ a, forOwner (Past.opener (cores pre) (mailbox.evStream (.principal x)))
      ((evs pre (mailbox.evStream (.principal x))).flatMap notes) a = true := by
  cases x with
  | invited a t p' m =>
    have := h.holdsNamed "only_opener_or_delegates_can_invite"
    dsimp only at this
    exact ⟨a, by simpa using this⟩
  | summoned a t p' m =>
    have := h.holdsNamed "only_opener_or_delegates_can_summon"
    dsimp only at this
    exact ⟨a, by simpa using this⟩
  | _ => simp [declares] at hx

/-- At every declaration the stream has an opener. -/
theorem opener_at_declaration {pre post : mailbox.XLog} {x : PrincipalEvent} {p : Id}
    (h : ValidX (pre ++ .inr (.principal x) :: post)) (hx : declares x = some p) :
    ∃ o, Past.opener (cores pre) (mailbox.evStream (.principal x)) = some o := by
  obtain ⟨a, ha⟩ := every_declaration_is_by_the_opener_or_a_delegate h hx
  cases ho : Past.opener (cores pre) (mailbox.evStream (.principal x)) with
  | some o => exact ⟨o, rfl⟩
  | none => rw [ho] at ha; simp [forOwner] at ha

/-- A declared principal is never the opener of the whole log. -/
theorem a_declared_principal_is_not_the_opener {log : mailbox.XLog} (h : ValidX log) {x : PrincipalEvent} {p t : Id}
    (hm : (.inr (MailEvent.principal x) : mailbox.XEv) ∈ log) (hs : mailbox.evStream (.principal x) = t)
    (hx : declares x = some p) : Past.opener (cores log) t ≠ some p := by
  obtain ⟨q1, q2, rfl⟩ := List.append_of_mem hm
  obtain ⟨o, ho⟩ := opener_at_declaration h hx
  have hne := the_opener_is_never_declared h hx
  subst hs
  rw [opener_of_prefix (post := .inr (.principal x) :: q2) ho]
  rw [ho] at hne
  exact hne

/-! ## Delegations: by persons, of declared principals, one delegator each -/

/-- **A delegate was delegated by its delegator**: the notes of a stream call `d` a delegate of `o` only after `o`
itself delegated `d` on the stream. -/
theorem delegated_of_delegate {pre : mailbox.XLog} {t o d : Id}
    (h : isDelegateOf ((evs pre t).flatMap notes) o d = true) :
    ∃ m, (.inr (MailEvent.principal (.delegated o t d m)) : mailbox.XEv) ∈ pre := by
  obtain ⟨e, hm, hs, hn⟩ := mem_notes_evs (List.contains_iff_mem.mp h)
  obtain ⟨t', m, rfl⟩ := delegate_note hn
  simp only [Commands.evStream_mk] at hs
  subst hs
  exact ⟨m, hm⟩

/-- A principal with no delegator is a delegate of nobody. -/
theorem not_delegate_of_no_delegator {w : List Note} {o d : String} (h : hasDelegator w d = false) :
    isDelegateOf w o d = false := by
  cases hd : isDelegateOf w o d with
  | false => rfl
  | true =>
    have : hasDelegator w d = true := by
      simp only [hasDelegator, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
      exact ⟨("delegate", o, d), List.contains_iff_mem.mp hd, rfl, rfl⟩
    rw [h] at this; exact absurd this (by simp)

/-- **A delegation adds exactly its pair**: after `a` delegates `d`, `d` is a delegate of `a`, and every other pair is
as it was. A delegation widens only what `a`'s delegate may do for `a`. -/
theorem a_delegation_adds_exactly_its_pair (w : List Note) (a t d : Id) (m : Meta) (o' d' : String) :
    isDelegateOf (w ++ notes (.principal (.delegated a t d m))) o' d' =
      ((a == o' && d == d') || isDelegateOf w o' d') := by
  simp only [isDelegateOf, notes, principalNotes, List.contains_append]
  by_cases h1 : a = o'
  · subst h1
    by_cases h2 : d = d'
    · subst h2; simp
    · have h2' : d' ≠ d := fun e => h2 e.symm
      simp [h2, h2']
  · have h1' : o' ≠ a := fun e => h1 e.symm
    simp [h1, h1']

/-- **A delegation is permanent**: once a delegate of `o`, a delegate of `o` in every extension of the notes. -/
theorem a_delegation_is_permanent {w1 w2 : List Note} {o d : String} (h : isDelegateOf w1 o d = true) :
    isDelegateOf (w1 ++ w2) o d = true := by
  simp only [isDelegateOf, List.contains_append, Bool.or_eq_true] at h ⊢
  exact Or.inl h

/-- **Every other event leaves every pair as it was**: only delegations change who delegates whom. -/
theorem other_events_keep_every_pair (w : List Note) (x : MailEvent)
    (hx : match x with | .principal (.delegated ..) => False | _ => True)
    (o d : String) : isDelegateOf (w ++ notes x) o d = isDelegateOf w o d := by
  simp only [isDelegateOf, List.contains_append]
  have : (notes x).contains ("delegate", o, d) = false := by
    rcases x with e | e | e <;> cases e <;> simp_all [notes, principalNotes, emailNotes, triageNotes, replyNotes] <;>
      (try split) <;> simp
  rw [this, Bool.or_false]

/-- **No principal delegates itself.** -/
theorem no_principal_delegates_itself {pre post : mailbox.XLog} {a t d : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.principal (.delegated a t d m)) :: post)) : a ≠ d := by
  have := h.holdsNamed "delegate_must_not_be_the_delegator"
  dsimp only at this
  simpa using this

/-- A delegation in a valid log is of a principal other than its delegator. -/
theorem delegate_is_not_its_delegator {log : mailbox.XLog} (h : ValidX log) {a t d : Id} {m : Meta}
    (hm : (.inr (MailEvent.principal (.delegated a t d m)) : mailbox.XEv) ∈ log) : a ≠ d := by
  obtain ⟨p1, p2, rfl⟩ := List.append_of_mem hm
  exact no_principal_delegates_itself h

/-- **Every delegator is a person**: the opener or an invited principal. An agent never delegates. -/
theorem every_delegator_is_a_person {pre post : mailbox.XLog} {a t d : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.principal (.delegated a t d m)) :: post)) :
    Past.opener (cores pre) t = some a ∨ ∃ o m', (.inr (MailEvent.principal (.invited o t a m')) : mailbox.XEv) ∈ pre := by
  have := h.holdsNamed "only_persons_can_delegate"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk, isPerson, Bool.or_eq_true, beq_iff_eq] at this
  rcases this with h1 | h1
  · exact Or.inl (by simpa using h1)
  · exact Or.inr (invited_of_noted h1)

/-- **Every delegate is declared**: invited or summoned earlier on the stream. -/
theorem every_delegate_is_declared {pre post : mailbox.XLog} {a t d : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.principal (.delegated a t d m)) :: post)) :
    (∃ o m', (.inr (MailEvent.principal (.invited o t d m')) : mailbox.XEv) ∈ pre) ∨
      ∃ o m', (.inr (MailEvent.principal (.summoned o t d m')) : mailbox.XEv) ∈ pre := by
  have := h.holdsNamed "delegate_must_be_declared"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk, Bool.or_eq_true] at this
  rcases this with h1 | h1
  · exact Or.inl (invited_of_noted h1)
  · exact Or.inr (summoned_of_noted h1)

/-- A delegate in a valid log is never the opener. -/
theorem no_delegate_is_the_opener {log : mailbox.XLog} (h : ValidX log) {a t d : Id} {m : Meta}
    (hm : (.inr (MailEvent.principal (.delegated a t d m)) : mailbox.XEv) ∈ log) : Past.opener (cores log) t ≠ some d := by
  obtain ⟨p1, p2, rfl⟩ := List.append_of_mem hm
  have hl : ∀ x, x ∈ p1 → x ∈ p1 ++ .inr (MailEvent.principal (.delegated a t d m)) :: p2 :=
    fun x hx => List.mem_append_left _ hx
  rcases every_delegate_is_declared h with ⟨o, m', hi⟩ | ⟨o, m', hi⟩
  · exact a_declared_principal_is_not_the_opener h (hl _ hi) rfl (x := .invited o t d m') rfl
  · exact a_declared_principal_is_not_the_opener h (hl _ hi) rfl (x := .summoned o t d m') rfl

/-- **A delegate is new**: before every `principal.delegate` of `d`, `d` was nobody's delegate. -/
theorem every_delegate_is_new {pre post : mailbox.XLog} {a t d : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.principal (.delegated a t d m)) :: post)) :
    hasDelegator ((evs pre t).flatMap notes) d = false := by
  have := h.holdsNamed "delegate_must_be_new"
  dsimp only at this
  simpa using this

/-- **Each delegate has one delegator, for the stream's life**: no valid log has two delegations of one principal on a
stream, in either order. So "on whose behalf" a delegate acts is never ambiguous, and no pair is delegated twice. -/
theorem a_principal_is_delegated_once {l1 l2 l3 : mailbox.XLog} {a a' t d : Id} {m m' : Meta}
    (h : ValidX (l1 ++ .inr (.principal (.delegated a t d m)) :: l2 ++
      .inr (.principal (.delegated a' t d m')) :: l3)) : False := by
  have := every_delegate_is_new h
  have hc := contains_of_mem (l1 ++ .inr (.principal (.delegated a t d m)) :: l2) t (.principal (.delegated a t d m))
    ("delegate", a, d) (by simp) (by simp) (by simp [notes, principalNotes])
  have hd : isDelegateOf _ a d = true := hc
  rw [not_delegate_of_no_delegator this] at hd
  exact absurd hd (by simp)

/-- **Each delegate has one delegator**: two delegations of one principal on a stream of a valid log are by the same
delegator. -/
theorem each_delegate_has_one_delegator {log : mailbox.XLog} (h : ValidX log) {o1 o2 t d : Id} {m1 m2 : Meta}
    (h1 : (.inr (MailEvent.principal (.delegated o1 t d m1)) : mailbox.XEv) ∈ log)
    (h2 : (.inr (MailEvent.principal (.delegated o2 t d m2)) : mailbox.XEv) ∈ log) : o1 = o2 := by
  by_cases hne : (.inr (MailEvent.principal (.delegated o1 t d m1)) : mailbox.XEv) =
      .inr (MailEvent.principal (.delegated o2 t d m2))
  · simp only [XE.inr.injEq, MailEvent.principal.injEq, PrincipalEvent.delegated.injEq] at hne
    exact hne.1
  · rcases mem_mem_split h1 h2 hne with ⟨l1, l2, l3, rfl⟩ | ⟨l1, l2, l3, rfl⟩
    · exact (a_principal_is_delegated_once h).elim
    · exact (a_principal_is_delegated_once h).elim

end Principals

/-! # Authority: the owner's, or a delegate's for the owner -/

namespace Authority

theorem forOwner_true {o : Option Id} {w : List Note} {a : Id} :
    forOwner o w a = true ↔ o = some a ∨ ∃ o', o = some o' ∧ isDelegateOf w o' a = true := by
  cases o <;> simp [forOwner]

theorem personForOwner_true {o : Option Id} {w : List Note} {a : Id} :
    personForOwner o w a = true ↔
      o = some a ∨ ∃ o', o = some o' ∧ isDelegateOf w o' a = true ∧ noted w "invited" a = true := by
  cases o <;> simp [personForOwner]

/-- **A delegate acts for its delegator**: a delegate of `o` has `o`'s authority over `o`'s items. -/
theorem a_delegate_acts_for_its_delegator {w : List Note} {o d : Id} (h : isDelegateOf w o d = true) :
    forOwner (some o) w d = true := forOwner_true.mpr (Or.inr ⟨o, rfl, h⟩)

/-- **A person delegate has terminal authority**: a delegate of `o` who is a person makes `o`'s terminal
decisions. -/
theorem a_person_delegate_has_terminal_authority {w : List Note} {o d : Id} (h : isDelegateOf w o d = true)
    (hp : noted w "invited" d = true) : personForOwner (some o) w d = true :=
  personForOwner_true.mpr (Or.inr ⟨o, rfl, h, hp⟩)

/-- **An agent delegate has no terminal authority**: a principal that is neither the owner nor invited makes no
terminal decision for the owner, whoever delegated it. -/
theorem an_agent_delegate_has_no_terminal_authority {w : List Note} {o d : Id} (hne : o ≠ d)
    (hp : noted w "invited" d = false) : personForOwner (some o) w d = false := by
  cases hc : personForOwner (some o) w d with
  | false => rfl
  | true =>
    rcases personForOwner_true.mp hc with h1 | ⟨o', h1, -, h3⟩
    · exact absurd (Option.some.inj h1) hne
    · rw [hp] at h3; exact absurd h3 (by simp)

/-- **Terminal authority is authority**: whoever may make a terminal decision for the owner has the owner's
authority. -/
theorem forOwner_of_personForOwner {o : Option Id} {w : List Note} {a : Id} (h : personForOwner o w a = true) :
    forOwner o w a = true := by
  rcases personForOwner_true.mp h with h1 | ⟨o', h1, h2, -⟩
  · exact forOwner_true.mpr (Or.inl h1)
  · exact forOwner_true.mpr (Or.inr ⟨o', h1, h2⟩)

/-- The principal an act on an item is by, for every command that needs the owner's authority. -/
def actor : MailEvent → Option Id
  | .principal (.invited a ..) | .principal (.summoned a ..)
  | .email (.created a ..) | .email (.solicited a ..) | .email (.drafted a ..) | .email (.sent a ..)
  | .email (.discarded a ..) | .triage (.requested a ..) | .triage (.asked a ..) | .triage (.considered a ..)
  | .triage (.replied a ..) | .triage (.worked a ..) | .triage (.ignored a ..) | .triage (.deferred a ..) => some a
  | _ => none

/-- The principal a terminal decision is by: a send, a discard, a reply, a work item, an ignore or a deferral. -/
def terminal : MailEvent → Option Id
  | .email (.sent a ..) | .email (.discarded a ..) | .triage (.replied a ..) | .triage (.worked a ..)
  | .triage (.ignored a ..) | .triage (.deferred a ..) => some a
  | _ => none

/-- **Every terminal decision is by the owner or a person delegate of the owner.** -/
theorem every_terminal_decision_is_by_the_owner_or_a_person_delegate {pre post : mailbox.XLog} {x : MailEvent}
    {a : Id} (h : ValidX (pre ++ .inr x :: post)) (hx : terminal x = some a) :
    personForOwner (Past.opener (cores pre) (mailbox.evStream x)) ((evs pre (mailbox.evStream x)).flatMap notes) a
      = true := by
  rcases x with e | e | e
  · cases e <;> simp [terminal] at hx
  · cases e with
    | sent a' t k u m =>
      simp only [terminal, Option.some.injEq] at hx; subst hx
      have := h.holdsNamed "only_owner_or_person_delegates_can_decide"
      dsimp only at this; simpa using this
    | discarded a' t k m =>
      simp only [terminal, Option.some.injEq] at hx; subst hx
      have := h.holdsNamed "only_owner_or_person_delegates_can_decide"
      dsimp only at this; simpa using this
    | _ => simp [terminal] at hx
  · have := holdsNamedFrom h "only_owner_or_person_delegates_can_decide" 23
    dsimp only at this
    cases e <;> simp only [terminal, Option.some.injEq, reduceCtorEq] at hx <;> subst hx <;> simpa using this

/-- **Every act is by the owner or a delegate of the owner**: every create, request, solicit, ask, draft and
consider, and every terminal decision. -/
theorem every_act_is_by_the_owner_or_a_delegate {pre post : mailbox.XLog} {x : MailEvent} {a : Id}
    (h : ValidX (pre ++ .inr x :: post)) (hx : actor x = some a) :
    forOwner (Past.opener (cores pre) (mailbox.evStream x)) ((evs pre (mailbox.evStream x)).flatMap notes) a = true := by
  rcases x with e | e | e
  · cases e with
    | invited a' t p m =>
      simp only [actor, Option.some.injEq] at hx; subst hx
      have := h.holdsNamed "only_opener_or_delegates_can_invite"
      dsimp only at this; simpa using this
    | summoned a' t p m =>
      simp only [actor, Option.some.injEq] at hx; subst hx
      have := h.holdsNamed "only_opener_or_delegates_can_summon"
      dsimp only at this; simpa using this
    | delegated => simp [actor] at hx
  · cases e with
    | created a' t k r m =>
      simp only [actor, Option.some.injEq] at hx; subst hx
      have := h.holdsNamed "only_opener_or_delegates_can_create"
      dsimp only at this; simpa using this
    | solicited a' t k p m =>
      simp only [actor, Option.some.injEq] at hx; subst hx
      have := h.holdsNamed "only_owner_or_delegates_can_solicit"
      dsimp only at this; simpa using this
    | drafted a' t k u s m =>
      simp only [actor, Option.some.injEq] at hx; subst hx
      have := h.holdsNamed "only_owner_or_delegates_can_draft"
      dsimp only at this; simpa using this
    | sent a' t k u m =>
      simp only [actor, Option.some.injEq] at hx; subst hx
      exact forOwner_of_personForOwner
        (every_terminal_decision_is_by_the_owner_or_a_person_delegate h (x := .email (.sent a' t k u m)) rfl)
    | discarded a' t k m =>
      simp only [actor, Option.some.injEq] at hx; subst hx
      exact forOwner_of_personForOwner
        (every_terminal_decision_is_by_the_owner_or_a_person_delegate h (x := .email (.discarded a' t k m)) rfl)
    | prepared => simp [actor] at hx
  · cases e with
    | requested a' t k u m =>
      simp only [actor, Option.some.injEq] at hx; subst hx
      have := h.holdsNamed "only_opener_or_delegates_can_request"
      dsimp only at this; simpa using this
    | asked a' t k d m =>
      simp only [actor, Option.some.injEq] at hx; subst hx
      have := h.holdsNamed "only_owner_or_delegates_can_ask"
      dsimp only at this; simpa using this
    | considered a' t k v m =>
      simp only [actor, Option.some.injEq] at hx; subst hx
      have := h.holdsNamed "only_owner_or_delegates_can_consider"
      dsimp only at this; simpa using this
    | advised => simp [actor] at hx
    | _ =>
      exact forOwner_of_personForOwner (every_terminal_decision_is_by_the_owner_or_a_person_delegate h
        (by simpa [actor, terminal] using hx))

/-- **No act rests on a chain**: a principal acting on an item other than its owner was delegated by the owner
itself, earlier on the stream, and is the owner's delegate. -/
theorem no_act_rests_on_a_chain {pre post : mailbox.XLog} {x : MailEvent} {a o : Id}
    (h : ValidX (pre ++ .inr x :: post)) (hx : actor x = some a)
    (ho : Past.opener (cores pre) (mailbox.evStream x) = some o) (hne : o ≠ a) :
    isDelegateOf ((evs pre (mailbox.evStream x)).flatMap notes) o a = true ∧
      ∃ m, (.inr (MailEvent.principal (.delegated o (mailbox.evStream x) a m)) : mailbox.XEv) ∈ pre := by
  have hf := every_act_is_by_the_owner_or_a_delegate h hx
  rw [ho] at hf
  rcases forOwner_true.mp hf with h1 | ⟨o', h1, h2⟩
  · exact absurd (Option.some.inj h1) hne
  · obtain rfl := Option.some.inj h1
    exact ⟨h2, Principals.delegated_of_delegate h2⟩

/-- **No agent makes a terminal decision**: no valid log has a principal summoned as an agent on a stream and has it
send, discard, reply, work, ignore or defer there. -/
theorem no_agent_makes_a_terminal_decision {log : mailbox.XLog} (h : ValidX log) {x : MailEvent} {a o : Id} {m : Meta}
    (hx : (.inr x : mailbox.XEv) ∈ log) (hterm : terminal x = some a)
    (hs : (.inr (MailEvent.principal (.summoned o (mailbox.evStream x) a m)) : mailbox.XEv) ∈ log) : False := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hx
  have hp := every_terminal_decision_is_by_the_owner_or_a_person_delegate h hterm
  rcases personForOwner_true.mp hp with h1 | ⟨o', -, -, h3⟩
  · -- the owner itself: the opener, who is never declared
    exact Principals.a_declared_principal_is_not_the_opener h hs rfl (x := .summoned o (mailbox.evStream x) a m) rfl
      (opener_of_prefix h1)
  · -- an invited person: never also summoned
    obtain ⟨i, mi, hi⟩ := Principals.invited_of_noted h3
    exact Principals.no_person_is_an_agent h (List.mem_append_left _ hi) hs

end Authority

/-! # The email's guarantees -/

namespace Email

theorem email_note {e : MailEvent} {k q : String} (h : ("email", k, q) ∈ notes e) :
    ∃ t r m, e = .email (.created q t k r m) := by
  rcases e with e | e | e <;> cases e <;> simp_all [notes, principalNotes, emailNotes, triageNotes]

theorem preparer_note {e : MailEvent} {k q : String} (h : ("preparer", k, q) ∈ notes e) :
    ∃ a t m, e = .email (.solicited a t k q m) := by
  rcases e with e | e | e <;> cases e <;> simp_all [notes, principalNotes, emailNotes, triageNotes]

/-- The email notes of a stream's events say `k` is an email only by an `email.created` of `k`. -/
theorem created_of_note {pre : mailbox.XLog} {t k o : Id} (h : ("email", k, o) ∈ (evs pre t).flatMap notes) :
    ∃ r m, (.inr (MailEvent.email (.created o t k r m)) : mailbox.XEv) ∈ pre := by
  obtain ⟨e, hm, hs, hn⟩ := mem_notes_evs h
  obtain ⟨t', r, m, rfl⟩ := email_note hn
  simp only [Commands.evStream_mk] at hs
  subst hs
  exact ⟨r, m, hm⟩

theorem solicited_of_contains {pre : mailbox.XLog} {t k p : Id}
    (h : ((evs pre t).flatMap notes).contains ("preparer", k, p) = true) :
    ∃ o m', (.inr (MailEvent.email (.solicited o t k p m')) : mailbox.XEv) ∈ pre := by
  obtain ⟨e, hm, hs, hn⟩ := mem_notes_evs (List.contains_iff_mem.mp h)
  obtain ⟨o, t', m', rfl⟩ := preparer_note hn
  simp only [Commands.evStream_mk] at hs
  subst hs
  exact ⟨o, m', hm⟩

/-! ## Who acts on an email -/

/-- **Every email is created by the opener or a delegate of the opener.** -/
theorem every_email_is_created_by_the_owner_or_a_delegate {pre post : mailbox.XLog} {a t k : Id}
    {r : Option String} {m : Meta} (h : ValidX (pre ++ .inr (.email (.created a t k r m)) :: post)) :
    forOwner (Past.opener (cores pre) t) ((evs pre t).flatMap notes) a = true := by
  simpa using Authority.every_act_is_by_the_owner_or_a_delegate h (x := .email (.created a t k r m)) rfl

/-- **Every solicitation is by the owner or a delegate of the owner.** -/
theorem every_solicitation_is_by_the_owner_or_a_delegate {pre post : mailbox.XLog} {a t k p : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.email (.solicited a t k p m)) :: post)) :
    forOwner (Past.opener (cores pre) t) ((evs pre t).flatMap notes) a = true := by
  simpa using Authority.every_act_is_by_the_owner_or_a_delegate h (x := .email (.solicited a t k p m)) rfl

/-- **Every draft is by the owner or a delegate of the owner.** -/
theorem every_draft_is_by_the_owner_or_a_delegate {pre post : mailbox.XLog} {a t k : Id} {u s : String}
    {m : Meta} (h : ValidX (pre ++ .inr (.email (.drafted a t k u s m)) :: post)) :
    forOwner (Past.opener (cores pre) t) ((evs pre t).flatMap notes) a = true := by
  simpa using Authority.every_act_is_by_the_owner_or_a_delegate h (x := .email (.drafted a t k u s m)) rfl

/-- **The send is by the owner or a person delegate of the owner.** -/
theorem the_send_is_by_the_owner_or_a_person_delegate {pre post : mailbox.XLog} {a t k : Id} {u : String}
    {m : Meta} (h : ValidX (pre ++ .inr (.email (.sent a t k u m)) :: post)) :
    personForOwner (Past.opener (cores pre) t) ((evs pre t).flatMap notes) a = true := by
  simpa using Authority.every_terminal_decision_is_by_the_owner_or_a_person_delegate h
    (x := .email (.sent a t k u m)) rfl

/-- **The discard is by the owner or a person delegate of the owner.** -/
theorem the_discard_is_by_the_owner_or_a_person_delegate {pre post : mailbox.XLog} {a t k : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.email (.discarded a t k m)) :: post)) :
    personForOwner (Past.opener (cores pre) t) ((evs pre t).flatMap notes) a = true := by
  simpa using Authority.every_terminal_decision_is_by_the_owner_or_a_person_delegate h
    (x := .email (.discarded a t k m)) rfl

/-- **No preparer solicits itself.** -/
theorem no_preparer_is_its_soliciter {pre post : mailbox.XLog} {a t k p : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.email (.solicited a t k p m)) :: post)) : a ≠ p := by
  have := h.holdsNamed "preparer_must_not_be_the_soliciter"
  dsimp only at this
  simpa using this

/-- **Every solicited preparer was declared**: invited or summoned on the stream before it was solicited. -/
theorem every_solicited_preparer_was_declared {pre post : mailbox.XLog} {a t k p : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.email (.solicited a t k p m)) :: post)) :
    (∃ o m', (.inr (MailEvent.principal (.invited o t p m')) : mailbox.XEv) ∈ pre) ∨
      ∃ o m', (.inr (MailEvent.principal (.summoned o t p m')) : mailbox.XEv) ∈ pre := by
  have := h.holdsNamed "preparer_must_be_declared"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk, Bool.or_eq_true] at this
  rcases this with h1 | h1
  · exact Or.inl (Principals.invited_of_noted h1)
  · exact Or.inr (Principals.summoned_of_noted h1)

/-- **Every preparation is by a solicited preparer.** -/
theorem every_preparation_is_by_a_solicited_preparer {pre post : mailbox.XLog} {p t k : Id} {u : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.email (.prepared p t k u m)) :: post)) :
    ∃ o m', (.inr (MailEvent.email (.solicited o t k p m')) : mailbox.XEv) ∈ pre := by
  have := h.holdsNamed "only_solicited_preparers_can_prepare"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk] at this
  exact solicited_of_contains this

/-! ## The roles are disjoint -/

/-- **No preparer is the owner.** -/
theorem no_preparer_is_the_owner {pre post : mailbox.XLog} {a t k p : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.email (.solicited a t k p m)) :: post)) :
    Past.opener (cores (pre ++ .inr (.email (.solicited a t k p m)) :: post)) t ≠ some p := by
  have h6' := h.holdsNamed "preparer_must_not_be_the_owner"
  dsimp only at h6'
  have h6 : Past.opener (cores pre) t ≠ some p := by simpa using h6'
  have hf := every_solicitation_is_by_the_owner_or_a_delegate h
  rcases Authority.forOwner_true.mp hf with h1 | ⟨o, h1, -⟩ <;> rw [opener_of_prefix h1] <;> rw [h1] at h6 <;>
    exact h6

/-- **No preparer is a drafter**: a preparer never drafts its own email, in either order. -/
theorem no_preparer_is_a_drafter {log : mailbox.XLog} (h : ValidX log) {o t k p : Id} {u' s : String} {m m' : Meta}
    (hb : (.inr (MailEvent.email (.solicited o t k p m)) : mailbox.XEv) ∈ log)
    (hr : (.inr (MailEvent.email (.drafted p t k u' s m')) : mailbox.XEv) ∈ log) : False := by
  rcases mem_mem_split hb hr (by simp) with ⟨l1, l2, l3, rfl⟩ | ⟨l1, l2, l3, rfl⟩
  · have := h.holdsNamed "drafter_must_not_be_a_preparer"
    dsimp only at this
    simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at this
    rw [contains_of_mem _ t (.email (.solicited o t k p m)) ("preparer", k, p) (by simp) (by simp)
      (by simp [notes, emailNotes])] at this
    exact Bool.noConfusion this
  · have := h.holdsNamed "preparer_must_not_be_a_drafter"
    dsimp only at this
    simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at this
    rw [contains_of_mem _ t (.email (.drafted p t k u' s m')) ("drafter", k, p) (by simp) (by simp)
      (by simp [notes, emailNotes])] at this
    exact Bool.noConfusion this

/-- **The roles are disjoint**: a preparer of an email is neither its owner nor ever a drafter of it. -/
theorem roles_are_disjoint {log : mailbox.XLog} (h : ValidX log) {a t k p : Id} {m : Meta}
    (hb : (.inr (MailEvent.email (.solicited a t k p m)) : mailbox.XEv) ∈ log) :
    Past.opener (cores log) t ≠ some p ∧
      ∀ u' s m', (.inr (MailEvent.email (.drafted p t k u' s m')) : mailbox.XEv) ∉ log := by
  refine ⟨?_, fun u' s m' hr => no_preparer_is_a_drafter h hb hr⟩
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hb
  exact no_preparer_is_the_owner h

/-! ## Each step once, every email created -/

/-- **An email is created once** per stream. -/
theorem an_email_is_created_once {pre post : mailbox.XLog} {a t k : Id} {r : Option String} {m : Meta}
    (h : ValidX (pre ++ .inr (.email (.created a t k r m)) :: post)) :
    noted ((evs pre t).flatMap notes) "email" k = false := by
  have := h.holdsNamed "email_id_must_be_new"
  dsimp only at this
  simpa using this

/-- The email an email event is about. -/
def item : EmailEvent → Id
  | .created _ _ k _ _ | .solicited _ _ k _ _ | .prepared _ _ k _ _ | .drafted _ _ k _ _ _
  | .sent _ _ k _ _ | .discarded _ _ k _ => k

/-- **Every event names a created email.** -/
theorem every_event_names_a_created_email {pre post : mailbox.XLog} {x : EmailEvent} {t : Id}
    (h : ValidX (pre ++ .inr (.email x) :: post)) (hs : mailbox.evStream (.email x) = t)
    (hx : match x with | .created .. => False | _ => True) :
    ∃ a r m, (.inr (MailEvent.email (.created a t (item x) r m)) : mailbox.XEv) ∈ pre := by
  subst hs
  have := h.holdsNamed "email_must_exist"
  dsimp only at this
  simp only [read_notes] at this
  have hn : noted ((evs pre (mailbox.evStream (.email x))).flatMap notes) "email" (item x) = true := by
    cases x <;> simp_all [item]
  obtain ⟨q, hq⟩ := noted_iff.mp hn
  obtain ⟨r, m, hc⟩ := created_of_note hq
  exact ⟨q, r, m, hc⟩

/-- **A preparer is solicited once** per email. -/
theorem a_preparer_is_solicited_once {pre post : mailbox.XLog} {a t k p : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.email (.solicited a t k p m)) :: post)) :
    ∀ o m', (.inr (MailEvent.email (.solicited o t k p m')) : mailbox.XEv) ∉ pre := by
  have := h.holdsNamed "preparer_is_solicited_once"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at this
  intro o m' hm
  rw [contains_of_mem pre t (.email (.solicited o t k p m')) ("preparer", k, p) hm (by simp)
    (by simp [notes, emailNotes])] at this
  exact Bool.noConfusion this

/-! ## The .eml files of an email are distinct -/

/-- The `.eml` an email event names of its email, if it names one. -/
def emlOf : EmailEvent → Option (Id × String)
  | .created _ _ k (some u) _ | .drafted _ _ k u _ _ | .sent _ _ k u _ => some (k, u)
  | .created _ _ _ none _ | .solicited .. | .prepared .. | .discarded .. => none

theorem eml_note {x : EmailEvent} {k u : String} (hx : emlOf x = some (k, u)) :
    ∃ what, namesEml what = true ∧ (what, k, u) ∈ notes (.email x) := by
  cases x with
  | created a t k' r m =>
    cases r with
    | none => simp [emlOf] at hx
    | some v =>
      simp only [emlOf, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨"reply_to", rfl, by simp [notes, emailNotes]⟩
  | _ => simp_all [emlOf, notes, emailNotes, namesEml]

theorem item_of_eml {x : EmailEvent} {k u : String} (hx : emlOf x = some (k, u)) : item x = k := by
  cases x with
  | created a t k' r m => cases r <;> simp_all [emlOf, item]
  | _ => simp_all [emlOf, item]

theorem email_noted_after {l1 l2 post : mailbox.XLog} {x : EmailEvent} {k u : String}
    (h : ValidX (l1 ++ .inr (.email x) :: (l2 ++ post))) (hx : emlOf x = some (k, u)) :
    noted ((evs (l1 ++ .inr (.email x) :: l2) (mailbox.evStream (.email x))).flatMap notes) "email" k = true := by
  have hw : (evs (l1 ++ .inr (.email x) :: l2) (mailbox.evStream (.email x))).flatMap notes =
      (evs l1 (mailbox.evStream (.email x))).flatMap notes ++
        (notes (.email x) ++ (evs l2 (mailbox.evStream (.email x))).flatMap notes) := by
    simp [evs_append, evs_cons_inr, List.flatMap_append, List.flatMap_cons]
  rw [hw]
  cases x with
  | created a t k' r m =>
    cases r with
    | none => simp [emlOf] at hx
    | some v =>
      simp only [emlOf, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      simp [noted, notes, emailNotes]
  | solicited => simp [emlOf] at hx
  | prepared => simp [emlOf] at hx
  | discarded => simp [emlOf] at hx
  | _ =>
    have h3 := h.holdsNamed "email_must_exist"
    dsimp only at h3
    simp only [read_notes] at h3
    simp only [emlOf, Option.some.injEq, Prod.mk.injEq] at hx
    obtain ⟨rfl, -⟩ := hx
    exact noted_mono h3

/-- **The .eml files are distinct**: no two events of a valid log name the same `.eml` of the same email. -/
theorem emls_are_distinct {l1 l2 l3 : mailbox.XLog} {x y : EmailEvent} {k u : String}
    (h : ValidX (l1 ++ .inr (.email x) :: l2 ++ .inr (.email y) :: l3))
    (hs : mailbox.evStream (.email y) = mailbox.evStream (.email x))
    (hx : emlOf x = some (k, u)) (hy : emlOf y = some (k, u)) : False := by
  obtain ⟨what, hw, hn⟩ := eml_note hx
  have hnamed : emlNamed ((evs (l1 ++ .inr (.email x) :: l2) (mailbox.evStream (.email y))).flatMap notes) k u
      = true := by
    simp only [emlNamed, List.any_eq_true]
    exact ⟨(what, k, u), List.contains_iff_mem.mp
      (contains_of_mem (l1 ++ .inr (.email x) :: l2) (mailbox.evStream (.email y)) (.email x) (what, k, u)
        (by simp) hs.symm hn), by simp [hw]⟩
  have hk : noted ((evs (l1 ++ .inr (.email x) :: l2) (mailbox.evStream (.email y))).flatMap notes) "email" k
      = true := by
    rw [hs]; exact email_noted_after (by simpa [List.append_assoc] using h) hx
  cases y with
  | created a t k' r m =>
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
  | prepared => simp [emlOf] at hy
  | discarded => simp [emlOf] at hy
  | _ =>
    have h4 := h.holdsNamed "eml_urls_must_be_unique"
    dsimp only at h4
    simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at h4
    simp only [Commands.evStream_mk] at hnamed
    simp only [emlOf, Option.some.injEq, Prod.mk.injEq] at hy
    rw [hy.1, hy.2, hnamed] at h4
    exact Bool.noConfusion h4

/-- **The sent message is none of the others.** -/
theorem the_sent_message_is_none_of_the_others {pre post : mailbox.XLog} {a t k : Id} {u : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.email (.sent a t k u m)) :: post)) :
    emlNamed ((evs pre t).flatMap notes) k u = false := by
  have := h.holdsNamed "eml_urls_must_be_unique"
  dsimp only at this
  simpa using this

/-- **The sent message is no draft.** -/
theorem the_sent_message_is_no_draft {log : mailbox.XLog} (h : ValidX log) {d a t k : Id} {u s : String}
    {m m' : Meta} (hp : (.inr (MailEvent.email (.drafted d t k u s m)) : mailbox.XEv) ∈ log)
    (hr : (.inr (MailEvent.email (.sent a t k u m')) : mailbox.XEv) ∈ log) : False := by
  rcases mem_mem_split hp hr (by simp) with ⟨l1, l2, l3, rfl⟩ | ⟨l1, l2, l3, rfl⟩
  · exact emls_are_distinct h rfl (x := .drafted d t k u s m) rfl rfl
  · exact emls_are_distinct h rfl (x := .sent a t k u m') rfl rfl

/-- **No draft is the message replied to.** -/
theorem no_draft_is_the_message_replied_to {log : mailbox.XLog} (h : ValidX log) {o d t k : Id} {u s : String}
    {m m' : Meta} (hb : (.inr (MailEvent.email (.created o t k (some u) m)) : mailbox.XEv) ∈ log)
    (hp : (.inr (MailEvent.email (.drafted d t k u s m')) : mailbox.XEv) ∈ log) : False := by
  rcases mem_mem_split hb hp (by simp) with ⟨l1, l2, l3, rfl⟩ | ⟨l1, l2, l3, rfl⟩
  · exact emls_are_distinct h rfl (x := .created o t k (some u) m) rfl rfl
  · exact emls_are_distinct h rfl (x := .drafted d t k u s m') rfl rfl

/-! ## A decision is final -/

def decides : EmailEvent → Bool
  | .sent .. | .discarded .. => true
  | _ => false

theorem decided_of_decides {d : EmailEvent} (hd : decides d = true) {w1 w2 : List Note} :
    emailDecided (w1 ++ notes (.email d) ++ w2) (item d) = true := by
  cases d <;> simp_all [decides, emailDecided, item, noted, notes, emailNotes]

/-- **An email is decided once.** -/
theorem an_email_is_decided_once {pre post : mailbox.XLog} {d : EmailEvent} (hd : decides d = true)
    (h : ValidX (pre ++ .inr (.email d) :: post)) :
    emailDecided ((evs pre (mailbox.evStream (.email d))).flatMap notes) (item d) = false := by
  have := h.holdsNamed "email_is_decided_once"
  dsimp only at this
  cases d <;> simp_all [decides, item]

theorem no_event_once_decided {pre post : mailbox.XLog} {x : EmailEvent}
    (h : ValidX (pre ++ .inr (.email x) :: post))
    (hex : noted ((evs pre (mailbox.evStream (.email x))).flatMap notes) "email" (item x) = true)
    (hdec : emailDecided ((evs pre (mailbox.evStream (.email x))).flatMap notes) (item x) = true) : False := by
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

theorem decision_admitted {pre post : mailbox.XLog} {d : EmailEvent} (hd : decides d = true)
    (h : ValidX (pre ++ .inr (.email d) :: post)) :
    noted ((evs pre (mailbox.evStream (.email d))).flatMap notes) "email" (item d) = true := by
  have h3 := h.holdsNamed "email_must_exist"
  dsimp only at h3
  simp only [read_notes] at h3
  cases d <;> simp only [decides, Bool.false_eq_true] at hd <;> simpa [item] using h3

/-- **Nothing follows a decision**: after an email is sent or discarded, no email event about it is accepted. -/
theorem nothing_follows_a_decision {pre mid post : mailbox.XLog} {d x : EmailEvent} (hd : decides d = true)
    (h : ValidX (pre ++ .inr (.email d) :: mid ++ .inr (.email x) :: post))
    (hs : mailbox.evStream (.email x) = mailbox.evStream (.email d)) (hk : item x = item d) : False := by
  have hd' : ValidX (pre ++ .inr (.email d) :: (mid ++ .inr (.email x) :: post)) := by
    simpa [List.append_assoc] using h
  have hw : (evs (pre ++ .inr (.email d) :: mid) (mailbox.evStream (.email x))).flatMap notes =
      (evs pre (mailbox.evStream (.email d))).flatMap notes ++ notes (.email d) ++
        (evs mid (mailbox.evStream (.email d))).flatMap notes := by
    rw [hs]; simp [evs_append, evs_cons_inr, List.flatMap_append, List.flatMap_cons, List.append_assoc]
  have hex := decision_admitted hd hd'
  refine no_event_once_decided h ?_ ?_ <;> rw [hw, hk]
  · simp only [noted, List.any_append, Bool.or_eq_true]; exact Or.inl (Or.inl (by simpa [noted] using hex))
  · exact decided_of_decides hd

/-! ## Acceptance: the owner's or a delegate's send; soliciting and preparing go on after a draft -/

/-- **The creator can always send**: a theorem of acceptance. After any valid log in which stream `t` is open, `a`
is the owner or a person delegate of the owner, email `k` is created and not decided, and the `.eml` `u` is
not yet named on `k`, the service accepts `a`'s `email.send` of `k` at `u`. -/
theorem the_creator_can_always_send {pre : mailbox.XLog} (h : ValidX pre) {a t k : Id} {u : String} {m : Meta}
    (hopen : Past.opened (cores pre) t = true) (hclosed : Past.closed (cores pre) t = false)
    (hauth : personForOwner (Past.opener (cores pre) t) ((evs pre t).flatMap notes) a = true)
    (hk : noted ((evs pre t).flatMap notes) "email" k = true)
    (hu : emlNamed ((evs pre t).flatMap notes) k u = false)
    (hdec : emailDecided ((evs pre t).flatMap notes) k = false) :
    mailbox.service.respond pre (.inr (a, .email (.send t k u m), [])) =
      .accepted (.inr (.email (.sent a t k u m))) := by
  refine Service.respond_accepted_iff.mpr ⟨rfl, ?_⟩
  have hv : ValidX (pre ++ [.inr (.email (.sent a t k u m))]) := by
    refine (ValidX.snoc_inr_iff h).mpr ⟨?_, ?_, ?_, ?_⟩
    · show (Past.view (cores pre) t).admits a = none
      exact View.admits_none.mpr ⟨by simpa using hopen, by simpa using hclosed⟩
    · rfl
    · intro r hr
      simp only [mailbox, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        <;> simp [hauth, hk, hu, hdec, Past.view]
    · intro r hr
      simp at hr
  exact (Service.Valid.inv hv).2

/-- **The owner or a delegate can always solicit**: a theorem of acceptance. After any valid log in which stream `t`
is open, `a` is the owner or a delegate of the owner, email `k` is created and not decided, and `p` is neither
`a`, nor the owner, nor yet a preparer or a drafter of `k`, the service accepts `a`'s `email.solicit` of `p`. Drafts
of `k` do not matter: soliciting goes on after them. -/
theorem soliciting_goes_on_after_a_draft {pre : mailbox.XLog} (h : ValidX pre) {a t k p : Id} {m : Meta}
    (hopen : Past.opened (cores pre) t = true) (hclosed : Past.closed (cores pre) t = false)
    (hauth : forOwner (Past.opener (cores pre) t) ((evs pre t).flatMap notes) a = true)
    (hp : a ≠ p) (hpo : Past.opener (cores pre) t ≠ some p)
    (hdecl : (noted ((evs pre t).flatMap notes) "invited" p || noted ((evs pre t).flatMap notes) "summoned" p) = true)
    (hk : noted ((evs pre t).flatMap notes) "email" k = true)
    (hs : ((evs pre t).flatMap notes).contains ("preparer", k, p) = false)
    (hd : ((evs pre t).flatMap notes).contains ("drafter", k, p) = false)
    (hdec : emailDecided ((evs pre t).flatMap notes) k = false) :
    mailbox.service.respond pre (.inr (a, .email (.solicit t k p m), [])) =
      .accepted (.inr (.email (.solicited a t k p m))) := by
  refine Service.respond_accepted_iff.mpr ⟨rfl, ?_⟩
  have hv : ValidX (pre ++ [.inr (.email (.solicited a t k p m))]) := by
    refine (ValidX.snoc_inr_iff h).mpr ⟨?_, ?_, ?_, ?_⟩
    · show (Past.view (cores pre) t).admits a = none
      exact View.admits_none.mpr ⟨by simpa using hopen, by simpa using hclosed⟩
    · rfl
    · intro r hr
      simp only [mailbox, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        <;> simp_all
    · intro r hr
      simp at hr
  exact (Service.Valid.inv hv).2

/-- **A solicited preparer can always prepare**: a theorem of acceptance. Drafts of `k` do not matter: preparing goes
on after them. -/
theorem preparing_goes_on_after_a_draft {pre : mailbox.XLog} (h : ValidX pre) {t k p : Id} {u : String} {m : Meta}
    (hopen : Past.opened (cores pre) t = true) (hclosed : Past.closed (cores pre) t = false)
    (hk : noted ((evs pre t).flatMap notes) "email" k = true)
    (hs : ((evs pre t).flatMap notes).contains ("preparer", k, p) = true)
    (hdec : emailDecided ((evs pre t).flatMap notes) k = false) :
    mailbox.service.respond pre (.inr (p, .email (.prepare t k u m), [])) =
      .accepted (.inr (.email (.prepared p t k u m))) := by
  refine Service.respond_accepted_iff.mpr ⟨rfl, ?_⟩
  have hv : ValidX (pre ++ [.inr (.email (.prepared p t k u m))]) := by
    refine (ValidX.snoc_inr_iff h).mpr ⟨?_, ?_, ?_, ?_⟩
    · show (Past.view (cores pre) t).admits p = none
      exact View.admits_none.mpr ⟨by simpa using hopen, by simpa using hclosed⟩
    · rfl
    · intro r hr
      simp only [mailbox, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        <;> simp_all
    · intro r hr
      simp at hr
  exact (Service.Valid.inv hv).2

end Email

/-! # The triage's guarantees -/

namespace Triage

theorem triage_note {e : MailEvent} {k q : String} (h : ("triage", k, q) ∈ notes e) :
    ∃ a t m, e = .triage (.requested a t k q m) := by
  rcases e with e | e | e <;> cases e <;> simp_all [notes, principalNotes, emailNotes, triageNotes]

theorem adviser_note {e : MailEvent} {k q : String} (h : ("adviser", k, q) ∈ notes e) :
    ∃ a t m, e = .triage (.asked a t k q m) := by
  rcases e with e | e | e <;> cases e <;> simp_all [notes, principalNotes, emailNotes, triageNotes]

theorem asked_of_contains {pre : mailbox.XLog} {t k d : Id}
    (h : ((evs pre t).flatMap notes).contains ("adviser", k, d) = true) :
    ∃ o m', (.inr (MailEvent.triage (.asked o t k d m')) : mailbox.XEv) ∈ pre := by
  obtain ⟨e, hm, hs, hn⟩ := mem_notes_evs (List.contains_iff_mem.mp h)
  obtain ⟨o, t', m', rfl⟩ := adviser_note hn
  simp only [Commands.evStream_mk] at hs
  subst hs
  exact ⟨o, m', hm⟩

/-! ## Who acts on a triage -/

theorem every_triage_is_requested_by_the_owner_or_a_delegate {pre post : mailbox.XLog} {a t k : Id} {u : String}
    {m : Meta} (h : ValidX (pre ++ .inr (.triage (.requested a t k u m)) :: post)) :
    forOwner (Past.opener (cores pre) t) ((evs pre t).flatMap notes) a = true := by
  simpa using Authority.every_act_is_by_the_owner_or_a_delegate h (x := .triage (.requested a t k u m)) rfl

theorem every_ask_is_by_the_owner_or_a_delegate {pre post : mailbox.XLog} {a t k d : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.triage (.asked a t k d m)) :: post)) :
    forOwner (Past.opener (cores pre) t) ((evs pre t).flatMap notes) a = true := by
  simpa using Authority.every_act_is_by_the_owner_or_a_delegate h (x := .triage (.asked a t k d m)) rfl

theorem every_consideration_is_by_the_owner_or_a_delegate {pre post : mailbox.XLog} {a t k : Id} {v : String}
    {m : Meta} (h : ValidX (pre ++ .inr (.triage (.considered a t k v m)) :: post)) :
    forOwner (Past.opener (cores pre) t) ((evs pre t).flatMap notes) a = true := by
  simpa using Authority.every_act_is_by_the_owner_or_a_delegate h (x := .triage (.considered a t k v m)) rfl

/-- Whether a triage event decides its triage: a reply, a work item, an ignore or a deferral. -/
def decides : TriageEvent → Bool
  | .replied .. | .worked .. | .ignored .. | .deferred .. => true
  | _ => false

def item : TriageEvent → Id
  | .requested _ _ k _ _ | .asked _ _ k _ _ | .advised _ _ k _ _ | .considered _ _ k _ _ | .replied _ _ k _ _
  | .worked _ _ k _ _ | .ignored _ _ k _ | .deferred _ _ k _ => k

/-- **Every decision is by the owner or a person delegate of the owner**: reply, work, ignore and defer. -/
theorem every_decision_is_by_the_owner_or_a_person_delegate {pre post : mailbox.XLog} {d : TriageEvent} {a : Id}
    (ha : Authority.terminal (.triage d) = some a)
    (h : ValidX (pre ++ .inr (.triage d) :: post)) :
    personForOwner (Past.opener (cores pre) (mailbox.evStream (.triage d)))
      ((evs pre (mailbox.evStream (.triage d))).flatMap notes) a = true :=
  Authority.every_terminal_decision_is_by_the_owner_or_a_person_delegate h ha

/-- **No adviser asks itself.** -/
theorem no_adviser_is_its_asker {pre post : mailbox.XLog} {a t k d : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.triage (.asked a t k d m)) :: post)) : a ≠ d := by
  have := h.holdsNamed "adviser_must_not_be_the_asker"
  dsimp only at this
  simpa using this

/-- **Every asked adviser was declared**: invited or summoned on the stream before it was asked. -/
theorem every_asked_adviser_was_declared {pre post : mailbox.XLog} {a t k d : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.triage (.asked a t k d m)) :: post)) :
    (∃ o m', (.inr (MailEvent.principal (.invited o t d m')) : mailbox.XEv) ∈ pre) ∨
      ∃ o m', (.inr (MailEvent.principal (.summoned o t d m')) : mailbox.XEv) ∈ pre := by
  have := h.holdsNamed "adviser_must_be_declared"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk, Bool.or_eq_true] at this
  rcases this with h1 | h1
  · exact Or.inl (Principals.invited_of_noted h1)
  · exact Or.inr (Principals.summoned_of_noted h1)

/-- **Every advice is by an asked adviser.** -/
theorem every_advice_is_by_an_asked_adviser {pre post : mailbox.XLog} {d t k : Id} {v : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.triage (.advised d t k v m)) :: post)) :
    ∃ o m', (.inr (MailEvent.triage (.asked o t k d m')) : mailbox.XEv) ∈ pre := by
  have := h.holdsNamed "only_asked_advisers_can_advise"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk] at this
  exact asked_of_contains this

/-! ## The roles are disjoint -/

/-- **No adviser is the owner.** -/
theorem no_adviser_is_the_owner {pre post : mailbox.XLog} {a t k d : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.triage (.asked a t k d m)) :: post)) :
    Past.opener (cores (pre ++ .inr (.triage (.asked a t k d m)) :: post)) t ≠ some d := by
  have h6' := h.holdsNamed "adviser_must_not_be_the_owner"
  dsimp only at h6'
  have h6 : Past.opener (cores pre) t ≠ some d := by simpa using h6'
  have hf := every_ask_is_by_the_owner_or_a_delegate h
  rcases Authority.forOwner_true.mp hf with h1 | ⟨o, h1, -⟩ <;> rw [opener_of_prefix h1] <;> rw [h1] at h6 <;>
    exact h6

/-- **No adviser is a considerer**: an adviser never considers its own triage, in either order. -/
theorem no_adviser_is_a_considerer {log : mailbox.XLog} (h : ValidX log) {o t k d : Id} {v : String} {m m' : Meta}
    (hb : (.inr (MailEvent.triage (.asked o t k d m)) : mailbox.XEv) ∈ log)
    (hr : (.inr (MailEvent.triage (.considered d t k v m')) : mailbox.XEv) ∈ log) : False := by
  rcases mem_mem_split hb hr (by simp) with ⟨l1, l2, l3, rfl⟩ | ⟨l1, l2, l3, rfl⟩
  · have := h.holdsNamed "considerer_must_not_be_an_adviser"
    dsimp only at this
    simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at this
    rw [contains_of_mem _ t (.triage (.asked o t k d m)) ("adviser", k, d) (by simp) (by simp)
      (by simp [notes, triageNotes])] at this
    exact Bool.noConfusion this
  · have := h.holdsNamed "adviser_must_not_be_a_considerer"
    dsimp only at this
    simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at this
    rw [contains_of_mem _ t (.triage (.considered d t k v m')) ("considerer", k, d) (by simp) (by simp)
      (by simp [notes, triageNotes])] at this
    exact Bool.noConfusion this

/-- **The roles are disjoint**: an adviser of a triage is neither its owner nor ever a considerer of it. -/
theorem roles_are_disjoint {log : mailbox.XLog} (h : ValidX log) {a t k d : Id} {m : Meta}
    (hb : (.inr (MailEvent.triage (.asked a t k d m)) : mailbox.XEv) ∈ log) :
    Past.opener (cores log) t ≠ some d ∧
      ∀ v m', (.inr (MailEvent.triage (.considered d t k v m')) : mailbox.XEv) ∉ log := by
  refine ⟨?_, fun v m' hr => no_adviser_is_a_considerer h hb hr⟩
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hb
  exact no_adviser_is_the_owner h

/-! ## Each step once, every triage requested -/

theorem a_triage_is_requested_once {pre post : mailbox.XLog} {a t k : Id} {u : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.triage (.requested a t k u m)) :: post)) :
    noted ((evs pre t).flatMap notes) "triage" k = false := by
  have := h.holdsNamed "triage_id_must_be_new"
  dsimp only at this
  simpa using this

theorem every_event_names_a_requested_triage {pre post : mailbox.XLog} {x : TriageEvent} {t : Id}
    (h : ValidX (pre ++ .inr (.triage x) :: post)) (hs : mailbox.evStream (.triage x) = t)
    (hx : match x with | .requested .. => False | _ => True) :
    ∃ a u m, (.inr (MailEvent.triage (.requested a t (item x) u m)) : mailbox.XEv) ∈ pre := by
  subst hs
  have := h.holdsNamed "triage_must_exist"
  dsimp only at this
  simp only [read_notes] at this
  have hn : noted ((evs pre (mailbox.evStream (.triage x))).flatMap notes) "triage" (item x) = true := by
    cases x <;> simp_all [item]
  obtain ⟨q, hq⟩ := noted_iff.mp hn
  obtain ⟨e, hm, hs', hn'⟩ := mem_notes_evs hq
  obtain ⟨a, t', m, rfl⟩ := triage_note hn'
  simp only [Commands.evStream_mk] at hs'
  subst hs'
  exact ⟨a, q, m, hm⟩

theorem an_adviser_is_asked_once {pre post : mailbox.XLog} {a t k d : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.triage (.asked a t k d m)) :: post)) :
    ∀ o m', (.inr (MailEvent.triage (.asked o t k d m')) : mailbox.XEv) ∉ pre := by
  have := h.holdsNamed "adviser_is_asked_once"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at this
  intro o m' hm
  rw [contains_of_mem pre t (.triage (.asked o t k d m')) ("adviser", k, d) hm (by simp)
    (by simp [notes, triageNotes])] at this
  exact Bool.noConfusion this

/-- **An adviser advises once** per triage. -/
theorem an_adviser_advises_once {pre post : mailbox.XLog} {d t k : Id} {v : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.triage (.advised d t k v m)) :: post)) :
    ∀ v' m', (.inr (MailEvent.triage (.advised d t k v' m')) : mailbox.XEv) ∉ pre := by
  have := h.holdsNamed "adviser_advises_once"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk, Bool.not_eq_true'] at this
  intro v' m' hm
  rw [contains_of_mem pre t (.triage (.advised d t k v' m')) ("advice", k, d) hm (by simp)
    (by simp [notes, triageNotes])] at this
  exact Bool.noConfusion this

/-! ## A decision is final: reply, work, ignore and defer alike -/

theorem decided_of_decides {d : TriageEvent} (hd : decides d = true) {w1 w2 : List Note} :
    triageDecided (w1 ++ notes (.triage d) ++ w2) (item d) = true := by
  cases d <;> simp_all [decides, triageDecided, item, noted, notes, triageNotes]

theorem a_triage_is_decided_once {pre post : mailbox.XLog} {d : TriageEvent} (hd : decides d = true)
    (h : ValidX (pre ++ .inr (.triage d) :: post)) :
    triageDecided ((evs pre (mailbox.evStream (.triage d))).flatMap notes) (item d) = false := by
  have := h.holdsNamed "triage_is_decided_once"
  dsimp only at this
  cases d <;> simp_all [decides, item]

theorem no_event_once_decided {pre post : mailbox.XLog} {x : TriageEvent}
    (h : ValidX (pre ++ .inr (.triage x) :: post))
    (hex : noted ((evs pre (mailbox.evStream (.triage x))).flatMap notes) "triage" (item x) = true)
    (hdec : triageDecided ((evs pre (mailbox.evStream (.triage x))).flatMap notes) (item x) = true) : False := by
  cases x with
  | requested a t k u m =>
    have := h.holdsNamed "triage_id_must_be_new"
    dsimp only at this
    simp_all [item]
  | replied a t k e m =>
    have := h.holdsNamed "triage_is_decided_once"
    dsimp only at this
    simp_all [item]
  | worked a t k i m =>
    have := h.holdsNamed "triage_is_decided_once"
    dsimp only at this
    simp_all [item]
  | ignored a t k m =>
    have := h.holdsNamed "triage_is_decided_once"
    dsimp only at this
    simp_all [item]
  | deferred a t k m =>
    have := h.holdsNamed "triage_is_decided_once"
    dsimp only at this
    simp_all [item]
  | _ =>
    have := h.holdsNamed "triage_must_be_undecided"
    dsimp only at this
    simp_all [item]

theorem decision_admitted {pre post : mailbox.XLog} {d : TriageEvent} (hd : decides d = true)
    (h : ValidX (pre ++ .inr (.triage d) :: post)) :
    noted ((evs pre (mailbox.evStream (.triage d))).flatMap notes) "triage" (item d) = true := by
  have h3 := h.holdsNamed "triage_must_exist"
  dsimp only at h3
  simp only [read_notes] at h3
  cases d <;> simp only [decides, Bool.false_eq_true] at hd <;> simpa [item] using h3

/-- **Nothing follows a decision**: after a triage is replied, made a work item, ignored or deferred, no triage event
about it is accepted. -/
theorem nothing_follows_a_decision {pre mid post : mailbox.XLog} {d x : TriageEvent} (hd : decides d = true)
    (h : ValidX (pre ++ .inr (.triage d) :: mid ++ .inr (.triage x) :: post))
    (hs : mailbox.evStream (.triage x) = mailbox.evStream (.triage d)) (hk : item x = item d) : False := by
  have hd' : ValidX (pre ++ .inr (.triage d) :: (mid ++ .inr (.triage x) :: post)) := by
    simpa [List.append_assoc] using h
  have hw : (evs (pre ++ .inr (.triage d) :: mid) (mailbox.evStream (.triage x))).flatMap notes =
      (evs pre (mailbox.evStream (.triage d))).flatMap notes ++ notes (.triage d) ++
        (evs mid (mailbox.evStream (.triage d))).flatMap notes := by
    rw [hs]; simp [evs_append, evs_cons_inr, List.flatMap_append, List.flatMap_cons, List.append_assoc]
  have hex := decision_admitted hd hd'
  refine no_event_once_decided h ?_ ?_ <;> rw [hw, hk]
  · simp only [noted, List.any_append, Bool.or_eq_true]; exact Or.inl (Or.inl (by simpa [noted] using hex))
  · exact decided_of_decides hd

/-- **Nothing follows a deferral**: a deferral closes its triage as the other decisions do. Coming back to the
message is a new `triage.request`. -/
theorem nothing_follows_a_deferral {pre mid post : mailbox.XLog} {a t k : Id} {m : Meta} {x : TriageEvent}
    (h : ValidX (pre ++ .inr (.triage (.deferred a t k m)) :: mid ++ .inr (.triage x) :: post))
    (hs : mailbox.evStream (.triage x) = t) (hk : item x = k) : False :=
  nothing_follows_a_decision (d := .deferred a t k m) rfl h (by simpa using hs) hk

/-! ## Acceptance: ignore and defer; asking and advising go on after a consideration -/

/-- **The creator can always ignore**: a theorem of acceptance. After any valid log in which stream `t` is open, `a`
is the owner or a person delegate of the owner, and triage `k` is requested and not decided, the service
accepts `a`'s `triage.ignore` of `k`. -/
theorem the_creator_can_always_ignore {pre : mailbox.XLog} (h : ValidX pre) {a t k : Id} {m : Meta}
    (hopen : Past.opened (cores pre) t = true) (hclosed : Past.closed (cores pre) t = false)
    (hauth : personForOwner (Past.opener (cores pre) t) ((evs pre t).flatMap notes) a = true)
    (hk : noted ((evs pre t).flatMap notes) "triage" k = true)
    (hdec : triageDecided ((evs pre t).flatMap notes) k = false) :
    mailbox.service.respond pre (.inr (a, .triage (.ignore t k m), [])) =
      .accepted (.inr (.triage (.ignored a t k m))) := by
  refine Service.respond_accepted_iff.mpr ⟨rfl, ?_⟩
  have hv : ValidX (pre ++ [.inr (.triage (.ignored a t k m))]) := by
    refine (ValidX.snoc_inr_iff h).mpr ⟨?_, ?_, ?_, ?_⟩
    · show (Past.view (cores pre) t).admits a = none
      exact View.admits_none.mpr ⟨by simpa using hopen, by simpa using hclosed⟩
    · rfl
    · intro r hr
      simp only [mailbox, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        <;> simp [hauth, hk, hdec, Past.view]
    · intro r hr
      simp at hr
  exact (Service.Valid.inv hv).2

/-- **The creator can always defer**, under the same hypotheses as the ignore. -/
theorem the_creator_can_always_defer {pre : mailbox.XLog} (h : ValidX pre) {a t k : Id} {m : Meta}
    (hopen : Past.opened (cores pre) t = true) (hclosed : Past.closed (cores pre) t = false)
    (hauth : personForOwner (Past.opener (cores pre) t) ((evs pre t).flatMap notes) a = true)
    (hk : noted ((evs pre t).flatMap notes) "triage" k = true)
    (hdec : triageDecided ((evs pre t).flatMap notes) k = false) :
    mailbox.service.respond pre (.inr (a, .triage (.defer t k m), [])) =
      .accepted (.inr (.triage (.deferred a t k m))) := by
  refine Service.respond_accepted_iff.mpr ⟨rfl, ?_⟩
  have hv : ValidX (pre ++ [.inr (.triage (.deferred a t k m))]) := by
    refine (ValidX.snoc_inr_iff h).mpr ⟨?_, ?_, ?_, ?_⟩
    · show (Past.view (cores pre) t).admits a = none
      exact View.admits_none.mpr ⟨by simpa using hopen, by simpa using hclosed⟩
    · rfl
    · intro r hr
      simp only [mailbox, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        <;> simp [hauth, hk, hdec, Past.view]
    · intro r hr
      simp at hr
  exact (Service.Valid.inv hv).2

/-- **The owner or a delegate can always ask**: a theorem of acceptance. Considerations of `k` do not matter: asking
goes on after them. -/
theorem asking_goes_on_after_a_consideration {pre : mailbox.XLog} (h : ValidX pre) {a t k d : Id} {m : Meta}
    (hopen : Past.opened (cores pre) t = true) (hclosed : Past.closed (cores pre) t = false)
    (hauth : forOwner (Past.opener (cores pre) t) ((evs pre t).flatMap notes) a = true)
    (hd : a ≠ d) (hdo : Past.opener (cores pre) t ≠ some d)
    (hdecl : (noted ((evs pre t).flatMap notes) "invited" d || noted ((evs pre t).flatMap notes) "summoned" d) = true)
    (hk : noted ((evs pre t).flatMap notes) "triage" k = true)
    (hs : ((evs pre t).flatMap notes).contains ("adviser", k, d) = false)
    (hc : ((evs pre t).flatMap notes).contains ("considerer", k, d) = false)
    (hdec : triageDecided ((evs pre t).flatMap notes) k = false) :
    mailbox.service.respond pre (.inr (a, .triage (.ask t k d m), [])) =
      .accepted (.inr (.triage (.asked a t k d m))) := by
  refine Service.respond_accepted_iff.mpr ⟨rfl, ?_⟩
  have hv : ValidX (pre ++ [.inr (.triage (.asked a t k d m))]) := by
    refine (ValidX.snoc_inr_iff h).mpr ⟨?_, ?_, ?_, ?_⟩
    · show (Past.view (cores pre) t).admits a = none
      exact View.admits_none.mpr ⟨by simpa using hopen, by simpa using hclosed⟩
    · rfl
    · intro r hr
      simp only [mailbox, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        <;> simp_all
    · intro r hr
      simp at hr
  exact (Service.Valid.inv hv).2

/-- **An asked adviser can always advise, once**: a theorem of acceptance. Considerations of `k` do not matter:
advising goes on after them. -/
theorem advising_goes_on_after_a_consideration {pre : mailbox.XLog} (h : ValidX pre) {t k d : Id} {v : String}
    {m : Meta}
    (hopen : Past.opened (cores pre) t = true) (hclosed : Past.closed (cores pre) t = false)
    (hk : noted ((evs pre t).flatMap notes) "triage" k = true)
    (hs : ((evs pre t).flatMap notes).contains ("adviser", k, d) = true)
    (ha : ((evs pre t).flatMap notes).contains ("advice", k, d) = false)
    (hdec : triageDecided ((evs pre t).flatMap notes) k = false) :
    mailbox.service.respond pre (.inr (d, .triage (.advise t k v m), [])) =
      .accepted (.inr (.triage (.advised d t k v m))) := by
  refine Service.respond_accepted_iff.mpr ⟨rfl, ?_⟩
  have hv : ValidX (pre ++ [.inr (.triage (.advised d t k v m))]) := by
    refine (ValidX.snoc_inr_iff h).mpr ⟨?_, ?_, ?_, ?_⟩
    · show (Past.view (cores pre) t).admits d = none
      exact View.admits_none.mpr ⟨by simpa using hopen, by simpa using hclosed⟩
    · rfl
    · intro r hr
      simp only [mailbox, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        <;> simp_all
    · intro r hr
      simp at hr
  exact (Service.Valid.inv hv).2

end Triage

/-! # The reply rule: a reply is an email of this stream, and answers one triage -/

namespace Reply

/-- **Every reply names a created email.** -/
theorem every_reply_names_a_created_email {pre post : mailbox.XLog} {a t k e : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.triage (.replied a t k e m)) :: post)) :
    ∃ o r m', (.inr (MailEvent.email (.created o t e r m')) : mailbox.XEv) ∈ pre := by
  have := h.holdsNamed "reply_must_name_an_unclaimed_email"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk] at this
  have he : noted ((evs pre t).flatMap notes) "email" e = true := by
    revert this; cases noted ((evs pre t).flatMap notes) "email" e <;> simp
  obtain ⟨q, hq⟩ := noted_iff.mp he
  obtain ⟨r, m', hc⟩ := Email.created_of_note hq
  exact ⟨q, r, m', hc⟩

/-- **An email answers one triage**: no valid log has two replies on one stream, one before the other, naming the
same email. -/
theorem an_email_answers_one_triage {l1 l2 l3 : mailbox.XLog} {a a' t k k' e : Id} {m m' : Meta}
    (h : ValidX (l1 ++ .inr (.triage (.replied a t k e m)) :: l2 ++ .inr (.triage (.replied a' t k' e m')) :: l3)) :
    False := by
  have := h.holdsNamed "reply_must_name_an_unclaimed_email"
  dsimp only at this
  simp only [read_notes, Commands.evStream_mk, Bool.and_eq_true, Bool.not_eq_true'] at this
  have hc : replyClaimed ((evs (l1 ++ .inr (MailEvent.triage (.replied a t k e m)) :: l2) t).flatMap notes) e
      = true := by
    simp only [replyClaimed, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
    exact ⟨("replied", k, e), List.contains_iff_mem.mp (contains_of_mem _ t (.triage (.replied a t k e m))
      ("replied", k, e) (by simp) (by simp) (by simp [notes, triageNotes])), rfl, rfl⟩
  rw [hc] at this
  exact Bool.noConfusion this.2

/-- **No email answers two triages.** -/
theorem no_email_answers_two_triages {log : mailbox.XLog} (h : ValidX log) {a a' t k k' e : Id} {m m' : Meta}
    (h1 : (.inr (MailEvent.triage (.replied a t k e m)) : mailbox.XEv) ∈ log)
    (h2 : (.inr (MailEvent.triage (.replied a' t k' e m')) : mailbox.XEv) ∈ log) : k = k' := by
  by_cases hne : (.inr (MailEvent.triage (.replied a t k e m)) : mailbox.XEv) =
      .inr (MailEvent.triage (.replied a' t k' e m'))
  · simp only [XE.inr.injEq, MailEvent.triage.injEq, TriageEvent.replied.injEq] at hne
    exact hne.2.2.1
  · rcases mem_mem_split h1 h2 hne with ⟨l1, l2, l3, rfl⟩ | ⟨l1, l2, l3, rfl⟩
    · exact (an_email_answers_one_triage h).elim
    · exact (an_email_answers_one_triage h).elim

/-- **The creator can always reply**: a theorem of acceptance. After any valid log in which stream `t` is open, `a`
is the owner or a person delegate of the owner, triage `k` is requested and not decided, and email `e` is
created on the stream and named by no reply yet, the service accepts `a`'s `triage.reply` of `k` with `e`. -/
theorem the_creator_can_always_reply {pre : mailbox.XLog} (h : ValidX pre) {a t k e : Id} {m : Meta}
    (hopen : Past.opened (cores pre) t = true) (hclosed : Past.closed (cores pre) t = false)
    (hauth : personForOwner (Past.opener (cores pre) t) ((evs pre t).flatMap notes) a = true)
    (hk : noted ((evs pre t).flatMap notes) "triage" k = true)
    (hdec : triageDecided ((evs pre t).flatMap notes) k = false)
    (he : noted ((evs pre t).flatMap notes) "email" e = true)
    (hc : replyClaimed ((evs pre t).flatMap notes) e = false) :
    mailbox.service.respond pre (.inr (a, .triage (.reply t k e m), [])) =
      .accepted (.inr (.triage (.replied a t k e m))) := by
  refine Service.respond_accepted_iff.mpr ⟨rfl, ?_⟩
  have hv : ValidX (pre ++ [.inr (.triage (.replied a t k e m))]) := by
    refine (ValidX.snoc_inr_iff h).mpr ⟨?_, ?_, ?_, ?_⟩
    · show (Past.view (cores pre) t).admits a = none
      exact View.admits_none.mpr ⟨by simpa using hopen, by simpa using hclosed⟩
    · rfl
    · intro r hr
      simp only [mailbox, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        <;> simp [hauth, hk, hdec, he, hc, Past.view]
    · intro r hr
      simp at hr
  exact (Service.Valid.inv hv).2

end Reply

/-! ## The core's guarantees, here -/

/-- **Only the opener closes the stream** (`Layer.ValidX.close_by_opener`). -/
theorem only_the_opener_closes_the_stream {pre post : mailbox.XLog} {a t : Id} {m : Meta}
    (h : ValidX (pre ++ .inl (Event.streamClosed a t m) :: post)) : Past.opener (cores pre) t = some a :=
  h.close_by_opener

/-- **Nothing follows a close** (`Layer.ValidX.close_final`). -/
theorem nothing_follows_a_close {pre mid post : mailbox.XLog} {a t : Id} {m : Meta} {x : mailbox.XEv}
    (h : ValidX (pre ++ .inl (Event.streamClosed a t m) :: mid ++ x :: post)) : streamX x ≠ t := h.close_final

end EmailTriageAndReply
