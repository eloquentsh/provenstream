-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Principals.Layer

/-!
# The principals layer's guarantees

Each is about a valid log of the layer (`ValidX`) and reads the layer's events of one stream (`evs log t`) through
`said`: whether one of them states a fact. They follow from the rules that held when each event was accepted
(`ValidX.holdsNamed`) and from the core's opener (`v.opener`); the core's own guarantees (`close_by_opener`,
`opener_fixed`, ...) hold here too, through `Layer.lean`.
-/

namespace Principals
open Provenstream Provenstream.Layer

/-- Some event of `past` states fact `f` of principal `p` (`"invited"`, `"promoted"` or `"summoned"`): what the layer's
memory reads. -/
def said (past : List PrincipalEvent) : String → Id → Bool := fun f p => past.any fun e => (marks e).contains (f, p)

@[simp] theorem said_nil (f : String) (p : Id) : said [] f p = false := rfl

@[simp] theorem said_append (a b : List PrincipalEvent) (f : String) (p : Id) :
    said (a ++ b) f p = (said a f p || said b f p) := by simp [said, List.any_append]

@[simp] theorem said_cons (e : PrincipalEvent) (past : List PrincipalEvent) (f : String) (p : Id) :
    said (e :: past) f p = ((marks e).contains (f, p) || said past f p) := by simp [said]

/-- What the layer's rules read of the stream's events is `said`. -/
theorem read_said (past : List PrincipalEvent) : (Memory.facts marks).read past = said past := rfl

theorem read_said' (past : List PrincipalEvent) (f : String) (p : Id) :
    (Memory.facts marks).read past f p = said past f p := rfl

/-- A fact a layer event states of `p` names that principal, on that event's stream. -/
theorem said_mem {log : principals.XLog} {t : Id} {f : String} {p : Id} (h : said (evs log t) f p = true) :
    ∃ e, .inr e ∈ log ∧ principals.evStream e = t ∧ (marks e).contains (f, p) = true := by
  obtain ⟨e, he, hc⟩ := List.any_eq_true.mp h
  exact ⟨e, (mem_evs.mp he).1, (mem_evs.mp he).2, hc⟩

theorem said_marks {e : PrincipalEvent} {f : String} {p : Id} (h : (marks e).contains (f, p) = true) :
    (f = "invited" ∧ ∃ a t m, e = .invited a t p m) ∨ (f = "promoted" ∧ ∃ a t m, e = .promoted a t p m) ∨
      (f = "summoned" ∧ ∃ a t m, e = .summoned a t p m) := by
  cases e <;> simp_all [marks]

/-! ## Who declares -/

/-- **Every declaration is by an admin**: every invite, promote and summon in a valid log is by the stream's opener or
a principal promoted in the stream before it. -/
theorem declarations_by_admins {pre post : principals.XLog} {x : PrincipalEvent}
    (h : ValidX (pre ++ .inr x :: post)) :
    isAdmin (Past.opener (cores pre) (principals.evStream x)) (said (evs pre (principals.evStream x)))
      (evActor (L := principals) x) = true := by
  cases x with
  | invited a t p m =>
    have := h.holdsNamed "only_admins_can_invite"; dsimp only at this
    simp only [read_said, Past.view_opener] at this; simpa [evActor, cores] using this
  | promoted a t p m =>
    have := h.holdsNamed "only_admins_can_promote"; dsimp only at this
    simp only [read_said, Past.view_opener] at this; simpa [evActor, cores] using this
  | summoned a t p m =>
    have := h.holdsNamed "only_admins_can_summon"; dsimp only at this
    simp only [read_said, Past.view_opener] at this; simpa [evActor, cores] using this

/-- **A principal is invited or summoned at most once in a stream**, and never its opener: at every invite or summon of
`p` in a valid log, no event before it declared `p`, and `p` is not the opener. -/
theorem declared_once {pre post : principals.XLog} {x : PrincipalEvent} {a t p : Id} {m : Meta}
    (hx : x = .invited a t p m ∨ x = .summoned a t p m) (h : ValidX (pre ++ .inr x :: post)) :
    said (evs pre t) "invited" p = false ∧ said (evs pre t) "summoned" p = false ∧ Past.opener (cores pre) t ≠ some p := by
  have := h.holdsNamed "principal_must_be_new"
  rcases hx with rfl | rfl <;> dsimp only at this <;> simp only [read_said, Past.view_opener, isNew] at this <;>
    simpa [cores, and_assoc] using this

/-- An invited principal is promoted at most once: at every promote of `p`, `p` was invited before and not promoted. -/
theorem promoted_once {pre post : principals.XLog} {a t p : Id} {m : Meta}
    (h : ValidX (pre ++ .inr (.promoted a t p m) :: post)) :
    said (evs pre t) "invited" p = true ∧ said (evs pre t) "promoted" p = false := by
  have h1 := h.holdsNamed "principal_must_be_invited"
  have h2 := h.holdsNamed "principal_is_promoted_once"
  dsimp only at h1 h2
  simp only [read_said'] at h1 h2
  simpa using And.intro h1 h2

/-! ## Roles -/

/-- Every principal promoted in a stream of a valid log was invited in it. -/
theorem promoted_was_invited {log : principals.XLog} (h : ValidX log) {t p : Id}
    (hp : said (evs log t) "promoted" p = true) : said (evs log t) "invited" p = true := by
  obtain ⟨e, he, hs, hc⟩ := said_mem hp
  rcases said_marks hc with ⟨hf, _⟩ | ⟨-, a, t', m, rfl⟩ | ⟨hf, _⟩
  · exact absurd hf (by decide)
  · simp only [Commands.evStream_mk] at hs
    subst hs
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem he
    have := (promoted_once h).1
    simp [this]
  · exact absurd hf (by decide)

/-- **Admins are persons**: every admin of a stream other than its opener was invited in it (a person, as this layer's
events say). Nothing proves the opener a person: that is decided where tokens are issued. -/
theorem admins_are_persons {log : principals.XLog} (h : ValidX log) {t p : Id}
    (hp : isAdmin (Past.opener (cores log) t) (said (evs log t)) p = true) :
    Past.opener (cores log) t = some p ∨ said (evs log t) "invited" p = true := by
  simp only [isAdmin, Bool.or_eq_true, beq_iff_eq] at hp
  rcases hp with hp | hp
  · exact .inl hp
  · exact .inr (promoted_was_invited h hp)

/-- Induction on a valid log of the layer, stated over `principals.XLog`. -/
@[elab_as_elim] theorem valid_induction {motive : (log : principals.XLog) → ValidX log → Prop} (nil : motive [] .nil)
    (snoc : ∀ {log : principals.XLog} {e : principals.XEv} (hv : ValidX log)
      (hok : principals.service.ok log e = true), motive log hv → motive (log ++ [e]) (.snoc hv hok))
    {log : principals.XLog} (h : ValidX log) : motive log h :=
  Service.Valid.rec (motive := fun l h => motive l h) nil (fun hv hok ih => snoc hv hok ih) h

/-- **One role**: no principal is both invited (a person) and summoned (an agent) in a stream of a valid log. -/
theorem one_role {log : principals.XLog} (h : ValidX log) (t p : Id) :
    ¬ (said (evs log t) "invited" p = true ∧ said (evs log t) "summoned" p = true) := by
  induction h using valid_induction with
  | nil => simp
  | @snoc log e hv hok ih =>
    have hv' : ValidX (log ++ [e]) := .snoc hv hok
    cases e with
    | inl e => simpa using ih
    | inr x =>
      have hnew : ∀ a t' q m, (x = .invited a t' q m ∨ x = .summoned a t' q m) →
          said (evs log t') "invited" q = false ∧ said (evs log t') "summoned" q = false :=
        fun a t' q m hx => ⟨(declared_once (post := []) hx hv').1, (declared_once (post := []) hx hv').2.1⟩
      cases x with
      | invited a t' q m =>
        have := hnew a t' q m (.inl rfl)
        by_cases ht : t' = t <;> by_cases hq : p = q <;> simp_all [marks]
      | summoned a t' q m =>
        have := hnew a t' q m (.inr rfl)
        by_cases ht : t' = t <;> by_cases hq : p = q <;> simp_all [marks]
      | promoted a t' q m =>
        by_cases ht : t' = t <;> simp_all [marks]

/-- **Agents are never promoted**: a principal summoned in a stream of a valid log is not promoted in it, so never an
admin unless it is the opener (which `principal_must_be_new` refuses to summon). -/
theorem agents_never_promoted {log : principals.XLog} (h : ValidX log) {t p : Id}
    (hs : said (evs log t) "summoned" p = true) : said (evs log t) "promoted" p = false := by
  cases hp : said (evs log t) "promoted" p
  · rfl
  · exact absurd ⟨promoted_was_invited h hp, hs⟩ (one_role h t p)

/-- **Declarations are permanent**: once a stream's events say a principal was invited, summoned or promoted, they say
so in every extension of the log. No hypothesis: nothing removes an event. -/
theorem declared_permanent {log : principals.XLog} {t p : Id} {f : String} (h : said (evs log t) f p = true)
    (post : principals.XLog) : said (evs (log ++ post) t) f p = true := by
  simp [h]

/-- So is being an admin: the opener stays the opener (`opener_stays`), and a promotion stays. -/
theorem admin_stays {log : principals.XLog} {t p : Id}
    (h : isAdmin (Past.opener (cores log) t) (said (evs log t)) p = true) (post : principals.XLog) :
    isAdmin (Past.opener (cores (log ++ post)) t) (said (evs (log ++ post) t)) p = true := by
  simp only [isAdmin, Bool.or_eq_true, beq_iff_eq] at h ⊢
  rcases h with h | h
  · exact .inl (by simpa [cores] using opener_stays h (cores post))
  · exact .inr (declared_permanent h post)

end Principals
