-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Provenstream.Rules

/-!
# The log, and deciding against it

A log is the list of accepted events, oldest first. A candidate is accepted when every rule holds against the log as it
stands; the first rule that fails is the rejection. Every rule reads only the candidate's own stream
(`rejection_local`). `Valid` and `check` are the generic ones of `Service.lean` at the base (`Core.lean`).
-/

namespace Provenstream

abbrev Log := List Event

def ok (past : Past) (e : Event) : Bool := (past.view e.stream).ok e

def rejection (past : Past) (e : Event) : Option String := (past.view e.stream).rejection e

/-- Accept a candidate: append it, or name the first rule it fails. -/
def accept (log : Log) (e : Event) : Except String Log :=
  match rejection log e with
  | some reason => .error reason
  | none => .ok (log ++ [e])

theorem rejection_none_iff (past : Past) (e : Event) : rejection past e = none ↔ ok past e = true :=
  View.rejection_none_iff _ e

/-- `accept` appends exactly when every rule holds. -/
theorem accept_ok_iff (log log' : Log) (e : Event) :
    accept log e = .ok log' ↔ ok log e = true ∧ log' = log ++ [e] := by
  unfold accept
  cases h : rejection log e with
  | none => simp [(rejection_none_iff log e).mp h, eq_comm]
  | some r =>
    have : ok log e ≠ true := fun hok => by simp [(rejection_none_iff log e).mpr hok] at h
    simp [this]

/-! ## Deciding is local to a stream -/

/-- The events of stream `s`, in order. -/
def onStream (L : Log) (s : Id) : Log := L.filter (·.stream == s)

theorem opens_stream {t : Id} {e : Event} (h : opens t e = true) : e.stream = t := by
  cases e <;> simp_all [opens, Event.stream]
theorem closes_stream {t : Id} {e : Event} (h : closes t e = true) : e.stream = t := by
  cases e <;> simp_all [closes, Event.stream]
theorem openerOf_stream {t : Id} {e : Event} (h : (openerOf t e).isSome = true) : e.stream = t := by
  cases e <;> simp only [openerOf] at h <;> (try split at h) <;> simp_all [Event.stream]

theorem any_onStream {L : Log} {s : Id} {f : Event → Bool} (hf : ∀ e, f e = true → e.stream = s) :
    (onStream L s).any f = L.any f := by
  induction L with
  | nil => rfl
  | cons e es ih =>
    simp only [onStream, List.filter_cons] at ih ⊢
    split
    · simp [ih]
    · rename_i hne
      rw [ih]
      simp only [List.any_cons]
      cases hfe : f e
      · simp
      · exact absurd (by simpa using hf e hfe) hne

theorem findSome_onStream {α : Type} {L : Log} {s : Id} {f : Event → Option α}
    (hf : ∀ e, (f e).isSome = true → e.stream = s) : (onStream L s).findSome? f = L.findSome? f := by
  induction L with
  | nil => rfl
  | cons e es ih =>
    simp only [onStream, List.filter_cons] at ih ⊢
    split
    · simp [List.findSome?_cons, ih]
    · rename_i hne
      rw [ih, List.findSome?_cons]
      cases hfe : f e
      · rfl
      · exact absurd (by simpa using hf e (by simp [hfe])) hne

theorem opened_onStream {L : Log} {s : Id} : Past.opened (onStream L s) s = Past.opened L s :=
  any_onStream fun _ => opens_stream
theorem closed_onStream {L : Log} {s : Id} : Past.closed (onStream L s) s = Past.closed L s :=
  any_onStream fun _ => closes_stream
theorem opener_onStream {L : Log} {s : Id} : Past.opener (onStream L s) s = Past.opener L s :=
  findSome_onStream fun _ => openerOf_stream

/-- **The view is local.** What the rules read about stream `s` from its own events is what they read from the whole
log. -/
theorem view_onStream (L : Log) (s : Id) : Past.view (onStream L s) s = Past.view L s := by
  simp only [Past.view, opened_onStream, closed_onStream, opener_onStream]

theorem ok_local (L : Log) (e : Event) : ok (onStream L e.stream) e = ok L e := by
  unfold ok; rw [view_onStream]

/-- **Deciding is local.** The first rule a candidate breaks, against the whole log, is the first it breaks against
its own stream's events. -/
theorem rejection_local (L : Log) (e : Event) : rejection (onStream L e.stream) e = rejection L e := by
  unfold rejection; rw [view_onStream]

end Provenstream
