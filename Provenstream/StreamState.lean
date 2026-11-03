-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Provenstream.Command

/-!
# The fast path: a stream's state, folded event by event

The engine keeps, per stream, a small state that each accepted event updates (`StreamState.step`); the rules read
their `View` from it (`StreamState.view`) and decide with it (`rejectionS`). Each field changes on one event exactly as
the fact it stands for does, so folding a log gives the fact over the whole log (`fold_view`). A snapshot is a state and
the number of events it folds.
-/

namespace Provenstream

theorem beq_eq_decide (a b : Id) : (a == b) = decide (a = b) := by rw [Bool.eq_iff_iff]; simp

/-- One stream's state: what the rules need to know of its past, and what reads show. -/
structure StreamState where
  stream : Id
  opened : Bool := false
  opener : Option Id := none
  url : Option String := none
  closed : Bool := false
  deriving Repr, DecidableEq

def StreamState.init (s : Id) : StreamState := { stream := s }

/-- The first value given, kept. -/
def keep {α} (o : Option α) (x : α) : Option α :=
  match o with
  | some y => some y
  | none => some x

/-- One accepted event. An event of another stream changes nothing. -/
def StreamState.step (st : StreamState) (e : Event) : StreamState :=
  if e.stream = st.stream then
    match e with
    | .streamOpened a _ u _ => { st with opened := true, opener := keep st.opener a, url := keep st.url u }
    | .streamClosed .. => { st with closed := true }
  else st

/-- The state of stream `s` after a log. -/
def fold (s : Id) (L : Log) : StreamState := L.foldl StreamState.step (StreamState.init s)

/-! ## Decisions from the state -/

/-- The rules' view of the stream, read from its state. -/
def StreamState.view (st : StreamState) : View := ⟨st.opened, st.closed, st.opener⟩

/-- The first rule that fails, from the state. -/
def rejectionS (st : StreamState) (e : Event) : Option String := st.view.rejection e

/-! ## The state is the past, fact by fact -/

theorem step_stream (st : StreamState) (e : Event) : (st.step e).stream = st.stream := by
  unfold StreamState.step; split
  · cases e <;> rfl
  · rfl

theorem step_opened (st : StreamState) (e : Event) : (st.step e).opened = (st.opened || opens st.stream e) := by
  unfold StreamState.step; split <;> cases e <;> simp_all [opens, Event.stream]

theorem step_closed (st : StreamState) (e : Event) : (st.step e).closed = (st.closed || closes st.stream e) := by
  unfold StreamState.step; split <;> cases e <;> simp_all [closes, Event.stream]

theorem step_opener (st : StreamState) (e : Event) : (st.step e).opener = st.opener.or (openerOf st.stream e) := by
  unfold StreamState.step
  split
  · rename_i hs
    cases e with
    | streamOpened a t u m =>
      simp only [Event.stream] at hs; subst hs
      cases st.opener <;> simp [keep, openerOf]
    | _ => cases st.opener <;> simp [openerOf]
  · rename_i hs
    cases e with
    | streamOpened a t u m =>
      simp only [Event.stream] at hs
      cases st.opener <;> simp [openerOf, hs]
    | _ => cases st.opener <;> simp [openerOf]

/-- A Boolean field that an event sets exactly when `f` says so folds to "some event says so". -/
theorem foldl_any {g : StreamState → Bool} {f : Id → Event → Bool}
    (hstep : ∀ st e, g (st.step e) = (g st || f st.stream e)) (st : StreamState) (L : Log) :
    g (L.foldl StreamState.step st) = (g st || L.any (f st.stream)) := by
  induction L generalizing st with
  | nil => simp
  | cons e es ih => simp [ih, hstep, step_stream, Bool.or_assoc]

theorem fold_any {g : StreamState → Bool} {f : Id → Event → Bool}
    (hstep : ∀ st e, g (st.step e) = (g st || f st.stream e)) (hinit : ∀ s, g (StreamState.init s) = false)
    (s : Id) (L : Log) : g (fold s L) = L.any (f s) := by
  rw [fold, foldl_any hstep, hinit]; simp [StreamState.init]

theorem findSome_cons {α : Type} (f : Event → Option α) (e : Event) (es : Log) :
    (e :: es).findSome? f = (f e).or (es.findSome? f) := by
  cases h : f e <;> simp [h]

/-- An optional field that keeps the first value an event gives (by `f`) folds to the first value of the log. -/
theorem foldl_findSome {α : Type} {g : StreamState → Option α} {f : Id → Event → Option α}
    (hstep : ∀ st e, g (st.step e) = (g st).or (f st.stream e)) (st : StreamState) (L : Log) :
    g (L.foldl StreamState.step st) = (g st).or (L.findSome? (f st.stream)) := by
  induction L generalizing st with
  | nil => simp
  | cons e es ih => rw [List.foldl_cons, ih, hstep, step_stream, findSome_cons, Option.or_assoc]

theorem fold_findSome {α : Type} {g : StreamState → Option α} {f : Id → Event → Option α}
    (hstep : ∀ st e, g (st.step e) = (g st).or (f st.stream e)) (hinit : ∀ s, g (StreamState.init s) = none)
    (s : Id) (L : Log) : g (fold s L) = L.findSome? (f s) := by
  rw [fold, foldl_findSome hstep, hinit]; rfl

theorem fold_stream (s : Id) (L : Log) : (fold s L).stream = s := by
  unfold fold
  suffices ∀ st : StreamState, (L.foldl StreamState.step st).stream = st.stream from this _
  induction L with
  | nil => intro; rfl
  | cons e es ih => intro st; simp [List.foldl_cons, ih, step_stream]

theorem fold_opened (s : Id) (L : Log) : (fold s L).opened = Past.opened L s :=
  fold_any step_opened (fun _ => rfl) s L

theorem fold_closed (s : Id) (L : Log) : (fold s L).closed = Past.closed L s :=
  fold_any step_closed (fun _ => rfl) s L

theorem fold_opener (s : Id) (L : Log) : (fold s L).opener = Past.opener L s :=
  fold_findSome step_opener (fun _ => rfl) s L

/-- **The state's view is the log's view.** No hypothesis: it holds for logs that are not valid too. -/
theorem fold_view (s : Id) (L : Log) : (fold s L).view = Past.view L s := by
  rw [StreamState.view, Past.view, fold_opened, fold_closed, fold_opener]

theorem rejectionS_eq (L : Log) (e : Event) : rejectionS (fold e.stream L) e = rejection L e := by
  unfold rejectionS rejection; rw [fold_view]

theorem snapshot_equiv (s : Id) (L₁ L₂ : Log) : fold s (L₁ ++ L₂) = L₂.foldl StreamState.step (fold s L₁) := by
  simp [fold, List.foldl_append]

theorem fold_snoc (s : Id) (L : Log) (e : Event) : fold s (L ++ [e]) = (fold s L).step e := by
  simp [fold, List.foldl_append]

end Provenstream
