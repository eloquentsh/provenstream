-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
/-!
# JSON values, as the proofs see them

`J` is a JSON value with objects as lists of pairs, so a decoder can be stated and proved without a map type. Bytes to
`J` and back is `Engine/Json.lean` (unproved: gap_wire_bytes). Numbers and booleans never occur in a request; they are
kept so answers can say `"accept": true` and `"at": 3`.

Core Lean only.
-/

namespace Provenstream.Wire

/-- A JSON value. -/
inductive J where
  | null
  | bool (b : Bool)
  | num (n : Nat)
  | str (s : String)
  | arr (xs : List J)
  | obj (kvs : List (String × J))

abbrev Fields := List (String × J)

/-- No U+0000 (the JSON edge decodes an escaped surrogate to U+0000, so a string holding one is refused). -/
def noNul (s : String) : Bool := !s.any (· == '\x00')

def fields (what : String) : J → Except String Fields
  | .obj kvs => .ok kvs
  | _ => .error s!"{what}: expected an object"

def onlyKeys (what : String) (kvs : Fields) (allowed : List String) : Except String Unit :=
  match kvs.find? (fun kv => !allowed.contains kv.1) with
  | some (k, _) => .error s!"{what}: unknown key {k}"
  | none => .ok ()

def get? (kvs : Fields) (k : String) : Option J := (kvs.find? (·.1 == k)).map (·.2)

/-- A string field, as it is. Forms are checked once the whole value is decoded. -/
def str (what : String) (kvs : Fields) (k : String) : Except String String :=
  match get? kvs k with
  | some (.str s) => .ok s
  | some _ => .error s!"{what}.{k}: expected a string"
  | none => .error s!"{what}.{k}: missing"

/-- Accept a decoded value only if it is well formed. -/
def checked {α} (what : String) (wf : α → Bool) (x : α) : Except String α :=
  if wf x then .ok x
  else .error s!"{what}: a field is not of its form (an id that is not a canonical lowercase UUID, a string holding U+0000 or a control character, meta over 4096 bytes, or a value its kind refuses)"

/-- An array of strings. -/
def strs (what : String) : J → Except String (List String)
  | .arr xs => xs.mapM fun
    | .str s => .ok s
    | _ => .error s!"{what}: expected strings"
  | _ => .error s!"{what}: expected an array"

/-- The string under key `k` of a JSON object, if there is one. -/
def keyStr (k : String) : J → Option String
  | .obj kvs => match get? kvs k with
    | some (.str n) => some n
    | _ => none
  | _ => none

/-- The object names one of `names` under key `k`. -/
def hasName (k : String) (names : List String) (j : J) : Bool :=
  match keyStr k j with
  | some n => names.contains n
  | none => false

/-- The name of the command a request carries: the `command` key of its `command` object. -/
def cmdName : J → Option String
  | .obj kvs => (get? kvs "command").bind (keyStr "command")
  | _ => none

/-- The `command` object of a request. -/
def cmdObj : J → Option Fields
  | .obj kvs => match get? kvs "command" with
    | some (.obj c) => some c
    | _ => none
  | _ => none

/-- A request's three parts: its `actor_id`, `command` and `fresh` values, and no other key. -/
def requestParts (j : J) : Except String (J × J × J) := do
  let kvs ← fields "request" j
  onlyKeys "request" kvs ["actor_id", "command", "fresh"]
  let some c := get? kvs "actor_id" | throw "request.actor_id: missing"
  let some cmd := get? kvs "command" | throw "request.command: missing"
  let some f := get? kvs "fresh" | throw "request.fresh: missing"
  return (c, cmd, f)

def malformedJ (detail : String) : J := .obj [("error", .str "malformed"), ("detail", .str detail)]

def notTranslation : String := "a stored event is not the translation of its stored request"

theorem checked_ok {α} {w : String} {wf : α → Bool} {x : α} (h : wf x = true) : checked w wf x = .ok x := by
  simp [checked, h]

theorem checked_wf {α} {w : String} {wf : α → Bool} {x y : α} (h : checked w wf x = .ok y) : wf y = true := by
  unfold checked at h
  split at h
  · cases h; assumption
  · cases h

theorem strs_toJ (what : String) (l : List String) : strs what (.arr (l.map .str)) = .ok l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [strs, List.map_cons, List.mapM_cons] at ih ⊢
    simp [ih, bind, Except.bind, pure, Except.pure]

theorem get?_of_mem {kvs : Fields} {k : String} {j : J} (hn : (kvs.map (·.1)).Nodup) (h : (k, j) ∈ kvs) :
    get? kvs k = some j := by
  induction kvs with
  | nil => cases h
  | cons kv kvs ih =>
    obtain ⟨k', j'⟩ := kv
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rcases List.mem_cons.mp h with h | h
    · cases h; simp [get?]
    · have hne : k' ≠ k := fun e => hn.1 ⟨(k, j), h, e.symm ▸ rfl⟩
      simpa [get?, List.find?_cons, hne] using ih hn.2 h

theorem requestParts_ok {j c cmd f : J} (h : requestParts j = .ok (c, cmd, f)) :
    ∃ kvs, j = .obj kvs ∧ get? kvs "command" = some cmd := by
  unfold requestParts at h
  cases j with
  | obj kvs =>
    refine ⟨kvs, rfl, ?_⟩
    simp only [fields, bind, Except.bind] at h
    cases ho : onlyKeys "request" kvs ["actor_id", "command", "fresh"] with
    | error e => rw [ho] at h; cases h
    | ok u =>
      rw [ho] at h
      cases hc : get? kvs "actor_id" with
      | none => rw [hc] at h; cases h
      | some c' =>
        rw [hc] at h
        cases hm : get? kvs "command" with
        | none => rw [hm] at h; cases h
        | some m =>
          rw [hm] at h
          cases hf : get? kvs "fresh" with
          | none => rw [hf] at h; cases h
          | some f' =>
            rw [hf] at h
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            rw [h.2.1]
  | _ => simp [fields, bind, Except.bind] at h

theorem requestParts_toJ (c cmd f : J) :
    requestParts (.obj [("actor_id", c), ("command", cmd), ("fresh", f)]) = .ok (c, cmd, f) := by
  simp [requestParts, fields, onlyKeys, get?, List.find?, bind, Except.bind, pure, Except.pure]

end Provenstream.Wire
