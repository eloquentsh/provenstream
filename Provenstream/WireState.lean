-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Provenstream.StreamState
import Provenstream.Wire

/-!
# Reads and snapshots of the core, from `StreamState`

A read of a stream answers its state as the rules see it; a snapshot is the state itself, and decodes to what it
encodes (`stateFromJ_toJ`).
-/

namespace Provenstream.Wire
open Provenstream

/-- What a read of a stream answers, from its state: its id, its opener, its proof revision and whether it is closed
(as the rules read them: `fold_view`, `fold_url`). -/
def streamSJ (st : StreamState) : J :=
  if st.opened then
    .obj [("stream_id", .str st.stream), ("opener_id", metaJ st.opener), ("proof_revision_url", metaJ st.url),
      ("closed", .bool st.closed)]
  else .obj [("error", .str "stream_must_exist")]

def stateToJ (st : StreamState) : J :=
  .obj [("stream", .str st.stream), ("opened", .bool st.opened), ("opener", metaJ st.opener),
    ("url", metaJ st.url), ("closed", .bool st.closed)]

def boolFromJ : Option J → Except String Bool
  | some (.bool b) => .ok b
  | _ => .error "state: expected a boolean"

def optFromJ : Option J → Except String (Option String)
  | some .null => .ok none
  | some (.str x) => .ok (some x)
  | _ => .error "state: expected a string or null"

def stateFromJ (j : J) : Except String StreamState := do
  let kvs ← fields "state" j
  let some (.str s) := get? kvs "stream" | throw "state.stream: missing"
  return { stream := s, opened := ← boolFromJ (get? kvs "opened"), opener := ← optFromJ (get? kvs "opener"),
           url := ← optFromJ (get? kvs "url"), closed := ← boolFromJ (get? kvs "closed") }

theorem optFromJ_toJ (o : Option String) : optFromJ (some (metaJ o)) = .ok o := by
  cases o <;> rfl

/-- **A snapshot decodes to the state it encodes.** -/
theorem stateFromJ_toJ (st : StreamState) : stateFromJ (stateToJ st) = .ok st := by
  obtain ⟨s, o, op, u, c⟩ := st
  simp [stateFromJ, stateToJ, fields, get?, List.find?, boolFromJ, optFromJ_toJ, bind, Except.bind, pure, Except.pure]

end Provenstream.Wire
