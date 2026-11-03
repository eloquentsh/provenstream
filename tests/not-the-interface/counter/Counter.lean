-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT

/-!
# Counter: a command and event stream of its own

One event, `add n`; the stream's total is the sum of its events (`total`), and the total of two logs one after the
other is the sum of their totals (`total_append`). Nothing here is the core's: no `stream.open`, no `stream.close`.
-/

namespace Counter

inductive Ev where
  | add (n : Nat)

def total : List Ev → Nat
  | [] => 0
  | .add n :: es => n + total es

theorem total_append (a b : List Ev) : total (a ++ b) = total a + total b := by
  induction a with
  | nil => simp [total]
  | cons e es ih => cases e; simp [total, ih, Nat.add_assoc]

end Counter
