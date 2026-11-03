-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import ProvenstreamCheck
import Provenstream

/-!
# The axiom check (`ProvenstreamCheck.axioms`)

Every declaration under `Provenstream` depends on `propext`, `Quot.sound` and `Classical.choice` at most.
Run: `lake env lean scripts/Axioms.lean` (scripts/check.sh).
-/

open Lean in
#eval ProvenstreamCheck.axioms [`Provenstream]
