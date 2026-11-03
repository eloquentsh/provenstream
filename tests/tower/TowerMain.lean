-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Tower
import Provenstream.Engine.Step
import TowerRevision

/-!
# tower-engine

The engine of the three-level tower: layer B (`Tower.reviews`) on layer A (`Tasks.tasks`) on the core, stamped
with the revision it is built from (`TowerRevision.lean`, written before the build; not in git).
-/

def main (args : List String) : IO UInt32 :=
  Provenstream.Engine.Layered.mainAt Tower.reviews "tower-engine" (pure Tower.Examples.storyOk) Tower.built args
