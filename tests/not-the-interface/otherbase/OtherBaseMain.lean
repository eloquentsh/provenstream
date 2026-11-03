-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import OtherBase
import Provenstream.Engine.Step
import OtherBaseRevision

/-!
# otherbase-engine

The tasks layer's commands and rules, served by the convention (`Layered.mainAt`), but on `looseBase`: a copy of the
core's base with `only_opener_can_close` taken out. A valid proof whose layer does not inherit from the core's proof.
-/

def main (args : List String) : IO UInt32 :=
  Provenstream.Engine.Layered.mainAt OtherBase.tasks "otherbase-engine" (pure OtherBase.otherCloses) OtherBase.built
    args
