-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import SoloChangeControl.Examples
import Provenstream.Engine.Step
import SoloChangeControlRevision

/-!
# solochangecontrol-engine

The layered engine serving the solo change control layer (`SoloChangeControl.solo`) on the core, stamped with the
revision it is built from (`SoloChangeControlRevision.lean`, written before the build; not in git).

    solochangecontrol-engine                  serve JSON lines
    solochangecontrol-engine --self-test      the worked examples through the compiled code
    solochangecontrol-engine --revision       {"revision", "repo", "package"}
    solochangecontrol-engine --describe       {"revision", "repo", "package", "protocol", "schema"}
-/

def main (args : List String) : IO UInt32 :=
  Provenstream.Engine.Layered.mainAt SoloChangeControl.solo "solochangecontrol-engine"
    (pure SoloChangeControl.Examples.allOk) SoloChangeControl.built args
