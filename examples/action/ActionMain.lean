-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Action.Examples
import Provenstream.Engine.Step
import ActionRevision

/-!
# action-engine

The layered engine serving the action layer (`Action.actions`) on the core, stamped with the revision it is built from
(`PostRevision.lean`, written before the build; not in git).

    action-engine                  serve JSON lines
    action-engine --self-test      the worked examples through the compiled code
    action-engine --revision       {"revision", "repo", "package"}
    action-engine --describe       {"revision", "repo", "package", "protocol", "schema"}
-/

def main (args : List String) : IO UInt32 :=
  Provenstream.Engine.Layered.mainAt Action.actions "action-engine" (pure Action.Examples.allOk) Action.built args
