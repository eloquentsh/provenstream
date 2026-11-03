-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Principals.Examples
import Provenstream.Engine.Step
import PrincipalsRevision

/-!
# principals-engine

The layered engine serving the principals layer (`Principals.principals`) on the core, stamped with the revision it
is built from (`PrincipalsRevision.lean`, written before the build; not in git).

    principals-engine                  serve JSON lines
    principals-engine --self-test      the worked examples through the compiled code
    principals-engine --revision       {"revision", "repo", "package"}
    principals-engine --describe       {"revision", "repo", "package", "protocol", "schema"}
-/

def main (args : List String) : IO UInt32 :=
  Provenstream.Engine.Layered.mainAt Principals.principals "principals-engine" (pure Principals.Examples.allOk)
    Principals.built args
