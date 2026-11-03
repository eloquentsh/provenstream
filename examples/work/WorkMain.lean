-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Work.Examples
import Provenstream.Engine.Step
import WorkRevision

/-!
# work-engine

The layered engine serving the work layer (`Work.work`) on the core, stamped with the revision it is built from
(`WorkRevision.lean`, written before the build; not in git).

    work-engine                  serve JSON lines
    work-engine --self-test      the worked examples through the compiled code
    work-engine --revision       {"revision", "repo", "package"}
    work-engine --describe       {"revision", "repo", "package", "protocol", "schema"}
-/

def main (args : List String) : IO UInt32 :=
  Provenstream.Engine.Layered.mainAt Work.work "work-engine" (pure Work.Examples.allOk) Work.built args
