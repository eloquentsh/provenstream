-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import EmailTriage.Examples
import Provenstream.Engine.Step
import EmailTriageRevision

/-!
# emailtriage-engine

The layered engine serving the inbound email triage layer (`EmailTriage.inbound`) on the core, stamped with the
revision it is built from (`EmailTriageRevision.lean`, written before the build; not in git).

    emailtriage-engine                  serve JSON lines
    emailtriage-engine --self-test      the worked examples through the compiled code
    emailtriage-engine --revision       {"revision", "repo", "package"}
    emailtriage-engine --describe       {"revision", "repo", "package", "protocol", "schema"}
-/

def main (args : List String) : IO UInt32 :=
  Provenstream.Engine.Layered.mainAt EmailTriage.inbound "emailtriage-engine" (pure EmailTriage.Examples.allOk) EmailTriage.built args
