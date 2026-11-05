-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Email.Examples
import Provenstream.Engine.Step
import EmailRevision

/-!
# email-engine

The layered engine serving the email layer (`Email.outbound`) on the core, stamped with the revision it is built from
(`EmailRevision.lean`, written before the build; not in git).

    email-engine                  serve JSON lines
    email-engine --self-test      the worked examples through the compiled code
    email-engine --revision       {"revision", "repo", "package"}
    email-engine --describe       {"revision", "repo", "package", "protocol", "schema"}
-/

def main (args : List String) : IO UInt32 :=
  Provenstream.Engine.Layered.mainAt Email.outbound "email-engine" (pure Email.Examples.allOk) Email.built args
