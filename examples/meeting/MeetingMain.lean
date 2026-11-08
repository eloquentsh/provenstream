-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Meeting.Examples
import Provenstream.Engine.Step
import MeetingRevision

/-!
# meeting-engine

The layered engine serving the meeting layer (`Meeting.meetings`) on the core, stamped with the revision it is built from
(`MeetingRevision.lean`, written before the build; not in git).

    meeting-engine                  serve JSON lines
    meeting-engine --self-test      the worked examples through the compiled code
    meeting-engine --revision       {"revision", "repo", "package"}
    meeting-engine --describe       {"revision", "repo", "package", "protocol", "schema"}
-/

def main (args : List String) : IO UInt32 :=
  Provenstream.Engine.Layered.mainAt Meeting.meetings "meeting-engine" (pure Meeting.Examples.allOk) Meeting.built args
