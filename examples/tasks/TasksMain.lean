-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Tasks.Examples
import Provenstream.Engine.Step
import TasksRevision

/-!
# tasks-engine

The layered engine serving the tasks layer (`Tasks.tasks`) on the core, stamped with the revision it is built
from (`TasksRevision.lean`, written before the build; not in git).

    tasks-engine                  serve JSON lines
    tasks-engine --self-test      the worked examples through the compiled code
    tasks-engine --revision       {"revision", "repo", "package"}
    tasks-engine --describe       {"revision", "repo", "package", "protocol", "schema"}
-/

def main (args : List String) : IO UInt32 :=
  Provenstream.Engine.Layered.mainAt Tasks.tasks "tasks-engine" (pure Tasks.Examples.allOk) Tasks.built args
