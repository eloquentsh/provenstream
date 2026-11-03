-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Log.Examples
import Provenstream.Engine.Step
import LogRevision

/-!
# log-engine

The layered engine serving the log layer (`Log.log`) on the core, stamped with the revision it is built from
(`LogRevision.lean`, written before the build; not in git).

    log-engine                  serve JSON lines
    log-engine --self-test      the worked examples through the compiled code
    log-engine --revision       {"revision", "repo", "package"}
    log-engine --describe       {"revision", "repo", "package", "protocol", "schema"}
-/

def main (args : List String) : IO UInt32 :=
  Provenstream.Engine.Layered.mainAt Log.log "log-engine" (pure Log.Examples.allOk) Log.built args
