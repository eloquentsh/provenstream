-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import ProvenstreamCheck
import Provenstream

/-!
# Audit of the decision functions' dependency tree (`ProvenstreamCheck.audit`)

Run: `lake env lean scripts/Audit.lean` (scripts/check.sh).
-/

open Lean in
#eval ProvenstreamCheck.audit
  [``Provenstream.handle, ``Provenstream.accept, ``Provenstream.check, ``Provenstream.run,
   ``Provenstream.toEvent, ``Provenstream.rejection, ``Provenstream.ok, ``Provenstream.View.admits,
   ``Provenstream.Wire.stepJ, ``Provenstream.Wire.replayRows, ``Provenstream.Wire.rowFromJ,
   ``Provenstream.Wire.requestFromJ, ``Provenstream.Wire.responseToJ, ``Provenstream.Wire.malformedJ,
   ``Provenstream.stepS, ``Provenstream.respondS, ``Provenstream.fold,
   ``Provenstream.Wire.replaySFrom, ``Provenstream.Wire.stateFromJ, ``Provenstream.Wire.stateToJ,
   ``Provenstream.Wire.streamSJ, ``Provenstream.Wire.entryRequest, ``Provenstream.Wire.entrySync,
   ``Provenstream.schemaJ,
   -- the services themselves: every field the generic functions call, the base's and any layer's
   ``Provenstream.coreService, ``Provenstream.Layer.service]
  [`Provenstream]
