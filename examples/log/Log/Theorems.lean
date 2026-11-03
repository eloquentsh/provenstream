-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Log.Layer

/-!
# The log's guarantees

Its own, from its one rule (`ValidX.holdsNamed`), and the core's, inherited through `h.cores` and `Layer.lean`.
-/

namespace Log
open Provenstream Provenstream.Layer

/-- **Every append is by the stream's opener**: in a valid log, the actor of a `log.appended` is the opener of its
stream, as the core's events before it say. -/
theorem append_by_opener {pre post : log.XLog} {a t : Id} {x : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.appended a t x m) :: post)) : Past.opener (cores pre) t = some a := by
  have := h.holdsNamed "only_opener_can_append"
  dsimp only at this
  simpa using this

/-- Every append is on an open, unclosed stream (the core's admission, `ValidX.admitted_open`). -/
theorem append_on_open_stream {pre post : log.XLog} {a t : Id} {x : String} {m : Meta}
    (h : ValidX (pre ++ .inr (.appended a t x m) :: post)) :
    Past.opened (cores pre) t = true ∧ Past.closed (cores pre) t = false := by
  simpa using h.admitted_open

end Log
