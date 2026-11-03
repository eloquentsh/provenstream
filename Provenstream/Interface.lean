-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Provenstream.Theorems
import Provenstream.Layer

/-!
# The interface a layer builds on

A layer imports this module and nothing else of the core, and relies only on the declarations it writes against, with
their statements, and on the guarantees every layer gets, by name (`Layer.ValidX.base`, `Layer.ValidX.cores`,
`Layer.ValidX.admitted`, `Layer.ValidX.holds`, `Layer.ValidX.close_by_opener`, `Layer.ValidX.opener_fixed`,
`Layer.ValidX.close_final`, `Layer.ValidX.proof_revision_unique`, and the core theorems of `Theorems.lean` through
`h.cores`). A layer's rules read the stream's opener as `v.opener` (the core's `View`): that is where every permission
a layer grants starts. The engine for a layer, on the core or on a tower of layers, is
`Provenstream.Engine.Layered.main` (`Engine/Step.lean`), which a layer's `Main.lean` imports beside its own modules.
-/

namespace Provenstream

/-! ## The view of a stream is its facts of the past -/

@[simp] theorem Past.view_opened (past : Past) (t : Id) : (past.view t).opened = past.opened t := rfl
@[simp] theorem Past.view_closed (past : Past) (t : Id) : (past.view t).closed = past.closed t := rfl
@[simp] theorem Past.view_opener (past : Past) (t : Id) : (past.view t).opener = past.opener t := rfl

/-! ## The stream and the actor of an event, by its constructor -/

@[simp] theorem Event.stream_streamOpened (a t : Id) (u : String) (m : Meta) :
    (Event.streamOpened a t u m).stream = t := rfl
@[simp] theorem Event.stream_streamClosed (a t : Id) (m : Meta) : (Event.streamClosed a t m).stream = t := rfl
@[simp] theorem Event.actor_streamOpened (a t : Id) (u : String) (m : Meta) :
    (Event.streamOpened a t u m).actor = a := rfl
@[simp] theorem Event.actor_streamClosed (a t : Id) (m : Meta) : (Event.streamClosed a t m).actor = a := rfl

end Provenstream
