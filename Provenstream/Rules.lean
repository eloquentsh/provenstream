-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Provenstream.Event

/-!
# The core's rules

A rule is a named check on a candidate event against the facts about its stream (`View`). Its name is the reason a
caller sees when it fails, and says what the rule requires. The facts are read from the whole past (`Past.view`), and
the rules are tried in the order of `rules`, the first that fails being the answer. Each rule also lists the commands
it judges (`cmds`), which is what the engine's description says of it.

| reason | refuses |
|---|---|
| `stream_id_must_be_new` | an open whose minted id names a stream already opened |
| `revision_url_must_name_a_commit` | an open whose URL is not a repository URL and a full commit |
| `stream_must_exist` | a close of a stream never opened |
| `stream_must_be_open` | a close of a closed stream |
| `only_opener_can_close` | a close by anyone but the stream's opener |

`View.admits` is what the core asks of every event a layer adds: the stream is open and not closed
(`stream_must_exist`, `stream_must_be_open`, in that order). It asks nothing of the actor: each layer says who may act,
reading `View.opener`. The layer mechanism tries it before any rule of the layer (`Layer.lean`).
-/

namespace Provenstream

abbrev Past := List Event

/-! ## What one event says -/

/-- The event opened stream `t`. -/
def opens (t : Id) : Event → Bool
  | .streamOpened _ t' .. => t' == t
  | _ => false

/-- The event closed stream `t`. -/
def closes (t : Id) : Event → Bool
  | .streamClosed _ t' .. => t' == t
  | _ => false

/-- The opener of stream `t`, if the event opened it. -/
def openerOf (t : Id) : Event → Option Id
  | .streamOpened a t' .. => if t' == t then some a else none
  | _ => none

/-! ## Facts about the past: flat statements, no index and no derived state -/

/-- Stream `t` was opened. -/
def Past.opened (past : Past) (t : Id) : Bool := past.any (opens t)

/-- Stream `t` was closed. -/
def Past.closed (past : Past) (t : Id) : Bool := past.any (closes t)

/-- The opener of stream `t`: the actor of its (first) opening, or `none` if it was not opened. -/
def Past.opener (past : Past) (t : Id) : Option Id := past.findSome? (openerOf t)

/-- Some earlier event minted `x`. A stream's id is minted by its opening and nothing else (`minted_eq_opened`). -/
def Past.minted (past : Past) (x : Id) : Bool := past.any fun p => p.mintedAll.contains x

/-! ## The facts a rule reads, about one stream -/

/-- The facts of a stream's past, as the core's rules and every layer's rules see them. -/
structure View where
  opened : Bool
  closed : Bool
  /-- `none` until opened; fixed once set (`opener_fixed`). -/
  opener : Option Id
  deriving DecidableEq

/-- The specification's view of stream `t`: the flat statements above. -/
def Past.view (past : Past) (t : Id) : View := ⟨past.opened t, past.closed t, past.opener t⟩

/-- **What the core asks of every event a layer adds**, before the layer's rules: the stream is open and not closed.
Any actor is admitted; a layer's own rules say who may act. -/
def View.admits (v : View) (_a : Id) : Option String :=
  if !v.opened then some "stream_must_exist"
  else if v.closed then some "stream_must_be_open"
  else none

/-- The reasons `View.admits` can give, in the order it tries them. -/
def admitReasons : List String := ["stream_must_exist", "stream_must_be_open"]

theorem View.admits_none {v : View} {a : Id} : v.admits a = none ↔ v.opened = true ∧ v.closed = false := by
  unfold View.admits
  cases v.opened <;> cases v.closed <;> simp

theorem View.admits_named {v : View} {a : Id} {r : String} (h : v.admits a = some r) : r ∈ admitReasons := by
  obtain ⟨o, c, op⟩ := v
  unfold View.admits at h
  cases o <;> cases c <;> simp at h <;> subst h <;> simp [admitReasons]

structure Rule where
  reason : String
  /-- The commands this rule judges (it holds of every other event): what the description lists it under. -/
  cmds : List String
  holds : View → Event → Bool

/-! ## Rules, in the order they are tried -/

def streamIdMustBeNew : Rule := ⟨"stream_id_must_be_new", ["stream.open"], fun v e =>
  match e with | .streamOpened .. => !v.opened | _ => true⟩

def revisionUrlMustNameACommit : Rule := ⟨"revision_url_must_name_a_commit", ["stream.open"], fun _ e =>
  match e with | .streamOpened _ _ u _ => validRevisionUrl u | _ => true⟩

def streamMustExist : Rule := ⟨"stream_must_exist", ["stream.close"], fun v e =>
  match e with | .streamOpened .. => true | _ => v.opened⟩

def streamMustBeOpen : Rule := ⟨"stream_must_be_open", ["stream.close"], fun v e =>
  match e with | .streamOpened .. => true | _ => !v.closed⟩

def onlyOpenerCanClose : Rule := ⟨"only_opener_can_close", ["stream.close"], fun v e =>
  match e with | .streamClosed a .. => v.opener == some a | _ => true⟩

def rules : List Rule :=
  [streamIdMustBeNew, revisionUrlMustNameACommit, streamMustExist, streamMustBeOpen, onlyOpenerCanClose]

/-- The names of the rules that judge command `n`, in the order they are tried. -/
def rulesOf (n : String) : List String := (rules.filter (·.cmds.contains n)).map (·.reason)

/-- Every rule holds for `e` against the view. -/
def View.ok (v : View) (e : Event) : Bool := rules.all fun r => r.holds v e

/-- The first rule that fails, if any: the answer a caller sees. -/
def View.rejection (v : View) (e : Event) : Option String := (rules.find? fun r => !r.holds v e).map (·.reason)

theorem View.rejection_none_iff (v : View) (e : Event) : v.rejection e = none ↔ v.ok e = true := by
  simp [View.rejection, View.ok, List.find?_eq_none, List.all_eq_true]

end Provenstream
