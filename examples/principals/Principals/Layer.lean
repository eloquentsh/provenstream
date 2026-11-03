-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Provenstream.Interface

/-!
# Principals: roles, as a layer on the core

Three commands, each naming an existing principal (`principal_id`, any UUID: the proof cannot know which ones the host
issued):

- `principal.invite` → `principal.invited`: declares a person;
- `principal.promote` → `principal.promoted`: makes an invited person an admin;
- `principal.summon` → `principal.summoned`: declares an agent.

Only an admin sends them. The stream's opener is its first admin, implicitly (no event declares it: the rules read the
core's `v.opener`); the others are the principals promoted in the stream. A principal is declared once (invited or
summoned, never both, and never the opener: `principal_must_be_new`), only an invited principal is promoted, once, so a
summoned agent is never an admin. Person or agent is only what these events say: the core and the host know no kinds.

The memory is the facts the events state (`Memory.facts`): `("invited", p)`, `("promoted", p)`, `("summoned", p)`. A read
of a stream adds `invited`, `promoted` and `summoned`.
-/

namespace Principals
open Provenstream Provenstream.Layer

inductive PrincipalCommand where
  | invite (stream principal : Id) («meta» : Meta)
  | promote (stream principal : Id) («meta» : Meta)
  | summon (stream principal : Id) («meta» : Meta)
  deriving DecidableEq

inductive PrincipalEvent where
  | invited (actor stream principal : Id) («meta» : Meta)
  | promoted (actor stream principal : Id) («meta» : Meta)
  | summoned (actor stream principal : Id) («meta» : Meta)
  deriving DecidableEq

/-- The facts an event states. -/
def marks : PrincipalEvent → List Fact
  | .invited _ _ p _ => [("invited", p)]
  | .promoted _ _ p _ => [("promoted", p)]
  | .summoned _ _ p _ => [("summoned", p)]

/-- **An admin**, by the stream's opener (the core's view) and what the layer's events say (`w`): the opener, or a
principal promoted in the stream. -/
def isAdmin (opener : Option Id) (w : String → String → Bool) (a : Id) : Bool := opener == some a || w "promoted" a

/-- Not yet declared in the stream (neither invited nor summoned), and not its opener. -/
def isNew (opener : Option Id) (w : String → String → Bool) (p : Id) : Bool :=
  !w "invited" p && !w "summoned" p && opener != some p

def adminSentence : String := "an admin: the stream's opener, or a principal promoted in the stream"

abbrev principals : Layer where
  Cmd := PrincipalCommand
  Ev := PrincipalEvent
  toRequest
    | .invited a t p m => (a, .invite t p m)
    | .promoted a t p m => (a, .promote t p m)
    | .summoned a t p m => (a, .summon t p m)
  ofRequest
    | (a, .invite t p m) => .invited a t p m
    | (a, .promote t p m) => .promoted a t p m
    | (a, .summon t p m) => .summoned a t p m
  stream | .invite t .. | .promote t .. | .summon t .. => t
  schema := [{ name := "principal.invite", event := "principal.invited", who := some adminSentence,
               fields := [("stream_id", .uuid), ("principal_id", .uuid), ("meta", .metaOpt)] },
             { name := "principal.promote", event := "principal.promoted", who := some adminSentence,
               fields := [("stream_id", .uuid), ("principal_id", .uuid), ("meta", .metaOpt)] },
             { name := "principal.summon", event := "principal.summoned", who := some adminSentence,
               fields := [("stream_id", .uuid), ("principal_id", .uuid), ("meta", .metaOpt)] }]
  toVals
    | .invite t p m => ("principal.invite", [.s t, .s p, .m m])
    | .promote t p m => ("principal.promote", [.s t, .s p, .m m])
    | .summon t p m => ("principal.summon", [.s t, .s p, .m m])
  ofVals
    | "principal.invite", [.s t, .s p, .m m] => some (.invite t p m)
    | "principal.promote", [.s t, .s p, .m m] => some (.promote t p m)
    | "principal.summon", [.s t, .s p, .m m] => some (.summon t p m)
    | _, _ => none
  memory := Memory.facts marks
  readJ st := [("invited", .arr ((factKeys st "invited").map .str)),
               ("promoted", .arr ((factKeys st "promoted").map .str)),
               ("summoned", .arr ((factKeys st "summoned").map .str))]
  rules := [⟨"only_admins_can_invite", ["principal.invite"], fun v w e => match e with
               | .invited a .. => isAdmin v.opener w a | _ => true⟩,
            ⟨"only_admins_can_promote", ["principal.promote"], fun v w e => match e with
               | .promoted a .. => isAdmin v.opener w a | _ => true⟩,
            ⟨"only_admins_can_summon", ["principal.summon"], fun v w e => match e with
               | .summoned a .. => isAdmin v.opener w a | _ => true⟩,
            ⟨"principal_must_be_new", ["principal.invite", "principal.summon"], fun v w e => match e with
               | .invited _ _ p _ | .summoned _ _ p _ => isNew v.opener w p | _ => true⟩,
            ⟨"principal_must_be_invited", ["principal.promote"], fun _ w e => match e with
               | .promoted _ _ p _ => w "invited" p | _ => true⟩,
            ⟨"principal_is_promoted_once", ["principal.promote"], fun _ w e => match e with
               | .promoted _ _ p _ => !w "promoted" p | _ => true⟩]

end Principals
