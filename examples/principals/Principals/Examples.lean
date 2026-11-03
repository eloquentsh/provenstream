-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Principals.Theorems

/-!
# Worked examples: a stream with persons, an admin and an agent

Requests with the answers they get, checked at build time (`#guard`) and compiled into the engine's `--self-test`.
Every rule of the layer, and the core's admission, refuses something.
-/

namespace Principals.Examples
open Provenstream Provenstream.Layer Principals

def url : String := "https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/principals"
def ann : Id := "a0000000-0000-4000-8000-000000000001"   -- the opener: the first admin
def ben : Id := "b0000000-0000-4000-8000-000000000002"   -- invited, then promoted: an admin
def cy : Id := "c0000000-0000-4000-8000-000000000003"    -- summoned: an agent
def dee : Id := "d0000000-0000-4000-8000-000000000004"   -- invited by ben: a person, not an admin
def eve : Id := "e0000000-0000-4000-8000-000000000005"   -- never declared
def S : Id := "50000000-0000-7000-8000-000000000001"

abbrev Sv := principals.service
def core (c : Id) (cmd : Command) (f : Fresh := []) : Sv.Req := .inl (c, cmd, f)
def pr (c : Id) (cmd : PrincipalCommand) (f : Fresh := []) : Sv.Req := .inr (c, cmd, f)

def story : List (Sv.Req × Option String) :=
  [ (pr ann (.invite S ben none), some "stream_must_exist"),                 -- the core's admission
    (core ann (.streamOpen url none) [S], none),
    (pr ann (.invite S ann none), some "principal_must_be_new"),             -- the opener is no one's invitee
    (pr ann (.invite S ben (some "a colleague")), none),
    (pr ben (.invite S dee none), some "only_admins_can_invite"),            -- invited is not admin
    (pr ann (.invite S ben none), some "principal_must_be_new"),             -- once
    (pr ann (.summon S cy none), none),
    (pr ann (.summon S ben none), some "principal_must_be_new"),             -- a person is not also an agent
    (pr ann (.invite S cy none), some "principal_must_be_new"),              -- nor an agent a person
    (pr ben (.promote S ben none), some "only_admins_can_promote"),
    (pr ann (.promote S cy none), some "principal_must_be_invited"),         -- agents are never promoted
    (pr ann (.promote S eve none), some "principal_must_be_invited"),
    (pr ann (.promote S ben none), none),                                    -- ben is an admin now
    (pr ann (.promote S ben none), some "principal_is_promoted_once"),
    (pr ben (.invite S dee none), none),                                     -- and invites
    (pr dee (.summon S eve none), some "only_admins_can_summon"),
    (pr cy (.summon S eve none), some "only_admins_can_summon"),             -- an agent declares no one
    (pr ann (.invite S dee none) [S], some "fresh_ids_must_match_the_command"),
    (core ben (.streamClose S none), some "only_opener_can_close"),          -- admins do not close: the opener does
    (core ann (.streamClose S none), none),
    (pr ann (.invite S eve none), some "stream_must_be_open") ]

def answersOk : Bool :=
  let (_, answers) := Sv.run (story.map (·.1))
  answers.length == story.length &&
    (answers.zip story).all fun (x, (_, want)) =>
      match x, want with
      | .accepted _, none => true
      | .rejected r, some r' => r == r'
      | _, _ => false

#guard answersOk

def checksOk : Bool :=
  let (log, answers) := Sv.run (story.map (·.1))
  Sv.check log && (Sv.runS (Sv.init S) (story.map (·.1))).2 == answers

#guard checksOk

def everyRuleBites : Bool :=
  (principals.rules.map (·.reason) ++ ["stream_must_exist", "stream_must_be_open"]).all fun r =>
    story.any fun (_, want) => want == some r

#guard everyRuleBites

def allOk : Bool := answersOk && checksOk && everyRuleBites

end Principals.Examples
