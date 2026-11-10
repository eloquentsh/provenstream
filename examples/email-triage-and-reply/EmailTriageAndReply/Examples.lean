-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import EmailTriageAndReply.Theorems

/-!
# Worked examples: one person's mail, triaged and answered on one stream

Requests with the answers they get, checked at build time (`#guard`) and compiled into the engine's `--self-test`.
Every rule of the layer and the core's admission refuse something. The opener first declares its helpers and
delegates to an agent and to a person. An email is then prepared, drafted by the agent and sent by the person. Then
messages are triaged on the same stream, and the replies name emails of this stream.
-/

namespace EmailTriageAndReply.Examples
open Provenstream Provenstream.Layer EmailTriageAndReply

def url : String :=
  "https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/email-triage-and-reply"
def ann : Id := "a0000000-0000-4000-8000-000000000001"   -- the opener, the owner of every item
def ben : Id := "b0000000-0000-4000-8000-000000000002"   -- someone else on the host, never declared
def cy : Id := "c0000000-0000-4000-8000-000000000003"    -- an invited person: a preparer, an adviser
def dee : Id := "d0000000-0000-4000-8000-000000000004"   -- a summoned agent: a preparer, an adviser
def eve : Id := "e0000000-0000-4000-8000-000000000005"   -- a summoned agent, ann's delegate: drafts and considers
def fay : Id := "f0000000-0000-4000-8000-000000000006"   -- an invited person, ann's delegate: may also decide
def gus : Id := "90000000-0000-4000-8000-000000000007"   -- a summoned agent, hal's delegate: nothing on ann's items
def hal : Id := "a1000000-0000-4000-8000-000000000008"   -- an invited person, invited by eve for ann
def S : Id := "50000000-0000-7000-8000-000000000001"
def E1 : Id := "60000000-0000-7000-8000-000000000001"   -- emails
def E2 : Id := "60000000-0000-7000-8000-000000000002"
def E3 : Id := "60000000-0000-7000-8000-000000000003"   -- never created
def E4 : Id := "60000000-0000-7000-8000-000000000004"
def E5 : Id := "60000000-0000-7000-8000-000000000005"   -- the reply to the first triaged message
def T1 : Id := "61000000-0000-7000-8000-000000000001"   -- triages
def T2 : Id := "61000000-0000-7000-8000-000000000002"
def T3 : Id := "61000000-0000-7000-8000-000000000003"
def T4 : Id := "61000000-0000-7000-8000-000000000004"
def T5 : Id := "61000000-0000-7000-8000-000000000005"   -- the deferred message, back again
def W1 : Id := "80000000-0000-7000-8000-000000000001"   -- a work item on the work proof's stream
def W2 : Id := "80000000-0000-7000-8000-000000000002"

/-- The .eml files, as the harness would name them. -/
def eml (n : String) : String := s!"https://example.org/mail/{n}.eml"
def IN := eml "inbound"
def D1 := eml "d1"
def D2 := eml "d2"
def D3 := eml "d3"
def OUT := eml "sent"
def OUT2 := eml "sent2"
def M1 := eml "m1"
def M2 := eml "m2"
def M3 := eml "m3"
def M4 := eml "m4"
def S1 : String := "https://example.org/screens/s1"
def S2 : String := "https://example.org/screens/s2"
def P1 : String := "https://example.org/prep/p1"
def P2 : String := "https://example.org/prep/p2"
def P3 : String := "https://example.org/prep/p3"
def P4 : String := "https://example.org/prep/p4"

abbrev Sv := mailbox.service
def core (c : Id) (cmd : Command) (f : Fresh := []) : Sv.Req := .inl (c, cmd, f)
def pr (c : Id) (cmd : PrincipalCommand) (f : Fresh := []) : Sv.Req := .inr (c, .principal cmd, f)
def em (c : Id) (cmd : EmailCommand) (f : Fresh := []) : Sv.Req := .inr (c, .email cmd, f)
def tr (c : Id) (cmd : TriageCommand) (f : Fresh := []) : Sv.Req := .inr (c, .triage cmd, f)

def story : List (Sv.Req × Option String) :=
  [ (em ann (.create S E1 (some IN) none), some "stream_must_exist"),                   -- the core's admission
    (core ann (.streamOpen url none) [S], none),
    -- principals: persons and agents, and delegations
    (pr ben (.invite S cy none), some "only_opener_or_delegates_can_invite"),
    (pr ann (.invite S ann none), some "principal_must_be_new"),                         -- the opener is a person already
    (pr ann (.invite S cy none), none),
    (pr ann (.invite S cy none), some "principal_must_be_new"),
    (pr ann (.summon S cy none), some "principal_must_be_new"),                          -- never both
    (pr ben (.summon S dee none), some "only_opener_or_delegates_can_summon"),
    (pr ann (.summon S dee none), none),
    (pr ann (.summon S eve none), none),
    (pr ann (.invite S fay none), none),
    (pr ann (.delegate S ben none), some "delegate_must_be_declared"),
    (pr dee (.delegate S cy none), some "only_persons_can_delegate"),                    -- an agent does not delegate
    (pr cy (.delegate S cy none), some "delegate_must_not_be_the_delegator"),
    (pr ann (.delegate S eve (some "an agent, drafts and considers")), none),
    (pr ann (.delegate S eve none), some "delegate_must_be_new"),
    (pr cy (.delegate S eve none), some "delegate_must_be_new"),                         -- one delegator each
    (pr ann (.delegate S fay (some "a person, may decide")), none),
    (pr eve (.summon S gus none), none),                                                 -- the agent declares for ann
    (pr eve (.invite S hal none), none),
    (pr hal (.delegate S gus none), none),                                               -- gus acts for hal only
    (pr eve (.delegate S gus none), some "only_persons_can_delegate"),
    -- an email, prepared, drafted by the agent and sent by the person
    (em ben (.create S E1 (some IN) none), some "only_opener_or_delegates_can_create"),
    (em ann (.create S E1 (some IN) none) [E2], some "fresh_ids_must_match_the_command"),
    (em ann (.create S E1 (some IN) (some "a reply to the inbound message")), none),
    (em ann (.create S E1 none none), some "email_id_must_be_new"),
    (em ann (.solicit S E3 cy none), some "email_must_exist"),
    (em ben (.solicit S E1 cy none), some "only_owner_or_delegates_can_solicit"),
    (em gus (.solicit S E1 cy none), some "only_owner_or_delegates_can_solicit"),       -- no chain through hal
    (em ann (.solicit S E1 ann none), some "preparer_must_not_be_the_owner"),
    (em ann (.solicit S E1 ben none), some "preparer_must_be_declared"),
    (em eve (.solicit S E1 eve none), some "preparer_must_not_be_the_soliciter"),
    (em ann (.solicit S E1 cy none), none),
    (em ann (.solicit S E1 cy none), some "preparer_is_solicited_once"),
    (em eve (.solicit S E1 dee none), none),                                             -- the delegate solicits
    (em ben (.prepare S E1 P1 none), some "only_solicited_preparers_can_prepare"),
    (em cy (.prepare S E1 P1 none), none),
    (em cy (.prepare S E1 P2 none), none),                                               -- as often as it likes
    (em dee (.prepare S E1 P1 none), none),                                              -- a preparation may repeat
    (em cy (.draft S E1 D1 S1 none), some "drafter_must_not_be_a_preparer"),
    (em ben (.draft S E1 D1 S1 none), some "only_owner_or_delegates_can_draft"),
    (em gus (.draft S E1 D1 S1 none), some "only_owner_or_delegates_can_draft"),
    (em eve (.draft S E1 IN S1 none), some "eml_urls_must_be_unique"),                  -- the message replied to
    (em eve (.draft S E3 D1 S1 none), some "email_must_exist"),
    (em eve (.draft S E1 D1 S1 none), none),                                             -- the agent drafts
    (em ann (.draft S E1 D2 S2 none), none),                                             -- and so may the owner
    (em ann (.solicit S E1 eve none), some "preparer_must_not_be_a_drafter"),
    (em ann (.solicit S E1 fay none), none),                                             -- soliciting goes on after a draft
    (em fay (.prepare S E1 P3 none), none),                                              -- and preparing
    (em eve (.send S E1 OUT none), some "only_owner_or_person_delegates_can_decide"),   -- an agent does not send
    (em gus (.send S E1 OUT none), some "only_owner_or_person_delegates_can_decide"),
    (em ann (.send S E1 D2 none), some "eml_urls_must_be_unique"),                       -- a draft
    (em ann (.send S E1 IN none), some "eml_urls_must_be_unique"),                       -- the inbound message
    (em ann (.send S E3 OUT none), some "email_must_exist"),
    (em fay (.send S E1 OUT (some "sent for ann")), none),                               -- the person delegate sends
    (em ann (.send S E1 OUT2 none), some "email_is_decided_once"),
    (em ann (.discard S E1 none), some "email_is_decided_once"),
    (em eve (.draft S E1 D3 S1 none), some "email_must_be_undecided"),                  -- nothing about E1 follows
    (em fay (.prepare S E1 P4 none), some "email_must_be_undecided"),
    (em ann (.solicit S E1 hal none), some "email_must_be_undecided"),
    (em eve (.create S E2 none none), none),                                             -- the delegate creates, for ann
    (em fay (.discard S E2 (some "not worth sending")), none),
    (em cy (.prepare S E2 P1 none), some "only_solicited_preparers_can_prepare"),       -- nobody was solicited on E2
    (em ann (.create S E4 (some OUT) none), none),                                       -- a reply to what E1 sent
    (em ann (.send S E4 OUT2 none), none),
    -- triage, on the same stream
    (tr ben (.request S T1 M1 none), some "only_opener_or_delegates_can_request"),
    (tr ann (.request S T1 M1 none) [T2], some "fresh_ids_must_match_the_command"),
    (tr ann (.request S T1 M1 (some "a catch-up cancelled")), none),
    (tr ann (.request S T1 M1 none), some "triage_id_must_be_new"),
    (tr ann (.ask S T3 cy none), some "triage_must_exist"),
    (tr ben (.ask S T1 cy none), some "only_owner_or_delegates_can_ask"),
    (tr ann (.ask S T1 ann none), some "adviser_must_not_be_the_owner"),
    (tr ann (.ask S T1 ben none), some "adviser_must_be_declared"),
    (tr eve (.ask S T1 eve none), some "adviser_must_not_be_the_asker"),
    (tr ann (.ask S T1 cy none), none),
    (tr ann (.ask S T1 cy none), some "adviser_is_asked_once"),
    (tr eve (.ask S T1 dee none), none),                                                 -- the delegate asks
    (tr ben (.advise S T1 "reply" none), some "only_asked_advisers_can_advise"),
    (tr cy (.advise S T1 "reply" (some "a person wrote and waits")), none),
    (tr cy (.advise S T1 "ignore" none), some "adviser_advises_once"),
    (tr cy (.consider S T1 "reply" none), some "considerer_must_not_be_an_adviser"),
    (tr ben (.consider S T1 "reply" none), some "only_owner_or_delegates_can_consider"),
    (tr gus (.consider S T1 "reply" none), some "only_owner_or_delegates_can_consider"),
    (tr eve (.consider S T3 "reply" none), some "triage_must_exist"),
    (tr eve (.consider S T1 "reply" (some "one line offering another time")), none),
    (tr ann (.consider S T1 "reply" none), none),                                        -- the owner considers too
    (tr ann (.ask S T1 eve none), some "adviser_must_not_be_a_considerer"),
    (tr ann (.ask S T1 fay none), none),                                                 -- asking goes on after a consideration
    (tr dee (.advise S T1 "defer" none), none),                                          -- and advising
    (tr fay (.advise S T1 "ignore" none), none),
    (tr eve (.reply S T1 E5 none), some "only_owner_or_person_delegates_can_decide"),   -- an agent does not reply
    (tr ann (.reply S T3 E5 none), some "triage_must_exist"),
    (tr ann (.reply S T1 E5 none), some "reply_must_name_an_unclaimed_email"),          -- E5 is not created yet
    (em eve (.create S E5 (some M1) (some "the reply to m1")), none),
    (tr fay (.reply S T1 E5 (some "drafted as E5 on this stream")), none),               -- decided by the person delegate
    (tr ann (.reply S T1 E4 none), some "triage_is_decided_once"),
    (tr ann (.ignore S T1 none), some "triage_is_decided_once"),
    (tr eve (.consider S T1 "ignore" none), some "triage_must_be_undecided"),           -- nothing about T1 follows
    (tr eve (.request S T2 M2 none), none),                                              -- the delegate requests, for ann
    (tr ann (.ask S T2 cy none), none),
    (tr ann (.reply S T2 E5 none), some "reply_must_name_an_unclaimed_email"),          -- E5 answers T1 already
    (tr eve (.defer S T2 none), some "only_owner_or_person_delegates_can_decide"),
    (tr ann (.defer S T2 (some "after the weekend")), none),                             -- deferred: closed
    (tr cy (.advise S T2 "reply" none), some "triage_must_be_undecided"),
    (tr ann (.ask S T2 dee none), some "triage_must_be_undecided"),
    (tr ann (.defer S T2 none), some "triage_is_decided_once"),
    (tr ann (.request S T3 M3 none), none),
    (tr ann (.ignore S T3 none), none),
    (tr ann (.ignore S T3 none), some "triage_is_decided_once"),
    (tr ann (.request S T4 M4 none), none),
    (tr eve (.consider S T4 "work" (some "a one-time thing that needs a look")), none),
    (tr eve (.work S T4 W1 none), some "only_owner_or_person_delegates_can_decide"),
    (tr ann (.work S T4 W1 (some "a general item on the work stream")), none),
    (tr ann (.work S T4 W2 none), some "triage_is_decided_once"),
    (tr ann (.reply S T4 E2 none), some "triage_is_decided_once"),
    (tr ann (.defer S T4 none), some "triage_is_decided_once"),
    (tr ann (.request S T5 M2 (some "back to m2, deferred as T2")), none),               -- a new triage, a new id
    (core ben (.streamClose S none), some "only_opener_can_close"),
    (core ann (.streamClose S none), none),
    (em ann (.create S E3 none none), some "stream_must_be_open"),                       -- nothing after a close
    (pr ann (.invite S ben none), some "stream_must_be_open") ]

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
  (mailbox.rules.map (·.reason) ++ ["stream_must_exist", "stream_must_be_open"]).all fun r =>
    story.any fun (_, want) => want == some r

#guard everyRuleBites

def allOk : Bool := answersOk && checksOk && everyRuleBites

end EmailTriageAndReply.Examples
