-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Provenstream.Streams

/-!
# The core's rules, run

A happy path, and for every rule a candidate that only that rule refuses ("every rule bites"). `#guard` fails the
build if any answer changes. The cases are data, so the compiled engine runs them too (`core-engine --self-test`).
-/

namespace Provenstream.Examples
open Provenstream

def url := "https://example.org/provenstream/commit/0123456789abcdef0123456789abcdef01234567"
def treeUrl := "https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/tasks"

/-! Ids are canonical lowercase UUIDs; nothing in an id says person or agent, and the core never asks. -/
def ann : Id := "a0000000-0000-4000-8000-000000000001"   -- opens s1
def ben : Id := "b0000000-0000-4000-8000-000000000002"   -- opens s2
def cy : Id := "c0000000-0000-4000-8000-000000000003"
def dee : Id := "d0000000-0000-4000-8000-000000000004"
def eve : Id := "e0000000-0000-4000-8000-000000000005"
def s1 : Id := "50000000-0000-7000-8000-000000000001"
def s2 : Id := "50000000-0000-7000-8000-000000000002"
def s3 : Id := "50000000-0000-7000-8000-000000000003"
def s9 : Id := "50000000-0000-7000-8000-000000000009"

#guard [ann, ben, cy, dee, eve, s1, s2, s3, s9].all validUuid
#guard !validUuid "A0000000-0000-4000-8000-000000000001"
#guard !validUuid "a0000000-0000-4000-8000-00000000001"
#guard !validUuid "a0000000000040008000000000000001"
#guard validMeta "anything at all, é 😀" && !validMeta "a\nb" && !validMeta (String.ofList (List.replicate 4097 'a'))

/-! Revision URLs: a commit names the root package; `/tree/<commit>/<package>` another package. -/
#guard validRevisionUrl url && validRevisionUrl treeUrl
#guard validRevisionUrl "https://git.example.org/repo#0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef"
#guard validRevisionUrl "https://example.org/x/y@0123456789abcdef0123456789abcdef01234567"
#guard validRevisionUrl "https://example.org/x/tree/0123456789abcdef0123456789abcdef01234567/a.b/c_d/e-f/G9"
#guard !validRevisionUrl "https://example.org/x/y/commit/0123456789ABCDEF0123456789abcdef01234567"
#guard !validRevisionUrl "https://example.org/x/y/commit/0123456"
#guard !validRevisionUrl "https://example.org/x/tree/0123456789abcdef0123456789abcdef01234567"
#guard !validRevisionUrl "https://example.org/x/tree/0123456789abcdef0123456789abcdef01234567/"
#guard !validRevisionUrl "https://example.org/x/tree/0123456789abcdef0123456789abcdef01234567/a//b"
#guard !validRevisionUrl "https://example.org/x/tree/0123456789abcdef0123456789abcdef01234567/a/../b"
#guard !validRevisionUrl "https://example.org/x/tree/0123456789abcdef0123456789abcdef01234567/./b"
#guard !validRevisionUrl "https://example.org/x/tree/0123456789abcdef0123456789abcdef01234567/a/b~"
#guard !validRevisionUrl "https://example.org/x/tree/0123456/a"
#guard !validRevisionUrl "https://example.org/tree/0123456789abcdef0123456789abcdef01234567/a"

/-- Ann opens `s1`, Ben opens `s2`. -/
def happy : Log :=
  [ .streamOpened ann s1 url none,
    .streamOpened ben s2 treeUrl (some "the second stream") ]

/-- Ann, its opener, closes `s1`. -/
def closed : Log := happy ++ [.streamClosed ann s1 (some "done")]

#guard check happy
#guard check closed

/-- Every example: the log, the candidate, and the answer. -/
def cases : List (Log × Event × Option String) :=
  [ (happy, .streamOpened dee s1 url none, some "stream_id_must_be_new"),
    (closed, .streamOpened ann s1 url none, some "stream_id_must_be_new"),            -- a closed stream's id too
    (happy, .streamOpened dee s3 "https://example.org/x/y/commit/0123456" none, some "revision_url_must_name_a_commit"),
    (happy, .streamClosed ann s9 none, some "stream_must_exist"),
    (closed, .streamClosed ann s1 none, some "stream_must_be_open"),                  -- closed once, for good
    (closed, .streamClosed ben s1 none, some "stream_must_be_open"),
    (happy, .streamClosed ben s1 none, some "only_opener_can_close"),                 -- another stream's opener
    (happy, .streamClosed dee s1 none, some "only_opener_can_close"),                 -- anyone else
    (happy, .streamClosed ann s2 none, some "only_opener_can_close"),                 -- openers are per stream
    -- acceptances
    (happy, .streamClosed ann s1 none, none),                                          -- the opener closes
    (happy, .streamClosed ben s2 (some "x"), none),
    (happy, .streamOpened cy s3 url none, none),                                       -- anyone opens a stream
    (closed, .streamClosed ben s2 none, none),                                         -- other streams carry on
    (closed, .streamOpened ann s3 treeUrl none, none) ]

#guard cases.all fun c => rejection c.1 c.2.1 == c.2.2

/-- The fast path answers every case the same (`fold_sound`, run on the examples). -/
def fastPathAgrees : Bool := cases.all fun c => rejectionS (fold c.2.1.stream c.1) c.2.1 == c.2.2

#guard fastPathAgrees

-- Every rule's reason appears among the cases: every rule bites.
#guard rules.all fun r => cases.any fun c => c.2.2 == some r.reason

#guard Past.opener happy s1 == some ann && Past.opener happy s2 == some ben && Past.opener happy s3 == none
#guard Past.opener closed s1 == some ann
#guard (Past.view happy s1).admits dee == none && (Past.view happy s1).admits ann == none   -- any actor is admitted
#guard (Past.view closed s1).admits ann == some "stream_must_be_open"
#guard (Past.view happy s9).admits ann == some "stream_must_exist"

-- The description's rule names, per command, in order.
#guard rulesOf "stream.open" == ["stream_id_must_be_new", "revision_url_must_name_a_commit"]
#guard rulesOf "stream.close" == ["stream_must_exist", "stream_must_be_open", "only_opener_can_close"]

def validLogs : List Log :=
  [happy, closed, closed ++ [.streamClosed ben s2 none],
   closed ++ [.streamOpened cy s3 url none, .streamClosed cy s3 none]]

#guard validLogs.all check

/-! ## Commands, in order, produce the events -/

def happyCommands : List Request :=
  [ (ann, .streamOpen url none, [s1]),
    (ben, .streamOpen treeUrl (some "the second stream"), [s2]),
    (ann, .streamClose s1 (some "done"), []) ]

/-- Refusals before any rule and by the rules; a refused request leaves the log as it was. -/
def mixedCommands : List Request :=
  happyCommands ++
  [ (cy, .streamOpen url none, [s1]),
    (ann, .streamClose s2 none, ["x"]),
    (ann, .streamOpen url none, []),
    (ann, .streamClose s1 none, []),
    (ann, .streamClose s2 none, []),
    (ben, .streamClose s2 none, []) ]

def commandsProduceEvents : Bool :=
  run happyCommands == (closed, closed.map Response.accepted) &&
  run mixedCommands == (closed ++ [.streamClosed ben s2 none],
    closed.map Response.accepted ++
      [.rejected "stream_id_must_be_new", .rejected "fresh_ids_must_match_the_command",
       .rejected "fresh_ids_must_match_the_command", .rejected "stream_must_be_open",
       .rejected "only_opener_can_close", .accepted (.streamClosed ben s2 none)])

#guard commandsProduceEvents

end Provenstream.Examples
