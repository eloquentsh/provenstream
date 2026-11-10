-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import EmailTriageAndReply.Examples
import Provenstream.Engine.Step
import EmailTriageAndReplyRevision

/-!
# email-triage-and-reply-engine

The layered engine serving the email triage and reply layer (`EmailTriageAndReply.mailbox`) on the core. It is stamped
with the revision it is built from (`EmailTriageAndReplyRevision.lean`, written before the build; not in git).

    email-triage-and-reply-engine                  serve JSON lines
    email-triage-and-reply-engine --self-test      the worked examples through the compiled code
    email-triage-and-reply-engine --revision       {"revision", "repo", "package"}
    email-triage-and-reply-engine --describe       {"revision", "repo", "package", "protocol", "schema"}
-/

def main (args : List String) : IO UInt32 :=
  Provenstream.Engine.Layered.mainAt EmailTriageAndReply.mailbox "email-triage-and-reply-engine"
    (pure EmailTriageAndReply.Examples.allOk) EmailTriageAndReply.built args
