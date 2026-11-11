-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Post.Examples
import Provenstream.Engine.Step
import PostRevision

/-!
# post-engine

The layered engine serving the post layer (`Post.posts`) on the core, stamped with the revision it is built from
(`PostRevision.lean`, written before the build; not in git).

    post-engine                  serve JSON lines
    post-engine --self-test      the worked examples through the compiled code
    post-engine --revision       {"revision", "repo", "package"}
    post-engine --describe       {"revision", "repo", "package", "protocol", "schema"}
-/

def main (args : List String) : IO UInt32 :=
  Provenstream.Engine.Layered.mainAt Post.posts "post-engine" (pure Post.Examples.allOk) Post.built args
