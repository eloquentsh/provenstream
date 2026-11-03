-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT

/-!
# NoRules: an answer, and a theorem about it

What `norules-engine` sends for every request: an acceptance, whatever the request. Nothing here is a `Layer`.
-/

namespace NoRules

def answer : String := "{\"stream_id\":\"\",\"event\":{},\"at\":0,\"accept\":true}"

theorem answer_nonempty : answer.isEmpty = false := by decide

end NoRules
