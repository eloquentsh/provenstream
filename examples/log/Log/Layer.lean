-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Provenstream.Interface

/-!
# Log: the smallest layer

`log.append {stream_id, text, meta?}` → `log.appended {text}`: the stream's opener appends a text. One command, one
rule (`only_opener_can_append`, reading the core's `v.opener`), and nothing remembered. A stream of this proof is a
notebook only its opener writes in.
-/

namespace Log
open Provenstream Provenstream.Layer

inductive LogCommand where
  | append (stream : Id) (text : String) («meta» : Meta)
  deriving DecidableEq

inductive LogEvent where
  | appended (actor stream : Id) (text : String) («meta» : Meta)
  deriving DecidableEq

abbrev log : Layer where
  Cmd := LogCommand
  Ev := LogEvent
  toRequest | .appended a t x m => (a, .append t x m)
  ofRequest | (a, .append t x m) => .appended a t x m
  stream | .append t .. => t
  schema := [{ name := "log.append", event := "log.appended", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("text", textKind), ("meta", .metaOpt)] }]
  toVals | .append t x m => ("log.append", [.s t, .s x, .m m])
  ofVals | "log.append", [.s t, .s x, .m m] => some (.append t x m) | _, _ => none
  memory := foldMemory () (fun _ _ => ()) (fun _ => .null) (fun _ => .ok ()) (fun _ => rfl)
  rules := [⟨"only_opener_can_append", ["log.append"], fun v _ e => match e with | .appended a .. => v.opener == some a⟩]

end Log
