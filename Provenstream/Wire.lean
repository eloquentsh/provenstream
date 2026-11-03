-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Provenstream.Schema

/-!
# The core's wire forms, and their round trips

Commands, requests and events of the core, decoded and encoded through the core's schema (`coreSchema`, `objFromJ`,
`objToJ`), so the core's own description (`schemaJ coreSchema`) is what it decodes with. A request carries its actor
as `actor_id`; an event carries its name (`stream.opened`, `stream.closed`), `actor_id`, the minted `stream_id` and its
command's fields. Decoding inverts encoding on
well-formed values (`requestFromJ_toJ`, `eventFromJ_toJ`), and whatever decodes is well formed (`requestFromJ_wf`,
`eventFromJ_wf`).
-/

namespace Provenstream.Wire
open Provenstream

/-! ## Forms -/

/-- A well-formed command: its values fit its schema's fields, in kind and form. -/
def commandWf (cmd : Command) : Bool := valsWf cmd.schema.fields cmd.toVals.2

def requestWf : Request → Bool
  | (c, cmd, f) => validUuid c && commandWf cmd && f.all validUuid

/-- A well-formed event: the same forms, through the request it came from. -/
def eventWf (e : Event) : Bool := requestWf (toRequest e)

/-! ## Encoding -/

def commandToJ (cmd : Command) : J := objToJ "command" cmd.toVals.1 cmd.schema.fields cmd.toVals.2

def requestToJ : Request → J
  | (c, cmd, f) => .obj [("actor_id", .str c), ("command", commandToJ cmd), ("fresh", .arr (f.map .str))]

/-- An event: its name, its actor, the ids it minted, its command's fields. -/
def eventToJ (e : Event) : J :=
  let (c, cmd, f) := toRequest e
  objToJ "event" cmd.schema.event cmd.schema.evFields (.s c :: (f.map .s ++ cmd.toVals.2))

/-! ## Decoding -/

def commandFromJ (j : J) : Except String Command := do
  let (sc, vs) ← objFromJ coreSchema "command" (·.name) (fun _ => []) j
  let some cmd := Command.ofVals sc.name vs | throw s!"command: {sc.name}: unexpected fields"
  checked "command" commandWf cmd

/-- The request's `actor_id`: a string (its form is checked with the whole request). -/
def actorFromJ : J → Except String Id
  | .str a => .ok a
  | _ => .error "request.actor_id: expected a string"

def freshFromJ : J → Except String Fresh := strs "fresh"

def requestFromJ (j : J) : Except String Request := do
  let (c, cmd, f) ← requestParts j
  checked "request" requestWf (← actorFromJ c, ← commandFromJ cmd, ← freshFromJ f)

/-- The strings of a list of values, if every one is a string. -/
def strsOf : List Val → Option (List String)
  | [] => some []
  | .s x :: vs => (strsOf vs).map (x :: ·)
  | _ => none

/-- The extra fields of a core event before its command's: the actor and the minted ids. -/
def evExtra (sc : CmdSchema) : List (String × Kind) := ("actor_id", .uuid) :: sc.minted.map (·, .uuid)

def eventFromJ (j : J) : Except String Event := do
  let (sc, vs) ← objFromJ coreSchema "event" (·.event) evExtra j
  let .s a :: rest := vs | throw s!"event: {sc.name}: unexpected fields"
  let some fr := strsOf (rest.take sc.minted.length) | throw s!"event: {sc.name}: unexpected fields"
  let some cmd := Command.ofVals sc.name (rest.drop sc.minted.length) | throw s!"event: {sc.name}: unexpected fields"
  match toEvent a cmd fr with
  | .ok e => checked "event" eventWf e
  | .error x => throw s!"event: {x}"

/-! ## Decoding inverts encoding -/

theorem CmdSchema.ok_of_mem {schema : List CmdSchema} {sc : CmdSchema} (h : schemaOk schema = true)
    (hm : sc ∈ schema) : sc.ok = true := by
  simp only [schemaOk, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 sc hm

theorem CmdSchema.cmd_nodup {sc : CmdSchema} (h : sc.ok = true) : ("command" :: sc.fields.map (·.1)).Nodup := by
  simp only [CmdSchema.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem CmdSchema.ev_nodup {sc : CmdSchema} (h : sc.ok = true) : ("event" :: sc.evFields.map (·.1)).Nodup := by
  simp only [CmdSchema.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

/-- A well-formed command survives encoding and decoding unchanged. -/
theorem commandFromJ_toJ (cmd : Command) (h : commandWf cmd = true) : commandFromJ (commandToJ cmd) = .ok cmd := by
  have hok := CmdSchema.ok_of_mem coreSchema_ok (Command.schema_mem cmd)
  have := objFromJ_toJ (what := "command") (key := (·.name)) (extra := fun _ => []) (vs := cmd.toVals.2)
    (Command.find_schema cmd)
    (by simpa [commandWf] using h) (by simpa using CmdSchema.cmd_nodup hok)
  simp only [List.nil_append] at this
  simp only [commandFromJ, commandToJ, this, Command.name_schema, Command.ofVals_toVals, checked_ok h, bind,
    Except.bind]

/-- A well-formed request survives encoding and decoding unchanged. -/
theorem requestFromJ_toJ (r : Request) (h : requestWf r = true) : requestFromJ (requestToJ r) = .ok r := by
  obtain ⟨c, cmd, f⟩ := r
  have hcmd : commandWf cmd = true := by simp_all [requestWf]
  have hr := checked_ok (w := "request") h
  simp_all [requestFromJ, requestToJ, requestParts_toJ, actorFromJ, commandFromJ_toJ cmd hcmd, freshFromJ, strs_toJ,
    bind, Except.bind]

theorem strsOf_map (f : List String) : strsOf (f.map .s) = some f := by
  induction f with
  | nil => rfl
  | cons x xs ih => simp [strsOf, ih]

theorem valsWf_uuids {ms : List String} {f : List String} (hl : f.length = ms.length) (hu : f.all validUuid = true) :
    valsWf (ms.map (·, .uuid)) (f.map .s) = true := by
  induction ms generalizing f with
  | nil => cases f <;> simp_all [valsWf]
  | cons m ms ih => cases f <;> simp_all [valsWf, Kind.wf]

/-- A well-formed event survives encoding and decoding unchanged. -/
theorem eventFromJ_toJ (e : Event) (h : eventWf e = true) : eventFromJ (eventToJ e) = .ok e := by
  have hr : requestWf (toRequest e) = true := h
  generalize hq : toRequest e = q at hr
  obtain ⟨c, cmd, f⟩ := q
  have hfl : f.length = cmd.schema.minted.length := by
    have := toRequest_fresh_length e; rw [hq] at this; exact this
  simp only [requestWf, Bool.and_eq_true] at hr
  obtain ⟨⟨hc, hcmd⟩, hf⟩ := hr
  have hok := CmdSchema.ok_of_mem coreSchema_ok (Command.schema_mem cmd)
  have hwf : valsWf (evExtra cmd.schema ++ cmd.schema.fields) (.s c :: (f.map .s ++ cmd.toVals.2)) = true := by
    simp only [evExtra, List.cons_append, valsWf, Kind.wf, hc, Bool.true_and]
    exact valsWf_append (valsWf_uuids hfl hf) hcmd
  have := objFromJ_toJ (what := "event") (key := (·.event)) (extra := evExtra) (Command.find_event cmd) hwf
    (by simpa [evExtra, CmdSchema.evFields] using CmdSchema.ev_nodup hok)
  have hev : eventToJ e = objToJ "event" cmd.schema.event (evExtra cmd.schema ++ cmd.schema.fields)
      (.s c :: (f.map .s ++ cmd.toVals.2)) := by
    simp only [eventToJ, hq, evExtra, CmdSchema.evFields, List.cons_append]
  have hlen : (f.map Val.s).length = cmd.schema.minted.length := by simp [hfl]
  have hte : toEvent c cmd f = .ok e := toEvent_ok_iff.mpr hq
  rw [hev]
  simp only [eventFromJ, this, bind, Except.bind, ← hlen, List.take_left, List.drop_left, strsOf_map,
    Command.name_schema, Command.ofVals_toVals, hte, checked_ok h]

/-! ## Whatever decodes is well formed -/

theorem commandFromJ_wf {j : J} {cmd : Command} (h : commandFromJ j = .ok cmd) : commandWf cmd = true := by
  unfold commandFromJ at h
  simp only [bind, Except.bind] at h
  repeat (first | (split at h <;> try contradiction) | exact checked_wf h)

theorem requestFromJ_wf {j : J} {r : Request} (h : requestFromJ j = .ok r) : requestWf r = true := by
  unfold requestFromJ at h
  simp only [bind, Except.bind] at h
  repeat (first | (split at h <;> try contradiction) | exact checked_wf h)

theorem eventFromJ_wf {j : J} {e : Event} (h : eventFromJ j = .ok e) : eventWf e = true := by
  unfold eventFromJ at h
  simp only [bind, Except.bind] at h
  repeat (first | (split at h <;> try contradiction) | exact checked_wf h)

theorem toEvent_wf {c : Id} {cmd : Command} {f : Fresh} {e : Event} (hr : requestWf (c, cmd, f) = true)
    (h : toEvent c cmd f = .ok e) : eventWf e = true := by
  rw [eventWf, toRequest_toEvent h]; exact hr

/-! ## The description is what decodes -/

theorem commandFromJ_keys {j : J} {cmd : Command} (h : commandFromJ j = .ok cmd) :
    ∃ sc ∈ coreSchema, ∃ kvs, j = .obj kvs ∧ get? kvs "command" = some (.str sc.name) ∧
      ∀ kv ∈ kvs, kv.1 ∈ "command" :: sc.fields.map (·.1) := by
  unfold commandFromJ at h
  simp only [bind, Except.bind] at h
  cases ho : objFromJ coreSchema "command" (·.name) (fun _ => []) j with
  | error e => rw [ho] at h; cases h
  | ok p =>
    obtain ⟨sc, vs⟩ := p
    obtain ⟨hm, kvs, rfl, hn, hk⟩ := objFromJ_keys ho
    exact ⟨sc, hm, kvs, rfl, hn, by simpa using hk⟩

/-- **What the core decodes is described** (`coreSchema`). -/
theorem requestFromJ_schema {j : J} {r : Request} (h : requestFromJ j = .ok r) :
    ∃ sc ∈ coreSchema, ∃ kvs, cmdObj j = some kvs ∧ get? kvs "command" = some (.str sc.name) ∧
      ∀ kv ∈ kvs, kv.1 ∈ "command" :: sc.fields.map (·.1) := by
  unfold requestFromJ at h
  simp only [bind, Except.bind] at h
  cases hp : requestParts j with
  | error e => rw [hp] at h; cases h
  | ok p =>
    obtain ⟨c, cj, f⟩ := p
    rw [hp] at h
    dsimp only at h
    obtain ⟨kvs, rfl, hg⟩ := requestParts_ok hp
    cases hc : actorFromJ c with
    | error e => rw [hc] at h; cases h
    | ok c' =>
      rw [hc] at h
      cases hm : commandFromJ cj with
      | error e => rw [hm] at h; cases h
      | ok cmd =>
        obtain ⟨sc, hsc, ckvs, rfl, hn, hk⟩ := commandFromJ_keys hm
        exact ⟨sc, hsc, ckvs, by simp [cmdObj, hg], hn, hk⟩

/-- **What the core describes is decoded**: a well-formed request's command is on the wire as its schema entry, with
exactly that entry's keys, in order. -/
theorem requestToJ_schema (r : Request) (h : requestWf r = true) :
    ∃ sc ∈ coreSchema, ∃ kvs, cmdObj (requestToJ r) = some kvs ∧ get? kvs "command" = some (.str sc.name) ∧
      kvs.map (·.1) = "command" :: sc.fields.map (·.1) := by
  obtain ⟨c, cmd, f⟩ := r
  have hcmd : commandWf cmd = true := by simp_all [requestWf]
  refine ⟨cmd.schema, cmd.schema_mem, ("command", .str cmd.toVals.1) :: valsToJ cmd.schema.fields cmd.toVals.2,
    ?_, ?_, ?_⟩
  · simp [cmdObj, requestToJ, get?, List.find?, commandToJ, objToJ]
  · simp [get?, Command.name_schema]
  · simp [valsWf_keys hcmd]

end Provenstream.Wire
