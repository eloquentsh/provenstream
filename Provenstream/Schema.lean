-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Provenstream.Json
import Provenstream.Command

/-!
# Command schemas: how a command is on the wire, and how an engine describes its commands

Every command, the core's and every layer's, is on the wire as an object: its name under `command`, then its fields,
each of a `Kind`. Its event is the event's own name (past tense) under `event`, the `actor_id`, the ids it mints, then
the same fields. A `CmdSchema` says all of that for one command, and also which field names the stream and, in a
sentence, who may send it (`who`). The engine decodes every command with the schema list it serves (`objFromJ`), and it
describes itself by printing the same list (`schemaJ`), with the names of the rules that judge each command: what a
host is told is, by construction, what the engine decodes with.

The core's two commands are written here, with their schema (`coreSchema`) and their values (`Command.toVals`,
`Command.ofVals`).
-/

namespace Provenstream
open Provenstream.Wire

/-! ## Kinds of field, and values -/

/-- The kind of a command's field: a canonical UUID; an optional canonical UUID (`uuid?`: a UUID, or absent or `null`
for none); a text without U+0000 that `wf` accepts (advertised under `name`); an optional such text (advertised under
`name?`: the text, or absent or `null` for none); the optional opaque `meta`; or a reference to an earlier event of the
same stream, by its 0-based position in the stream (`ref`: a natural number, or absent or `null` for none). The
mechanism checks every reference of every layer event before the layer's rules (`ref_must_name_an_earlier_event`,
`Layer.lean`). -/
inductive Kind where
  | uuid
  | uuidOpt
  | text (name : String) (wf : String → Bool)
  | textOpt (name : String) (wf : String → Bool)
  | metaOpt
  | ref

/-- A field's value. -/
inductive Val where
  | s (x : String)
  | m (x : Meta)
  | r (x : Option Nat)
  | uo (x : Option String)
  deriving DecidableEq

/-- How a kind is advertised. -/
def Kind.name : Kind → String
  | .uuid => "uuid"
  | .uuidOpt => "uuid?"
  | .text n _ => n
  | .textOpt n _ => n ++ "?"
  | .metaOpt => "meta"
  | .ref => "ref"

def Kind.isUuid : Kind → Bool
  | .uuid => true
  | _ => false

def Kind.isRef : Kind → Bool
  | .ref => true
  | _ => false

/-- A well-formed `meta`: absent, or at most 4096 bytes without a control character (`validMeta`). -/
def wfMeta : Meta → Bool
  | none => true
  | some s => noNul s && validMeta s

/-- The value has the field's kind and form. -/
def Kind.wf : Kind → Val → Bool
  | .uuid, .s x => validUuid x
  | .uuidOpt, .uo none => true
  | .uuidOpt, .uo (some x) => validUuid x
  | .text _ wf, .s x => noNul x && wf x
  | .textOpt _ _, .uo none => true
  | .textOpt _ wf, .uo (some x) => noNul x && wf x
  | .metaOpt, .m o => wfMeta o
  | .ref, .r _ => true
  | _, _ => false

/-- One value per field, each of the field's kind and form. -/
def valsWf : List (String × Kind) → List Val → Bool
  | [], [] => true
  | (_, k) :: fs, v :: vs => k.wf v && valsWf fs vs
  | _, _ => false

def metaJ : Meta → J
  | none => .null
  | some s => .str s

def Val.toJ : Val → J
  | .s x => .str x
  | .m o => metaJ o
  | .r none => .null
  | .r (some n) => .num n
  | .uo none => .null
  | .uo (some x) => .str x

/-- A field of the object `kvs`, read by its kind. -/
def Kind.fromJ (what : String) (kvs : Fields) : String × Kind → Except String Val
  | (k, .metaOpt) => match get? kvs k with
    | none | some .null => .ok (.m none)
    | some (.str s) => .ok (.m (some s))
    | some _ => .error s!"{what}.{k}: expected a string or null"
  | (k, .uuidOpt) => match get? kvs k with
    | none | some .null => .ok (.uo none)
    | some (.str s) => .ok (.uo (some s))
    | some _ => .error s!"{what}.{k}: expected a string (a canonical UUID) or null"
  | (k, .textOpt n _) => match get? kvs k with
    | none | some .null => .ok (.uo none)
    | some (.str s) => .ok (.uo (some s))
    | some _ => .error s!"{what}.{k}: expected a string ({n}) or null"
  | (k, .ref) => match get? kvs k with
    | none | some .null => .ok (.r none)
    | some (.num n) => .ok (.r (some n))
    | some _ => .error s!"{what}.{k}: expected a natural number (a position in the stream) or null"
  | (k, _) => .s <$> str what kvs k

/-- The references among a command's values: the positions its `ref` fields name. -/
def refsIn : List (String × Kind) → List Val → List Nat
  | (_, .ref) :: fs, .r (some n) :: vs => n :: refsIn fs vs
  | _ :: fs, _ :: vs => refsIn fs vs
  | _, _ => []

def valsToJ : List (String × Kind) → List Val → Fields
  | (k, _) :: fs, v :: vs => (k, v.toJ) :: valsToJ fs vs
  | _, _ => []

/-! ## One command's schema -/

/-- One command on the wire: its name, the name of its event (past tense), its fields in order, the event fields minted
from the request's fresh ids (in order; their number is the number of fresh ids the command takes), the field (a
command field or a minted one) that names the stream, and a sentence saying who may send it (for the description
only; the rules decide). -/
structure CmdSchema where
  name : String
  event : String
  fields : List (String × Kind)
  minted : List String := []
  stream : String := "stream_id"
  who : Option String := none

/-- The fields of the command's event: the actor, the minted ids, the command's fields. -/
def CmdSchema.evFields (sc : CmdSchema) : List (String × Kind) :=
  ("actor_id", .uuid) :: sc.minted.map (·, .uuid) ++ sc.fields

def CmdSchema.lookup (sc : CmdSchema) (f : String) : Option Kind := (sc.fields.find? (·.1 == f)).map (·.2)

/-- A schema entry a service may use: its command's keys and its event's keys are distinct; the stream field is minted
or a UUID field. -/
def CmdSchema.ok (sc : CmdSchema) : Bool :=
  decide (("command" :: sc.fields.map (·.1)).Nodup) && decide (("event" :: sc.evFields.map (·.1)).Nodup) &&
  (sc.minted.contains sc.stream || ((sc.lookup sc.stream).map Kind.isUuid).getD false)

/-- A schema list a service may use: command names distinct, event names distinct, every entry `ok`. -/
def schemaOk (schema : List CmdSchema) : Bool :=
  decide (schema.map (·.name)).Nodup && decide (schema.map (·.event)).Nodup && schema.all CmdSchema.ok

/-- In a schema whose `key`s are distinct, looking an entry up by its own key finds it. -/
theorem find_key_of_mem {schema : List CmdSchema} {key : CmdSchema → String} (hnd : (schema.map key).Nodup)
    {sc : CmdSchema} (hm : sc ∈ schema) : schema.find? (key · == key sc) = some sc := by
  induction schema with
  | nil => cases hm
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hm with rfl | hm
    · simp
    · have hne : key x ≠ key sc := fun h => hnd.1 (h ▸ List.mem_map_of_mem hm)
      simp [hne, ih hnd.2 hm]

/-! ## Objects on the wire, by schema -/

/-- An object: its name under `what` (`command` or `event`), then its fields. -/
def objToJ (what n : String) (fs : List (String × Kind)) (vs : List Val) : J :=
  .obj ((what, .str n) :: valsToJ fs vs)

/-- Read an object of `schema`: its name under `what` (an entry's `key`: its command's name, or its event's), then the
`extra` fields of its entry and the entry's fields, in order. -/
def objFromJ (schema : List CmdSchema) (what : String) (key : CmdSchema → String)
    (extra : CmdSchema → List (String × Kind)) (j : J) : Except String (CmdSchema × List Val) := do
  let kvs ← fields what j
  let n ← str what kvs what
  let some sc := schema.find? (key · == n) | throw s!"{what}: unknown {what} {n}"
  onlyKeys what kvs (what :: (extra sc ++ sc.fields).map (·.1))
  return (sc, ← (extra sc ++ sc.fields).mapM (Kind.fromJ what kvs))

theorem valsWf_keys {fs : List (String × Kind)} {vs : List Val} (h : valsWf fs vs = true) :
    (valsToJ fs vs).map (·.1) = fs.map (·.1) := by
  induction fs generalizing vs with
  | nil => rfl
  | cons f fs ih => cases vs <;> simp_all [valsWf, valsToJ]

theorem valsWf_length {fs : List (String × Kind)} {vs : List Val} (h : valsWf fs vs = true) :
    vs.length = fs.length := by
  induction fs generalizing vs with
  | nil => cases vs <;> simp_all [valsWf]
  | cons f fs ih => cases vs <;> simp_all [valsWf]

theorem valsWf_append {fs gs : List (String × Kind)} {vs ws : List Val} (h1 : valsWf fs vs = true)
    (h2 : valsWf gs ws = true) : valsWf (fs ++ gs) (vs ++ ws) = true := by
  induction fs generalizing vs with
  | nil => cases vs <;> simp_all [valsWf]
  | cons f fs ih => cases vs <;> simp_all [valsWf]

theorem mapM_fromJ {what : String} {kvs : Fields} {fs : List (String × Kind)} {vs : List Val}
    (hf : valsWf fs vs = true) (hk : ∀ kv ∈ valsToJ fs vs, get? kvs kv.1 = some kv.2) :
    fs.mapM (Kind.fromJ what kvs) = .ok vs := by
  induction fs generalizing vs with
  | nil => cases vs <;> simp_all [valsWf, pure, Except.pure]
  | cons f fs ih => cases vs with
    | nil => simp [valsWf] at hf
    | cons v vs =>
      obtain ⟨k, kd⟩ := f
      simp only [valsWf, valsToJ, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp] at hf hk
      have hrest := ih hf.2 hk.2
      cases kd <;> cases v <;> (try rename_i o; try cases o) <;> simp_all [Kind.wf, Kind.fromJ, List.mapM_cons, str,
        Val.toJ, metaJ, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

theorem objFromJ_toJ {schema : List CmdSchema} {what n : String} {key : CmdSchema → String}
    {extra : CmdSchema → List (String × Kind)}
    {sc : CmdSchema} {vs : List Val} (hsc : schema.find? (key · == n) = some sc)
    (hwf : valsWf (extra sc ++ sc.fields) vs = true) (hnd : (what :: (extra sc ++ sc.fields).map (·.1)).Nodup) :
    objFromJ schema what key extra (objToJ what n (extra sc ++ sc.fields) vs) = .ok (sc, vs) := by
  have hkeys : ((what, J.str n) :: valsToJ (extra sc ++ sc.fields) vs).map (·.1) =
      what :: (extra sc ++ sc.fields).map (·.1) := by
    simp [valsWf_keys hwf]
  have hfind : List.find? (fun kv => !(what :: (extra sc ++ sc.fields).map (·.1)).contains kv.1)
      ((what, J.str n) :: valsToJ (extra sc ++ sc.fields) vs) = none :=
    List.find?_eq_none.mpr fun kv h => by
      have hc : (what :: (extra sc ++ sc.fields).map (·.1)).contains kv.1 = true :=
        List.elem_iff.mpr (hkeys ▸ List.mem_map_of_mem h)
      rw [hc]; decide
  simp only [objFromJ, objToJ, fields, str, get?, List.find?_cons, beq_self_eq_true, Option.map_some, hsc, onlyKeys,
    hfind, bind, Except.bind, pure, Except.pure,
    mapM_fromJ hwf fun kv h => get?_of_mem (hkeys ▸ hnd) (List.mem_cons_of_mem _ h)]

/-- **What decodes is the schema's**: an object `objFromJ` accepts names an entry of the schema under `what`, and every
key it has is that entry's (`what`, the extra fields, the entry's fields). -/
theorem objFromJ_keys {schema : List CmdSchema} {what : String} {key : CmdSchema → String}
    {extra : CmdSchema → List (String × Kind)} {j : J}
    {sc : CmdSchema} {vs : List Val} (h : objFromJ schema what key extra j = .ok (sc, vs)) :
    sc ∈ schema ∧ ∃ kvs, j = .obj kvs ∧ get? kvs what = some (.str (key sc)) ∧
      ∀ kv ∈ kvs, kv.1 ∈ what :: (extra sc ++ sc.fields).map (·.1) := by
  unfold objFromJ at h
  simp only [bind, Except.bind] at h
  cases j with
  | obj kvs =>
    simp only [fields] at h
    cases hs : str what kvs what with
    | error e => rw [hs] at h; cases h
    | ok n =>
      rw [hs] at h
      simp only at h
      cases hf : schema.find? (key · == n) with
      | none => rw [hf] at h; cases h
      | some sc' =>
        rw [hf] at h
        simp only at h
        cases ho : onlyKeys what kvs (what :: (extra sc' ++ sc'.fields).map (·.1)) with
        | error e => rw [ho] at h; cases h
        | ok u =>
          rw [ho] at h
          simp only at h
          cases hm : (extra sc' ++ sc'.fields).mapM (Kind.fromJ what kvs) with
          | error e => rw [hm] at h; cases h
          | ok vs' =>
            rw [hm] at h
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hname : key sc' = n := by simpa using List.find?_some hf
            refine ⟨List.mem_of_find?_eq_some hf, kvs, rfl, ?_, ?_⟩
            · unfold str at hs
              split at hs
              · rename_i s' hg; cases hs; rw [hname]; exact hg
              · cases hs
              · cases hs
            · intro kv hkv
              unfold onlyKeys at ho
              split at ho
              · cases ho
              · rename_i hnone
                have h3 := List.find?_eq_none.mp hnone kv hkv
                cases hc : (what :: (extra sc' ++ sc'.fields).map (·.1)).contains kv.1
                · rw [hc] at h3; exact absurd rfl h3
                · exact List.elem_iff.mp hc
  | _ => simp [fields] at h

/-! ## How an engine describes its commands -/

/-- The keys of the command's event, as the description lists them: `event`, the stream field, `actor_id`, `meta` (when
the command has one), then the rest in wire order. -/
def CmdSchema.eventKeys (sc : CmdSchema) : List String :=
  let all := sc.evFields.map (·.1)
  ["event", sc.stream, "actor_id"] ++ (if all.contains "meta" then ["meta"] else []) ++
    all.filter fun k => k != sc.stream && k != "actor_id" && k != "meta"

/-- One command, described: its params and their kinds, the ids the host mints (`fresh`, `minted`), the stream field,
who may send it (when the schema says), its event (name and keys), and the rules that judge it, in order. -/
def CmdSchema.toJ (rules : String → List String) (sc : CmdSchema) : J :=
  .obj ([("name", .str sc.name),
        ("params", .arr (sc.fields.map fun (f, k) => .obj [("name", .str f), ("kind", .str k.name)])),
        ("fresh", .num sc.minted.length),
        ("minted", .arr (sc.minted.map .str)),
        ("stream_id", .str sc.stream)] ++
        (match sc.who with | some w => [("who", .str w)] | none => []) ++
        [("event", .obj [("name", .str sc.event), ("fields", .arr (sc.eventKeys.map .str))]),
         ("rules", .arr ((rules sc.name).map .str))])

/-- **The description an engine gives of its commands**: the schema list it decodes with, printed, each command with
the names of the rules that judge it (`rules`, the service's `rulesOf`). -/
def schemaJ (schema : List CmdSchema) (rules : String → List String) : J :=
  .obj [("commands", .arr (schema.map (CmdSchema.toJ rules)))]

/-! ## The core's commands -/

/-- Any text without U+0000 (a revision URL: the rules judge its form, `revision_url_must_name_a_commit`). -/
def textKind : Kind := .text "text" fun _ => true

/-- The core's two commands. `stream.open` takes one fresh id, the stream's (`stream_id`). -/
def coreSchema : List CmdSchema :=
  [{ name := "stream.open", event := "stream.opened", fields := [("proof_revision_url", textKind), ("meta", .metaOpt)],
     minted := ["stream_id"], who := some "anyone signed in; the caller becomes the stream's opener" },
   { name := "stream.close", event := "stream.closed", fields := [("stream_id", .uuid), ("meta", .metaOpt)],
     who := some "the stream's opener" }]

def coreNames : List String := coreSchema.map (·.name)

theorem coreSchema_ok : schemaOk coreSchema = true := by decide

def Command.toVals : Command → String × List Val
  | .streamOpen u m => ("stream.open", [.s u, .m m])
  | .streamClose t m => ("stream.close", [.s t, .m m])

def Command.ofVals : String → List Val → Option Command
  | "stream.open", [.s u, .m m] => some (.streamOpen u m)
  | "stream.close", [.s t, .m m] => some (.streamClose t m)
  | _, _ => none

theorem Command.ofVals_toVals (c : Command) : Command.ofVals c.toVals.1 c.toVals.2 = some c := by
  cases c <;> rfl

/-- The schema entry of a core command. -/
def Command.schema : Command → CmdSchema
  | .streamOpen .. => coreSchema[0]
  | .streamClose .. => coreSchema[1]

theorem Command.find_schema (c : Command) : coreSchema.find? (·.name == c.toVals.1) = some c.schema := by
  cases c <;> rfl

theorem Command.find_event (c : Command) : coreSchema.find? (·.event == c.schema.event) = some c.schema := by
  cases c <;> rfl

theorem Command.schema_mem (c : Command) : c.schema ∈ coreSchema := by
  cases c <;> simp [Command.schema, coreSchema]

theorem Command.name_schema (c : Command) : c.schema.name = c.toVals.1 := by
  cases c <;> rfl

/-- The fresh ids a core command takes are its schema's minted fields, one each. -/
theorem toRequest_fresh_length (e : Event) : (toRequest e).2.2.length = (toRequest e).2.1.schema.minted.length := by
  cases e <;> rfl

end Provenstream
