-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Provenstream.Streams

/-!
# Layers: refinement of a base

A `Layer B` is what an extension writes on a base `B` (the core, `coreBase`, by default; or a layer with everything
below it, `Layer.toBase`), in four parts:
- its commands and events (`Layer.Commands`): the two types, the event's request and back (proved by
  `layer_bijection`), the stream a command is on, and each command's wire form as a schema entry (`CmdSchema`: the
  command's name, its event's name, its fields, who may send it) with the command as that entry's values and back;
- what its rules remember of the stream's own layer events (`Memory`), with its fast path;
- its rules (`Layer.Rule`), tried in order, each reading the base's `View` of the event's stream and the memory, and
  each naming the commands it judges (for the description);
- its guards (rules over the base's events, default none), tried after the base's own rules on the base's events.

The combined service, `Layer.service L` (the base's events and the layer's side by side), is built and proved here once
for every layer, so `Service.lean` gives it everything the base has. In the terms of refinement:

- **forward simulation by projection**: the base's events of a valid combined log form a valid log of the base
  (`ValidX.base`): every behaviour of the layer, projected, is a behaviour of the base;
- **stuttering**: a layer's own events project to no base event (`bases_snoc_inr`); the base is asked of each only what
  it asks of every layer event (`Base.admits`: at the core, the stream is open and not closed; any actor), tried before
  any rule of the layer (`ValidX.admitted`);
- **guards only refuse more**: on a base event, the base's rules are tried first and the layer's guards after
  (`rejectionX`), so a base refusal stands in every layer (`ValidX.base_refusal_stands`), and a guard can only add one;
- **towers compose transitively**: `L.toBase` is a base, so a layer sits on a layer, and `h.base.base` takes a valid log
  two levels down; the admission asked of the top layer's events is the bottom base's (`toBase_admits`).

A layer that names a base command, or tries to accept what the base refuses, cannot: its commands' names are disjoint
from the base's (`names_ok`), and nothing in a `Layer` is consulted before the base's rules on a base event. What this
does **not** give: anything about the layer's own events beyond its own rules and the base's admission.

**References.** A field of kind `ref` names an earlier event of the same stream by its 0-based position. Before any
rule of the layer, the mechanism refuses a layer event whose references are not below the stream's length
(`ref_must_name_an_earlier_event`); a layer's reference rules (`refRules`) may then read what the layer's `tag` says of each target.
Every reference of a valid log points to an earlier event of the same stream (`ValidX.ref_earlier`), the event at a
position never changes (`ref_target_fixed`), and the target is an accepted event (`ValidX.ref_target_valid`). Positions
are those of the stream of the service that judges the layer; in a tower, a lower layer's references index the stream
as that layer sees it (its events and those below), which is the stored position only for the top layer.
-/

namespace Provenstream
open Provenstream.Wire

/-! ## A layer's commands and events -/

/-- A schema a layer may use: `schemaOk`, and its commands mint nothing (a layer command takes no fresh id). -/
def layerSchemaOk (schema : List CmdSchema) : Bool := schemaOk schema && schema.all (·.minted.isEmpty)

/-- Proves a layer's translation equations (`Layer.Commands`), each by cases and `rfl`. -/
macro "layer_bijection" : tactic =>
  `(tactic| first | (intro x; cases x <;> rfl) | (intro ⟨_, x⟩; cases x <;> rfl))

/-- Proves that every command is on the wire under one of its schema's names, by cases and `simp`. -/
macro "layer_names" : tactic =>
  `(tactic| (intro x; cases x <;> simp))

/-- A request of a layer: caller, command, fresh ids (a layer command takes none). -/
abbrev LRequest (Cmd : Type) := Id × Cmd × Fresh

/-- A layer's commands and events: an event is its actor and its command (`toRequest`, `ofRequest`, inverse to each
other); a command is on one stream (`stream`) and is on the wire as the values of its schema entry (`toVals`,
`ofVals`). An event is on the wire under its schema entry's `event` name, with `actor_id` and the command's fields. -/
structure Layer.Commands where
  Cmd : Type
  Ev : Type
  [decEv : DecidableEq Ev]
  toRequest : Ev → Id × Cmd
  ofRequest : Id × Cmd → Ev
  stream : Cmd → Id
  schema : List CmdSchema
  toVals : Cmd → String × List Val
  ofVals : String → List Val → Option Cmd
  ofRequest_toRequest : ∀ e, ofRequest (toRequest e) = e := by layer_bijection
  toRequest_ofRequest : ∀ r, toRequest (ofRequest r) = r := by layer_bijection
  ofVals_toVals : ∀ c, ofVals (toVals c).1 (toVals c).2 = some c := by layer_bijection
  schema_ok : layerSchemaOk schema = true := by decide
  /-- Every command is on the wire under one of the schema's names. -/
  toVals_name : ∀ c, (schema.map (·.name)).contains (toVals c).1 = true := by layer_names

attribute [instance] Layer.Commands.decEv

namespace Layer.Commands
variable (C : Layer.Commands)

/-- The stream a layer event is on: its command's. -/
def evStream (e : C.Ev) : Id := C.stream (C.toRequest e).2

/-- On a concrete layer the stream of an event is its command's (`simp` reduces `L.evStream (.done a t i m)` to `t`). -/
@[simp] theorem evStream_mk {Cmd Ev : Type} [DecidableEq Ev] {toRequest : Ev → Id × Cmd} {ofRequest : Id × Cmd → Ev}
    {stream : Cmd → Id} {schema toVals ofVals h₁ h₂ h₃ h₄ h₅} (e : Ev) :
    evStream ⟨Cmd, Ev, toRequest, ofRequest, stream, schema, toVals, ofVals, h₁, h₂, h₃, h₄, h₅⟩ e =
      stream (toRequest e).2 := rfl

def names : List String := C.schema.map (·.name)

/-- The names of the layer's events. -/
def eventNames : List String := C.schema.map (·.event)

def fieldsOf (n : String) : List (String × Kind) := ((C.schema.find? (·.name == n)).map (·.fields)).getD []

/-- The name of command `n`'s event. -/
def eventOf (n : String) : String := ((C.schema.find? (·.name == n)).map (·.event)).getD ""

/-- A well-formed command: its values fit its schema entry's fields, in kind and form. -/
def cmdWf (cmd : C.Cmd) : Bool :=
  match C.schema.find? (·.name == (C.toVals cmd).1) with
  | some sc => valsWf sc.fields (C.toVals cmd).2
  | none => false

def requestWf : LRequest C.Cmd → Bool
  | (c, cmd, f) => validUuid c && C.cmdWf cmd && f.all validUuid

/-- A well-formed event: the same forms, through the request it came from. -/
def evWf (e : C.Ev) : Bool := C.requestWf ((C.toRequest e).1, (C.toRequest e).2, [])

def cmdToJ (cmd : C.Cmd) : J := objToJ "command" (C.toVals cmd).1 (C.fieldsOf (C.toVals cmd).1) (C.toVals cmd).2

/-- An event: its name, its actor, its command's fields. -/
def evToJ (e : C.Ev) : J :=
  let (n, vs) := C.toVals (C.toRequest e).2
  objToJ "event" (C.eventOf n) (("actor_id", .uuid) :: C.fieldsOf n) (.s (C.toRequest e).1 :: vs)

def cmdFromJ (j : J) : Except String C.Cmd := do
  let (sc, vs) ← objFromJ C.schema "command" (·.name) (fun _ => []) j
  let some cmd := C.ofVals sc.name vs | throw s!"command: {sc.name}: unexpected fields"
  checked "command" C.cmdWf cmd

def evFromJ (j : J) : Except String C.Ev := do
  let (sc, vs) ← objFromJ C.schema "event" (·.event) (fun _ => [("actor_id", .uuid)]) j
  let .s a :: vs := vs | throw s!"event: {sc.name}: unexpected fields"
  let some cmd := C.ofVals sc.name vs | throw s!"event: {sc.name}: unexpected fields"
  checked "event" C.evWf (C.ofRequest (a, cmd))

/-- The positions a command's references name (its `ref` fields, `Kind.ref`). -/
def refsOf (cmd : C.Cmd) : List Nat := refsIn (C.fieldsOf (C.toVals cmd).1) (C.toVals cmd).2

variable {C}

theorem cmdWf_find {cmd : C.Cmd} (h : C.cmdWf cmd = true) : ∃ sc, C.schema.find? (·.name == (C.toVals cmd).1) = some sc ∧
    valsWf sc.fields (C.toVals cmd).2 = true ∧ C.fieldsOf (C.toVals cmd).1 = sc.fields ∧
    C.eventOf (C.toVals cmd).1 = sc.event := by
  unfold cmdWf at h
  split at h
  · rename_i sc hsc; exact ⟨sc, hsc, h, by simp [fieldsOf, hsc], by simp [eventOf, hsc]⟩
  · cases h

theorem schema_ok' : schemaOk C.schema = true := by
  have := C.schema_ok; simp only [layerSchemaOk, Bool.and_eq_true] at this; exact this.1

theorem events_nodup : (C.schema.map (·.event)).Nodup := by
  have := C.schema_ok'; simp only [schemaOk, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1.2

/-- A command's name is under an entry of the schema, which `find?` finds. -/
theorem find_of_names {n : String} (h : C.names.contains n = true) : ∃ sc, C.schema.find? (·.name == n) = some sc := by
  cases hf : C.schema.find? (·.name == n) with
  | some sc => exact ⟨sc, rfl⟩
  | none =>
    obtain ⟨sc, hm, rfl⟩ := List.mem_map.mp (List.elem_iff.mp h)
    exact absurd (List.find?_eq_none.mp hf sc hm) (by simp)

/-- Every command's event is under one of the layer's event names. -/
theorem eventOf_mem (cmd : C.Cmd) : C.eventNames.contains (C.eventOf (C.toVals cmd).1) = true := by
  obtain ⟨sc, hsc⟩ := find_of_names (C.toVals_name cmd)
  simp only [eventOf, hsc, Option.map_some, Option.getD_some, eventNames]
  exact List.elem_iff.mpr (List.mem_map_of_mem (List.mem_of_find?_eq_some hsc))

theorem schema_entry_ok {sc : CmdSchema} (h : sc ∈ C.schema) : sc.ok = true := CmdSchema.ok_of_mem schema_ok' h

theorem schema_minted {sc : CmdSchema} (h : sc ∈ C.schema) : sc.minted = [] := by
  have := C.schema_ok
  simp only [layerSchemaOk, Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff] at this
  exact this.2 sc h

theorem find_name {n : String} {sc : CmdSchema} (h : C.schema.find? (·.name == n) = some sc) : sc.name = n := by
  simpa using List.find?_some h

theorem cmdFromJ_toJ (cmd : C.Cmd) (h : C.cmdWf cmd = true) : C.cmdFromJ (C.cmdToJ cmd) = .ok cmd := by
  obtain ⟨sc, hsc, hwf, hfs, -⟩ := cmdWf_find h
  have := objFromJ_toJ (what := "command") (key := (·.name)) (extra := fun _ => []) hsc (by simpa using hwf)
    (by simpa using CmdSchema.cmd_nodup (schema_entry_ok (List.mem_of_find?_eq_some hsc)))
  simp only [List.nil_append] at this
  simp only [cmdFromJ, cmdToJ, hfs, this, find_name hsc, C.ofVals_toVals, checked_ok h, bind, Except.bind]

theorem evFromJ_toJ (e : C.Ev) (h : C.evWf e = true) : C.evFromJ (C.evToJ e) = .ok e := by
  have hc : C.cmdWf (C.toRequest e).2 = true := by simp_all [evWf, requestWf]
  obtain ⟨sc, hsc, hwf, hfs, hev⟩ := cmdWf_find hc
  have hm := schema_minted (List.mem_of_find?_eq_some hsc)
  have hnd := CmdSchema.ev_nodup (schema_entry_ok (List.mem_of_find?_eq_some hsc))
  simp only [CmdSchema.evFields, hm, List.map_nil] at hnd
  have hse := find_key_of_mem (key := (·.event)) C.events_nodup (List.mem_of_find?_eq_some hsc)
  have := objFromJ_toJ (what := "event") (key := (·.event)) (extra := fun _ => [("actor_id", .uuid)])
    (vs := .s (C.toRequest e).1 :: (C.toVals (C.toRequest e).2).2)
    hse (by simp_all [valsWf, Kind.wf, evWf, requestWf]) (by simpa using hnd)
  simp only [evFromJ, evToJ, hfs, hev, List.cons_append, List.nil_append] at this ⊢
  simp only [this, find_name hsc, C.ofVals_toVals, C.ofRequest_toRequest, checked_ok h, bind, Except.bind]

theorem cmdFromJ_wf {j : J} {cmd : C.Cmd} (h : C.cmdFromJ j = .ok cmd) : C.cmdWf cmd = true := by
  unfold cmdFromJ at h
  simp only [bind, Except.bind] at h
  repeat (first | (split at h <;> try contradiction) | exact checked_wf h)

theorem evFromJ_wf {j : J} {e : C.Ev} (h : C.evFromJ j = .ok e) : C.evWf e = true := by
  unfold evFromJ at h
  simp only [bind, Except.bind] at h
  repeat (first | (split at h <;> try contradiction) | exact checked_wf h)

theorem cmdFromJ_keys {j : J} {cmd : C.Cmd} (h : C.cmdFromJ j = .ok cmd) :
    ∃ sc ∈ C.schema, ∃ kvs, j = .obj kvs ∧ get? kvs "command" = some (.str sc.name) ∧
      ∀ kv ∈ kvs, kv.1 ∈ "command" :: sc.fields.map (·.1) := by
  unfold cmdFromJ at h
  simp only [bind, Except.bind] at h
  cases ho : objFromJ C.schema "command" (·.name) (fun _ => []) j with
  | error e => rw [ho] at h; cases h
  | ok p =>
    obtain ⟨sc, vs⟩ := p
    obtain ⟨hm, kvs, rfl, hn, hk⟩ := objFromJ_keys ho
    exact ⟨sc, hm, kvs, rfl, hn, by simpa using hk⟩

theorem toVals_mem (cmd : C.Cmd) : C.names.contains (C.toVals cmd).1 = true := C.toVals_name cmd

end Layer.Commands

/-! ## What a layer's rules remember of the stream's own layer events -/

/-- What a layer's rules read of the layer events before the candidate on its stream (`read`), and the state the fast
path keeps instead: folding those events into the state and taking its `view` is reading them (`fold_view`). -/
structure Memory (Ev : Type) where
  V : Type
  read : List Ev → V
  St : Type
  [decSt : DecidableEq St]
  init : St
  step : St → Ev → St
  view : St → V
  fold_view : ∀ past, view (past.foldl step init) = read past
  stateToJ : St → J
  stateFromJ : J → Except String St
  stateFromJ_toJ : ∀ st, stateFromJ (stateToJ st) = .ok st

attribute [instance] Memory.decSt

/-- **A fold memory**: the rules read the fold of the stream's layer events (`read := foldl step init`, `view := id`),
so the obligation `fold_view` is `rfl`. -/
abbrev foldMemory {Ev St : Type} [DecidableEq St] (init : St) (step : St → Ev → St) (toJ : St → J)
    (ofJ : J → Except String St) (h : ∀ st, ofJ (toJ st) = .ok st) : Memory Ev where
  V := St
  read past := past.foldl step init
  St := St
  init := init
  step := step
  view st := st
  fold_view _ := rfl
  stateToJ := toJ
  stateFromJ := ofJ
  stateFromJ_toJ := h

/-- A fact a layer event states: a name and a key (`("created", item id)`). -/
abbrev Fact := String × String

/-- Add a fact unless it is there: the facts, in order of first mention. -/
def addFact (st : List Fact) (x : Fact) : List Fact := if st.contains x then st else st ++ [x]

theorem contains_foldl_addFact (ms st : List Fact) (x : Fact) :
    (ms.foldl addFact st).contains x = (st.contains x || ms.contains x) := by
  induction ms generalizing st with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons, ih, addFact]
    split <;> rename_i h <;> by_cases hx : x = y <;> simp_all

theorem facts_fold {Ev : Type} (marks : Ev → List Fact) (past : List Ev) (st : List Fact) (x : Fact) :
    (past.foldl (fun st e => (marks e).foldl addFact st) st).contains x =
      (st.contains x || past.any fun e => (marks e).contains x) := by
  induction past generalizing st with
  | nil => simp
  | cons e es ih => simp only [List.foldl_cons, List.any_cons, ih, contains_foldl_addFact, Bool.or_assoc]

theorem facts_view {Ev : Type} (marks : Ev → List Fact) (past : List Ev) :
    (fun f k => (past.foldl (fun st e => (marks e).foldl addFact st) []).contains (f, k)) =
      fun f k => past.any fun e => (marks e).contains (f, k) := by
  funext f k; simpa using facts_fold marks past [] (f, k)

def factsToJ (st : List Fact) : J := .arr (st.map fun (f, k) => .arr [.str f, .str k])

def factsFromJ : J → Except String (List Fact)
  | .arr xs => xs.mapM fun
    | .arr [.str f, .str k] => .ok (f, k)
    | _ => .error "state: expected a fact"
  | _ => .error "state: expected facts"

theorem factsFromJ_toJ (st : List Fact) : factsFromJ (factsToJ st) = .ok st := by
  induction st with
  | nil => rfl
  | cons x xs ih =>
    simp only [factsToJ, factsFromJ, List.map_cons, List.mapM_cons] at ih ⊢
    simp [ih, bind, Except.bind, pure, Except.pure]

/-- **Facts**: the rules read whether some layer event before the candidate on its stream stated fact `f` of key `k`
(`seen f k`); the state is the facts stated, in order of first mention. `marks e`: the facts event `e` states. -/
def Memory.facts {Ev : Type} (marks : Ev → List Fact) : Memory Ev where
  V := String → String → Bool
  read past f k := past.any fun e => (marks e).contains (f, k)
  St := List Fact
  init := []
  step st e := (marks e).foldl addFact st
  view st f k := st.contains (f, k)
  fold_view := facts_view marks
  stateToJ := factsToJ
  stateFromJ := factsFromJ
  stateFromJ_toJ := factsFromJ_toJ

/-- The keys of fact `f` in a facts state, in order of first mention (for reads). -/
def factKeys (st : List Fact) (f : String) : List String := st.filterMap fun (f', k) => if f' == f then some k else none

@[simp] theorem Memory.facts_read {Ev : Type} (marks : Ev → List Fact) (past : List Ev) (f k : String) :
    (Memory.facts marks).read past f k = past.any fun e => (marks e).contains (f, k) := rfl

/-! ## Projection keeps validity -/

/-- **Projection keeps validity.** If every event a service `S` accepts projects (by `f`) to nothing or to an event
that service `T` accepts against the projection of the log, the projection of every valid log of `S` is a valid log
of `T`. `ValidX.base` below is this, at the projection to the base. -/
theorem Service.Valid.project {S T : Service} (f : S.Ev → Option T.Ev)
    (hok : ∀ log e, S.Valid log → S.ok log e = true → ∀ e', f e = some e' → T.ok (log.filterMap f) e' = true)
    {log : S.Log} (h : S.Valid log) : T.Valid (log.filterMap f) := by
  induction h with
  | nil => exact .nil
  | @snoc log e hv hk ih =>
    rw [List.filterMap_append]
    cases hf : f e with
    | none => simpa [hf] using ih
    | some e' => simpa [hf] using Service.Valid.snoc ih (hok log e hv hk e' hf)

/-! ## A base: a service, the facts it shows the layer above, and what it asks of every actor -/

theorem keyStr_objToJ (what n : String) (fs : List (String × Kind)) (vs : List Val) :
    keyStr what (objToJ what n fs vs) = some n := by
  simp [keyStr, objToJ, get?]

/-- What a layer sits on: a service (the core, `coreBase`, or a layer with everything below it, `Layer.toBase`), and
- `view log t`: what its layers' rules and guards may read of stream `t` after `log`, which reads only `t`'s events
  (`view_local`), and which the fast path reads from the stream's state (`viewS`, `viewS_fold`);
- `admits v a`: what it asks of every event a layer adds, by the event's actor `a` against the view of its stream
  (`none`: admitted; `some r`: refused with `r`), and the reasons it can give, in order (`admitRules`, for the
  description);
- `live st`: the stream exists, so a read of it shows the layers' fields;
- that every request and event it encodes is under one of its schema's command or event names (`requestToJ_name`,
  `eventToJ_name`), which no layer above may use. -/
structure Base extends Service where
  View : Type
  view : List Ev → Id → View
  view_local : ∀ log s, view (log.filter (stream · == s)) s = view log s
  viewS : St → View
  viewS_fold : ∀ s (log : List Ev), viewS (log.foldl step (init s)) = view log s
  admits : View → Id → Option String
  admitRules : List String
  admits_named : ∀ v a r, admits v a = some r → r ∈ admitRules
  live : St → Bool
  requestToJ_name : ∀ r, ∃ n, cmdName (requestToJ r) = some n ∧ n ∈ schema.map (·.name)
  eventToJ_name : ∀ e, ∃ n, keyStr "event" (eventToJ e) = some n ∧ n ∈ schema.map (·.event)

/-- The names a base's commands are under. -/
abbrev Base.names (B : Base) : List String := B.schema.map (·.name)

/-- The names a base's events are under. -/
abbrev Base.eventNames (B : Base) : List String := B.schema.map (·.event)

theorem core_requestToJ_name (r : Request) : ∃ n, cmdName (requestToJ r) = some n ∧ n ∈ coreSchema.map (·.name) := by
  obtain ⟨c, cmd, f⟩ := r
  refine ⟨cmd.toVals.1, ?_, ?_⟩
  · simp [cmdName, requestToJ, get?, commandToJ, objToJ, keyStr]
  · rw [← Command.name_schema]; exact List.mem_map_of_mem (Command.schema_mem cmd)

theorem core_eventToJ_name (e : Event) : ∃ n, keyStr "event" (eventToJ e) = some n ∧ n ∈ coreSchema.map (·.event) := by
  refine ⟨(toRequest e).2.1.schema.event, ?_, ?_⟩
  · simp [eventToJ, keyStr, objToJ, get?]
  · exact List.mem_map_of_mem (Command.schema_mem _)

/-- **The core, as a base**: its view is `Past.view` (opened, closed, the opener), read from the state by
`StreamState.view`, and what it asks of every event a layer adds is `View.admits`: the stream is open and not closed. -/
abbrev coreBase : Base where
  toService := coreService
  View := Provenstream.View
  view log t := Past.view log t
  view_local log s := view_onStream log s
  viewS := StreamState.view
  viewS_fold s log := fold_view s log
  admits := View.admits
  admitRules := admitReasons
  admits_named _ _ _ h := View.admits_named h
  live st := st.opened
  requestToJ_name := core_requestToJ_name
  eventToJ_name := core_eventToJ_name

@[simp] theorem coreBase_view (log : Log) (t : Id) : coreBase.view log t = Past.view log t := rfl
@[simp] theorem coreBase_admits (v : View) (a : Id) : coreBase.admits v a = v.admits a := rfl
@[simp] theorem coreBase_names : coreBase.names = coreNames := rfl
@[simp] theorem coreBase_eventNames : coreBase.eventNames = coreSchema.map (·.event) := rfl

/-! ## A layer -/

/-- A layer's rule: the refusal a caller sees when it fails (named for what it requires), the commands it judges (it
should hold of every other event; the description lists it under these), and its check against the base's view of the
event's stream (`BV`), what the layer's memory reads (`V`), and the event (`Ev`). A guard is a rule whose events are the
base's. -/
structure Layer.Rule (BV V Ev : Type) where
  reason : String
  cmds : List String
  holds : BV → V → Ev → Bool

/-- A layer's rule about the events its references name: it reads, for each position of the event's stream, what
the layer's `tag` says of the event there (`none` for a base event or an untagged one), and the event. -/
structure Layer.RefRule (Ev : Type) where
  reason : String
  cmds : List String
  holds : (Nat → Option (Option String)) → Ev → Bool

/-- A layer on base `B` (the core, by default): its commands and events, what its rules remember, its rules (tried
in order after the base's admission of the actor), its guards (tried after the base's own rules on the base's events),
what it shows the layer above (`Exposed`), and what a read of a stream adds (`readJ`). Its command names are none of
the base's (`names_ok`, by `decide`), and neither are its event names (`events_ok`). -/
structure Layer (B : Base := coreBase) extends Layer.Commands where
  memory : Memory Ev
  rules : List (Layer.Rule B.View memory.V Ev)
  guards : List (Layer.Rule B.View memory.V B.Ev) := []
  Exposed : Type := memory.V
  expose : memory.V → Exposed := by exact fun v => v
  readJ : memory.St → Fields := fun _ => []
  /-- What reference rules may read of an event of this layer (default: nothing). -/
  tag : Ev → Option String := fun _ => none
  /-- Rules about the events an event's references name, tried after `rules`. -/
  refRules : List (Layer.RefRule Ev) := []
  names_ok : B.names.all (fun n => !(schema.map (·.name)).contains n) = true := by decide
  events_ok : B.eventNames.all (fun n => !(schema.map (·.event)).contains n) = true := by decide

/-- An event of a combined log: the base's (`inl`) or the layer's (`inr`). -/
inductive Layer.XE {B : Base} {L : Layer B} : Type where
  | inl (e : B.Ev)
  | inr (x : L.Ev)
  deriving DecidableEq

namespace Layer
variable {B : Base} (L : Layer B)

/-! ## The combined log -/

abbrev XEv := @XE B L
abbrev XLog := List L.XEv
abbrev XReq := B.Req ⊕ LRequest L.Cmd

variable {L}

/-- The base's event of a combined event, if it is one. -/
def baseOf : L.XEv → Option B.Ev
  | .inl e => some e
  | .inr _ => none

/-- The base's events of a combined log, in order: its projection to the level below. -/
def bases : L.XLog → List B.Ev := List.filterMap baseOf

/-- The core's events of a combined log over the core. -/
abbrev cores {L : Layer coreBase} (log : L.XLog) : Log := bases log

/-- The layer's events of a combined log, in order. -/
def exts : L.XLog → List (L.Ev) := List.filterMap fun | .inl _ => none | .inr x => some x

/-- The actor of a layer event. -/
def evActor (x : L.Ev) : Id := (L.toRequest x).1

@[simp] theorem baseOf_inl (e : B.Ev) : baseOf (L := L) (.inl e) = some e := rfl
@[simp] theorem baseOf_inr (x : L.Ev) : baseOf (L := L) (.inr x) = none := rfl
@[simp] theorem bases_nil : bases ([] : L.XLog) = [] := rfl
@[simp] theorem exts_nil : exts ([] : L.XLog) = [] := rfl
@[simp] theorem bases_append (a b : L.XLog) : bases (a ++ b) = bases a ++ bases b := List.filterMap_append ..
@[simp] theorem exts_append (a b : L.XLog) : exts (a ++ b) = exts a ++ exts b := List.filterMap_append ..
@[simp] theorem bases_cons_inl (e : B.Ev) (l : L.XLog) : bases (.inl e :: l) = e :: bases l := rfl
@[simp] theorem bases_cons_inr (x : L.Ev) (l : L.XLog) : bases (.inr x :: l) = bases l := rfl
@[simp] theorem exts_cons_inl (e : B.Ev) (l : L.XLog) : exts (.inl e :: l) = exts l := rfl
@[simp] theorem exts_cons_inr (x : L.Ev) (l : L.XLog) : exts (.inr x :: l) = x :: exts l := rfl

/-- **Stuttering**: a layer event projects to no base event. -/
theorem bases_snoc_inr (log : L.XLog) (x : L.Ev) : bases (log ++ [.inr x]) = bases log := by simp

/-- The layer's events of stream `t` in a combined log, in order: what the layer's memory reads. -/
def evs (log : L.XLog) (t : Id) : List (L.Ev) := (exts log).filter (L.evStream · == t)

@[simp] theorem mem_bases {e : B.Ev} {log : L.XLog} : e ∈ bases log ↔ .inl e ∈ log := by
  simp [bases, List.mem_filterMap]; constructor
  · rintro ⟨a, h, ha⟩; cases a <;> simp_all [baseOf]
  · intro h; exact ⟨_, h, rfl⟩
@[simp] theorem mem_exts {x : L.Ev} {log : L.XLog} : x ∈ exts log ↔ .inr x ∈ log := by
  simp [exts, List.mem_filterMap]; constructor
  · rintro ⟨a, h, ha⟩; cases a <;> simp_all
  · intro h; exact ⟨_, h, rfl⟩

@[simp] theorem evs_nil (t : Id) : evs ([] : L.XLog) t = [] := rfl
@[simp] theorem evs_append (a b : L.XLog) (t : Id) : evs (a ++ b) t = evs a t ++ evs b t := by
  simp [evs, List.filter_append]
@[simp] theorem evs_cons_inl (e : B.Ev) (l : L.XLog) (t : Id) : evs (.inl e :: l) t = evs l t := rfl
@[simp] theorem evs_cons_inr (x : L.Ev) (l : L.XLog) (t : Id) :
    evs (.inr x :: l) t = if L.evStream x = t then x :: evs l t else evs l t := by
  by_cases h : L.evStream x = t <;> simp only [evs, exts_cons_inr, List.filter_cons, h, beq_self_eq_true] <;> simp [h]
@[simp] theorem mem_evs {x : L.Ev} {log : L.XLog} {t : Id} : x ∈ evs log t ↔ .inr x ∈ log ∧ L.evStream x = t := by
  simp only [evs, List.mem_filter, mem_exts, beq_iff_eq]

/-- The stream of a combined event. -/
def streamX : L.XEv → Id
  | .inl e => B.stream e
  | .inr x => L.evStream x

@[simp] theorem streamX_inl (e : B.Ev) : streamX (L := L) (.inl e) = B.stream e := rfl
@[simp] theorem streamX_inr (x : L.Ev) : streamX (L := L) (.inr x) = L.evStream x := rfl

/-- What reference rules read of a combined event: the layer's tag of its own events, nothing of the base's. -/
def tagX : L.XEv → Option String
  | .inl _ => none
  | .inr x => L.tag x

@[simp] theorem tagX_inl (e : B.Ev) : tagX (L := L) (.inl e) = none := rfl
@[simp] theorem tagX_inr (x : L.Ev) : tagX (L := L) (.inr x) = L.tag x := rfl

/-- The element at position `n`, by structural recursion (not `xs[n]?`, whose instance reaches a panic the audit
refuses). -/
def nth {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => nth xs n

@[simp] theorem nth_eq {α : Type} (l : List α) (n : Nat) : nth l n = l[n]? := by
  induction l generalizing n with
  | nil => rfl
  | cons x xs ih => cases n <;> simp [nth, ih]

/-- The positions a layer event's references name. -/
def evRefs (x : L.Ev) : List Nat := L.refsOf (L.toRequest x).2

/-- The events of stream `s` in a combined log, in order: position `n` of the stream is index `n` here. -/
def onStreamX (log : L.XLog) (s : Id) : L.XLog := log.filter (streamX · == s)

/-- The reason the mechanism refuses a reference to no earlier event of the stream. -/
def refReason : String := "ref_must_name_an_earlier_event"

/-- **The mechanism's check of references**: every position an event's references name is below the stream's length,
so names an event already in the stream. -/
def refCheck (len : Nat) (x : L.Ev) : Option String :=
  if (evRefs x).all (· < len) then none else some refReason

/-! ## The rules and the guards, combined -/

/-- The first layer rule that `x` fails. -/
def rejectionL (v : B.View) (w : L.memory.V) (x : L.Ev) : Option String :=
  (L.rules.find? (!·.holds v w x)).map (·.reason)

/-- The first guard that the base's event `e` fails. -/
def rejectionG (v : B.View) (w : L.memory.V) (e : B.Ev) : Option String :=
  (L.guards.find? (!·.holds v w e)).map (·.reason)

/-- The first reference rule that `x` fails, given what the tags say at each position of its stream. -/
def rejectionR (look : Nat → Option (Option String)) (x : L.Ev) : Option String :=
  (L.refRules.find? (!·.holds look x)).map (·.reason)

theorem rejectionR_none {look : Nat → Option (Option String)} {x : L.Ev} :
    L.rejectionR look x = none ↔ ∀ r ∈ L.refRules, r.holds look x = true := by
  simp [rejectionR, List.find?_eq_none]

theorem rejectionL_none {v : B.View} {w : L.memory.V} {x : L.Ev} :
    L.rejectionL v w x = none ↔ ∀ r ∈ L.rules, r.holds v w x = true := by
  simp [rejectionL, List.find?_eq_none]

theorem rejectionG_none {v : B.View} {w : L.memory.V} {e : B.Ev} :
    L.rejectionG v w e = none ↔ ∀ g ∈ L.guards, g.holds v w e = true := by
  simp [rejectionG, List.find?_eq_none]

/-- The first rule a candidate fails against the combined log: for the base's event, the base's rules against the
base's events, then the layer's guards; for the layer's, the base's admission of its actor, then the layer's rules;
each guard and rule against the base's view of the stream and the memory of the stream's layer events. -/
def rejectionX (log : L.XLog) : L.XEv → Option String
  | .inl e => (B.rejection (bases log) e).or
      (L.rejectionG (B.view (bases log) (B.stream e)) (L.memory.read (evs log (B.stream e))) e)
  | .inr x => (B.admits (B.view (bases log) (L.evStream x)) (evActor x)).or
      ((refCheck (onStreamX log (L.evStream x)).length x).or
      ((L.rejectionL (B.view (bases log) (L.evStream x)) (L.memory.read (evs log (L.evStream x))) x).or
      (L.rejectionR (fun n => nth ((onStreamX log (L.evStream x)).map tagX) n) x)))

theorem onStreamX_filter (log : L.XLog) (s : Id) : onStreamX (log.filter (streamX · == s)) s = onStreamX log s := by
  simp only [onStreamX, List.filter_filter, Bool.and_self]

theorem bases_filter (log : L.XLog) (s : Id) : bases (log.filter (streamX · == s)) = (bases log).filter (B.stream · == s) := by
  induction log with
  | nil => rfl
  | cons e es ih => cases e <;> simp only [List.filter_cons] at ih ⊢ <;> split <;> simp_all [streamX]

theorem exts_filter (log : L.XLog) (s : Id) : exts (log.filter (streamX · == s)) = (exts log).filter (L.evStream · == s) := by
  induction log with
  | nil => rfl
  | cons e es ih => cases e <;> simp only [List.filter_cons] at ih ⊢ <;> split <;> simp_all [streamX]

theorem evs_filter (log : L.XLog) (s : Id) : evs (log.filter (streamX · == s)) s = evs log s := by
  simp only [evs, exts_filter, List.filter_filter, Bool.and_self]

theorem rejectionX_local (log : L.XLog) (e : L.XEv) :
    rejectionX (log.filter (streamX · == streamX e)) e = rejectionX log e := by
  cases e with
  | inl e =>
    rw [show streamX (L := L) (.inl e) = B.stream e from rfl]
    simp only [rejectionX]; rw [bases_filter, evs_filter, B.view_local, B.rejection_local]
  | inr x =>
    rw [show streamX (L := L) (.inr x) = L.evStream x from rfl]
    simp only [rejectionX]; rw [bases_filter, evs_filter, B.view_local, onStreamX_filter]

/-! ## Commands, combined: a layer command mints nothing, so it takes no fresh ids -/

def toEventX : L.XReq → Except String L.XEv
  | .inl r => (B.toEvent r).map .inl
  | .inr (c, cmd, []) => .ok (.inr (L.ofRequest (c, cmd)))
  | .inr _ => .error "fresh_ids_must_match_the_command"

def toRequestX : L.XEv → L.XReq
  | .inl e => .inl (B.toRequest e)
  | .inr x => .inr ((L.toRequest x).1, (L.toRequest x).2, [])

def reqStreamX : L.XReq → Id
  | .inl r => B.reqStream r
  | .inr (_, cmd, _) => L.stream cmd

theorem toEventX_ok_iff {r : L.XReq} {e : L.XEv} : toEventX r = .ok e ↔ toRequestX e = r := by
  rcases r with r | ⟨c, cmd, _ | ⟨_, _⟩⟩ <;> rcases e with e | x <;>
    simp [toEventX, toRequestX, Service.except_map_ok, B.toEvent_ok_iff]
  constructor
  · rintro rfl; simp [L.toRequest_ofRequest]
  · intro h; rw [← L.ofRequest_toRequest x, show L.toRequest x = (c, cmd) from Prod.ext h.1 h.2]

theorem toEventX_stream {r : L.XReq} {e : L.XEv} (h : toEventX r = .ok e) : streamX e = reqStreamX r := by
  have := toEventX_ok_iff.mp h; subst this
  cases e with
  | inl e => exact B.toEvent_stream (B.toEvent_ok_iff.mpr rfl)
  | inr x => rfl

/-! ## The fast path, combined: the base's state and the layer memory's, side by side -/

/-- The fast path's state: the base's, the layer memory's, and the tags of the stream's events, in order. -/
abbrev XSt (L : Layer B) := B.St × L.memory.St × List (Option String)

def stepX (st : L.XSt) : L.XEv → L.XSt
  | .inl e => (B.step st.1 e, st.2.1, if B.stream e = B.stStream st.1 then st.2.2 ++ [none] else st.2.2)
  | .inr x => (st.1, (if L.evStream x = B.stStream st.1 then L.memory.step st.2.1 x else st.2.1),
      if L.evStream x = B.stStream st.1 then st.2.2 ++ [L.tag x] else st.2.2)

def rejectionXS (st : L.XSt) : L.XEv → Option String
  | .inl e => (B.rejectionS st.1 e).or (L.rejectionG (B.viewS st.1) (L.memory.view st.2.1) e)
  | .inr x => (B.admits (B.viewS st.1) (evActor x)).or ((refCheck st.2.2.length x).or
      ((L.rejectionL (B.viewS st.1) (L.memory.view st.2.1) x).or (L.rejectionR (fun n => nth st.2.2 n) x)))

theorem foldl_stepX (log : L.XLog) (st : L.XSt) :
    log.foldl stepX st = ((bases log).foldl B.step st.1,
      ((exts log).filter (L.evStream · == B.stStream st.1)).foldl L.memory.step st.2.1,
      st.2.2 ++ (onStreamX log (B.stStream st.1)).map tagX) := by
  induction log generalizing st with
  | nil => simp [onStreamX]
  | cons e es ih =>
    cases e <;> simp only [List.foldl_cons, ih, stepX, B.stStream_step, bases_cons_inl, bases_cons_inr,
      exts_cons_inl, exts_cons_inr, List.filter_cons, onStreamX] <;> (try split) <;> simp_all [streamX]

theorem fold_stepX (s : Id) (log : L.XLog) :
    log.foldl stepX (B.init s, L.memory.init, []) =
      (B.fold s (bases log), (evs log s).foldl L.memory.step L.memory.init, (onStreamX log s).map tagX) := by
  rw [foldl_stepX]; simp only [B.stStream_init, List.nil_append]; rfl

theorem rejectionXS_fold (log : L.XLog) (e : L.XEv) :
    rejectionXS (log.foldl stepX (B.init (streamX e), L.memory.init, [])) e = rejectionX log e := by
  rw [fold_stepX]
  cases e with
  | inl e =>
    simp only [rejectionXS, rejectionX, streamX, L.memory.fold_view, Service.fold, B.rejectionS_fold, B.viewS_fold]
  | inr x => simp only [rejectionXS, rejectionX, streamX, L.memory.fold_view, Service.fold, B.viewS_fold, List.length_map]

/-! ## The wire, combined -/

def requestToJL (r : LRequest L.Cmd) : J :=
  .obj [("actor_id", .str r.1), ("command", L.cmdToJ r.2.1), ("fresh", .arr (r.2.2.map .str))]

def requestFromJL (j : J) : Except String (LRequest L.Cmd) := do
  let (c, cmd, f) ← requestParts j
  checked "request" L.requestWf (← actorFromJ c, ← L.cmdFromJ cmd, ← freshFromJ f)

/-- Is this request the layer's: its `command` object names one of the layer's commands. -/
def isLayerRequest (j : J) : Bool :=
  match cmdName j with
  | some n => L.names.contains n
  | none => false

def requestToJX : L.XReq → J
  | .inl r => B.requestToJ r
  | .inr r => requestToJL r

def requestFromJX (j : J) : Except String L.XReq :=
  if isLayerRequest (L := L) j then (requestFromJL j).map .inr else (B.requestFromJ j).map .inl

def requestWfX : L.XReq → Bool
  | .inl r => B.requestWf r
  | .inr r => L.requestWf r

def eventToJX : L.XEv → J
  | .inl e => B.eventToJ e
  | .inr x => L.evToJ x

def eventFromJX (j : J) : Except String L.XEv :=
  if hasName "event" L.eventNames j then (L.evFromJ j).map .inr else (B.eventFromJ j).map .inl

def eventWfX : L.XEv → Bool
  | .inl e => B.eventWf e
  | .inr x => L.evWf x

/-- A snapshot: the base's state (under `core`) and the layer memory's. Over a layer, the base's state is itself such
an object: snapshots nest. -/
def tagsToJ (ts : List (Option String)) : J := .arr (ts.map metaJ)

def tagsFromJ : J → Except String (List (Option String))
  | .arr xs => xs.mapM fun
    | .null => .ok none
    | .str t => .ok (some t)
    | _ => .error "state.tags: expected a string or null"
  | _ => .error "state.tags: expected an array"

theorem tagsFromJ_toJ (ts : List (Option String)) : tagsFromJ (tagsToJ ts) = .ok ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [tagsToJ, tagsFromJ, List.map_cons, List.mapM_cons] at ih ⊢
    cases t <;> simp [ih, metaJ, bind, Except.bind, pure, Except.pure]

def stateToJX (st : L.XSt) : J :=
  .obj [("core", B.stateToJ st.1), ("layer", L.memory.stateToJ st.2.1), ("tags", tagsToJ st.2.2)]

def stateFromJX (j : J) : Except String L.XSt := do
  let kvs ← fields "state" j
  let some c := get? kvs "core" | throw "state.core: missing"
  let some x := get? kvs "layer" | throw "state.layer: missing"
  let some t := get? kvs "tags" | throw "state.tags: missing"
  return (← B.stateFromJ c, ← L.memory.stateFromJ x, ← tagsFromJ t)

/-- A read of a stream: the base's read, with the layer's fields added when the stream exists. -/
def streamSJX (st : L.XSt) : J :=
  match B.streamSJ st.1 with
  | .obj kvs => if B.live st.1 then .obj (kvs ++ L.readJ st.2.1) else .obj kvs
  | j => j

theorem names_disjoint {n : String} (hn : n ∈ B.names) : L.names.contains n = false := by
  have := List.all_eq_true.mp L.names_ok n hn
  simpa [Commands.names] using this

theorem events_disjoint {n : String} (hn : n ∈ B.eventNames) : L.eventNames.contains n = false := by
  have := List.all_eq_true.mp L.events_ok n hn
  simpa [Commands.eventNames] using this

theorem requestFromJX_toJ (r : L.XReq) (h : requestWfX r = true) : requestFromJX (requestToJX r) = .ok r := by
  rcases r with r | ⟨c, cmd, f⟩
  · obtain ⟨n, hn, hm⟩ := B.requestToJ_name r
    have : isLayerRequest (L := L) (B.requestToJ r) = false := by
      simp only [isLayerRequest, hn, names_disjoint hm]
    simp only [requestFromJX, requestToJX, this, Bool.false_eq_true, ite_false]
    rw [B.requestFromJ_toJ r h]; rfl
  · have hcmd : L.cmdWf cmd = true := by simp_all [requestWfX, Commands.requestWf]
    have hl : isLayerRequest (L := L) (requestToJL (c, cmd, f)) = true := by
      simpa [isLayerRequest, requestToJL, cmdName, get?, List.find?, Commands.cmdToJ, keyStr_objToJ] using
        Commands.toVals_mem cmd
    have hr := checked_ok (w := "request") (show L.requestWf (c, cmd, f) = true from h)
    simp only [requestFromJX, requestToJX, hl, ite_true]
    simp_all [requestFromJL, requestToJL, requestParts_toJ, actorFromJ, Commands.cmdFromJ_toJ cmd hcmd, freshFromJ,
      strs_toJ, bind, Except.bind, Except.map]

theorem requestFromJX_wf {j : J} {r : L.XReq} (h : requestFromJX j = .ok r) : requestWfX r = true := by
  unfold requestFromJX at h
  split at h <;> obtain ⟨a, ha, rfl⟩ := Service.except_map_ok.mp h
  · unfold requestFromJL at ha
    simp only [bind, Except.bind] at ha
    repeat (first | (split at ha <;> try contradiction) | exact (checked_wf ha :))
  · exact B.requestFromJ_wf ha

theorem eventFromJX_toJ (e : L.XEv) (h : eventWfX e = true) : eventFromJX (eventToJX e) = .ok e := by
  cases e with
  | inl e =>
    obtain ⟨n, hn, hm⟩ := B.eventToJ_name e
    have : hasName "event" L.eventNames (B.eventToJ e) = false := by simp only [hasName, hn, events_disjoint hm]
    simp only [eventFromJX, eventToJX, this, Bool.false_eq_true, ite_false]
    rw [B.eventFromJ_toJ e h]; rfl
  | inr x =>
    have : hasName "event" L.eventNames (L.evToJ x) = true := by
      simpa [hasName, Commands.evToJ, keyStr_objToJ] using Commands.eventOf_mem (L.toRequest x).2
    simp only [eventFromJX, eventToJX, this, ite_true]
    rw [Commands.evFromJ_toJ x h]; rfl

theorem eventFromJX_wf {j : J} {e : L.XEv} (h : eventFromJX j = .ok e) : eventWfX e = true := by
  unfold eventFromJX at h
  split at h <;> obtain ⟨a, ha, rfl⟩ := Service.except_map_ok.mp h
  · exact Commands.evFromJ_wf ha
  · exact B.eventFromJ_wf ha

theorem stateFromJX_toJ (st : L.XSt) : stateFromJX (stateToJX st) = .ok st := by
  obtain ⟨c, x, t⟩ := st
  simp [stateFromJX, stateToJX, fields, get?, List.find?, B.stateFromJ_toJ, L.memory.stateFromJ_toJ, tagsFromJ_toJ,
    bind, Except.bind, pure, Except.pure]

/-! ## The combined description: the base's commands, then the layer's -/

theorem requestFromJX_schema {j : J} {r : L.XReq} (h : requestFromJX j = .ok r) :
    ∃ sc ∈ B.schema ++ L.schema, ∃ kvs, cmdObj j = some kvs ∧ get? kvs "command" = some (.str sc.name) ∧
      ∀ kv ∈ kvs, kv.1 ∈ "command" :: sc.fields.map (·.1) := by
  unfold requestFromJX at h
  split at h <;> obtain ⟨a, ha, rfl⟩ := Service.except_map_ok.mp h
  · unfold requestFromJL at ha
    simp only [bind, Except.bind] at ha
    cases hp : requestParts j with
    | error e => rw [hp] at ha; cases ha
    | ok p =>
      obtain ⟨c, cj, f⟩ := p
      rw [hp] at ha
      dsimp only at ha
      obtain ⟨kvs, rfl, hg⟩ := requestParts_ok hp
      cases hc : actorFromJ c with
      | error e => rw [hc] at ha; cases ha
      | ok c' =>
        rw [hc] at ha
        cases hm : L.cmdFromJ cj with
        | error e => rw [hm] at ha; cases ha
        | ok cmd =>
          obtain ⟨sc, hsc, ckvs, rfl, hn, hk⟩ := Commands.cmdFromJ_keys hm
          exact ⟨sc, List.mem_append_right _ hsc, ckvs, by simp [cmdObj, hg], hn, hk⟩
  · obtain ⟨sc, hsc, rest⟩ := B.requestFromJ_schema ha
    exact ⟨sc, List.mem_append_left _ hsc, rest⟩

theorem requestToJX_schema (r : L.XReq) (h : requestWfX r = true) :
    ∃ sc ∈ B.schema ++ L.schema, ∃ kvs, cmdObj (requestToJX r) = some kvs ∧ get? kvs "command" = some (.str sc.name) ∧
      kvs.map (·.1) = "command" :: sc.fields.map (·.1) := by
  rcases r with r | ⟨c, cmd, f⟩
  · obtain ⟨sc, hsc, rest⟩ := B.requestToJ_schema r h
    exact ⟨sc, List.mem_append_left _ hsc, rest⟩
  · have hcmd : L.cmdWf cmd = true := by simp_all [requestWfX, Commands.requestWf]
    obtain ⟨sc, hsc, hwf, hfs, -⟩ := Commands.cmdWf_find hcmd
    refine ⟨sc, List.mem_append_right _ (List.mem_of_find?_eq_some hsc),
      ("command", .str (L.toVals cmd).1) :: valsToJ sc.fields (L.toVals cmd).2, ?_, ?_, ?_⟩
    · simp [cmdObj, requestToJX, requestToJL, get?, List.find?, Commands.cmdToJ, objToJ, hfs]
    · simp [get?, Commands.find_name hsc]
    · simp [valsWf_keys hwf]

/-! ## The combined description: which rules judge each command -/

/-- The names of the rules that judge command `n` of the combined service, in the order they are tried: for a base
command, the base's, then the layer's guards that judge it; for a layer command, the base's admission, the mechanism's
reference check (when the command has a `ref` field), the layer's rules that judge it, then its reference rules. -/
def rulesOfX (n : String) : List String :=
  if B.names.contains n then B.rulesOf n ++ (L.guards.filter (·.cmds.contains n)).map (·.reason)
  else B.admitRules ++ (if (L.fieldsOf n).any (·.2.isRef) then [refReason] else []) ++
    (L.rules.filter (·.cmds.contains n)).map (·.reason) ++ (L.refRules.filter (·.cmds.contains n)).map (·.reason)

/-! ## The combined service -/

/-- The base and the layer, as one service: the engine serves it, and `Service.lean` proves it. -/
abbrev service (L : Layer B) : Service where
  Ev := L.XEv
  Req := L.XReq
  St := L.XSt
  toEvent := toEventX
  toRequest := toRequestX
  toEvent_ok_iff := toEventX_ok_iff
  stream := streamX
  reqStream := reqStreamX
  toEvent_stream := toEventX_stream
  ok log e := (rejectionX log e).isNone
  rejection := rejectionX
  rejection_none_iff _ _ := by simp [Option.isNone_iff_eq_none]
  rejection_local := rejectionX_local
  init s := (B.init s, L.memory.init, [])
  step := stepX
  rejectionS := rejectionXS
  rejectionS_fold := rejectionXS_fold
  stStream st := B.stStream st.1
  stStream_init s := B.stStream_init s
  stStream_step st e := by cases e <;> simp [stepX, B.stStream_step]
  requestWf := requestWfX
  eventWf := eventWfX
  eventWf_eq e := by cases e <;> simp [eventWfX, requestWfX, toRequestX, B.eventWf_eq, Commands.evWf]
  requestToJ := requestToJX
  requestFromJ := requestFromJX
  requestFromJ_toJ := requestFromJX_toJ
  requestFromJ_wf := requestFromJX_wf
  eventToJ := eventToJX
  eventFromJ := eventFromJX
  eventFromJ_toJ := eventFromJX_toJ
  eventFromJ_wf := eventFromJX_wf
  stateToJ := stateToJX
  stateFromJ := stateFromJX
  stateFromJ_toJ := stateFromJX_toJ
  streamSJ := streamSJX
  schema := B.schema ++ L.schema
  requestFromJ_schema := requestFromJX_schema
  requestToJ_schema := requestToJX_schema
  rulesOf := rulesOfX (L := L)

/-! ## A layer is a base: towers -/

/-- **A layer, with everything below it, is a base** for the layer above: its service is `L.service`, its view of a
stream is the base's view and what the layer exposes of its memory, what it asks of every actor is what its base asks
(so admission is the bottom base's all the way up), and its names are the base's and the layer's. -/
abbrev toBase (L : Layer B) : Base where
  toService := L.service
  View := B.View × L.Exposed
  view log t := (B.view (bases log) t, L.expose (L.memory.read (evs log t)))
  view_local log s := by
    show (B.view (bases (log.filter (streamX · == s))) s, L.expose (L.memory.read (evs (log.filter (streamX · == s)) s))) = _
    rw [bases_filter, evs_filter, B.view_local]
  viewS st := (B.viewS st.1, L.expose (L.memory.view st.2.1))
  viewS_fold s log := by
    show (B.viewS (log.foldl stepX (B.init s, L.memory.init, [])).1,
      L.expose (L.memory.view (log.foldl stepX (B.init s, L.memory.init, [])).2.1)) = _
    rw [fold_stepX]; simp only [Service.fold, B.viewS_fold, L.memory.fold_view]
  admits v a := B.admits v.1 a
  admitRules := B.admitRules
  admits_named v a r h := B.admits_named v.1 a r h
  live st := B.live st.1
  requestToJ_name r := by
    rcases r with r | ⟨c, cmd, f⟩
    · obtain ⟨n, h1, h2⟩ := B.requestToJ_name r
      exact ⟨n, h1, by simp only [List.map_append]; exact List.mem_append_left _ h2⟩
    · refine ⟨(L.toVals cmd).1, ?_, ?_⟩
      · simp [requestToJX, requestToJL, cmdName, get?, List.find?, Commands.cmdToJ, keyStr_objToJ]
      · simp only [List.map_append]; exact List.mem_append_right _ (Commands.toVals_mem cmd |> List.elem_iff.mp)
  eventToJ_name e := by
    rcases e with e | x
    · obtain ⟨n, h1, h2⟩ := B.eventToJ_name e
      exact ⟨n, h1, by simp only [List.map_append]; exact List.mem_append_left _ h2⟩
    · refine ⟨L.eventOf (L.toVals (L.toRequest x).2).1, ?_, ?_⟩
      · simp [eventToJX, Commands.evToJ, keyStr_objToJ]
      · simp only [List.map_append]
        exact List.mem_append_right _ (Commands.eventOf_mem (L.toRequest x).2 |> List.elem_iff.mp)

@[simp] theorem toBase_view (L : Layer B) (log : L.XLog) (t : Id) :
    L.toBase.view log t = (B.view (bases log) t, L.expose (L.memory.read (evs log t))) := rfl
/-- **Admission composes**: what a tower asks of every actor is what the base at its bottom asks. -/
@[simp] theorem toBase_admits (L : Layer B) (v : B.View × L.Exposed) (a : Id) : L.toBase.admits v a = B.admits v.1 a := rfl
theorem toBase_service (L : Layer B) : L.toBase.toService = L.service := rfl

/-! ## Every layer keeps its base's guarantees, its own rules and its guards -/

/-- A combined log built only by accepting candidates (`Service.Valid` at `L.service`). -/
abbrev ValidX : L.XLog → Prop := L.service.Valid

/-- **Forward simulation by projection: the base's log inside a valid combined log is valid at the base.** So every
theorem proved of a valid log of the base holds of the base's events of a valid combined log: a layer cannot break what
is below it. Over a tower it applies at each level (`h.base.base`). -/
theorem ValidX.base {log : L.XLog} (h : ValidX log) : B.Valid (bases log) := by
  refine Service.Valid.project (S := L.service) baseOf (fun log e _ hok e' he => ?_) h
  cases e with
  | inr x => cases he
  | inl e =>
    simp only [baseOf, Option.some.injEq] at he; subst he
    have hn : rejectionX log (.inl e) = none := Option.isNone_iff_eq_none.mp hok
    simp only [rejectionX, Option.or_eq_none_iff] at hn
    exact (B.rejection_none_iff _ _).mp hn.1

/-- **The core's events of a valid combined log over it form a `Valid` core log.** -/
theorem ValidX.cores {L : Layer coreBase} {log : L.XLog} (h : ValidX log) : Valid (cores log) := h.base

/-- **Guards only refuse more**: a base event the base refuses after the base's events of a combined log is refused by
every layer there. -/
theorem ValidX.base_refusal_stands {pre : L.XLog} {e : B.Ev} {r : String} (hr : B.rejection (bases pre) e = some r) :
    ¬ ValidX (pre ++ [.inl e]) := by
  intro hv
  have : (rejectionX pre (.inl e)).isNone = true := Service.Valid.okAt (post := []) hv
  rw [Option.isNone_iff_eq_none] at this
  simp only [rejectionX, Option.or_eq_none_iff] at this
  rw [hr] at this; exact absurd this.1 (by simp)

/-- **Every layer event was admitted by the base**: against the base's view of its stream before it, the base refused
nothing (at the core: the stream was open and not closed; any actor is admitted, and the layer's rules say who may
act). -/
theorem ValidX.admitted {pre post : L.XLog} {x : L.Ev} (h : ValidX (pre ++ .inr x :: post)) :
    B.admits (B.view (bases pre) (L.evStream x)) (evActor x) = none := by
  have : (rejectionX pre (.inr x)).isNone = true := Service.Valid.okAt h
  rw [Option.isNone_iff_eq_none] at this
  simp only [rejectionX, Option.or_eq_none_iff] at this
  exact this.1

/-- What the combined rejection of a layer event comes to when it is accepted: admitted, references in range, every
rule, every reference rule. -/
theorem ValidX.inr_parts {pre post : L.XLog} {x : L.Ev} (h : ValidX (pre ++ .inr x :: post)) :
    B.admits (B.view (bases pre) (L.evStream x)) (evActor x) = none ∧
    refCheck (onStreamX pre (L.evStream x)).length x = none ∧
    L.rejectionL (B.view (bases pre) (L.evStream x)) (L.memory.read (evs pre (L.evStream x))) x = none ∧
    L.rejectionR (fun n => nth ((onStreamX pre (L.evStream x)).map tagX) n) x = none := by
  have : (rejectionX pre (.inr x)).isNone = true := Service.Valid.okAt h
  rw [Option.isNone_iff_eq_none] at this
  simpa only [rejectionX, Option.or_eq_none_iff] using this

/-- **A layer event of a valid combined log held every layer rule** against the base's view of its stream and the
memory of the stream's layer events before it. A layer proves its own theorems from this. -/
theorem ValidX.holds {pre post : L.XLog} {x : L.Ev} (h : ValidX (pre ++ .inr x :: post))
    {r : Layer.Rule B.View L.memory.V L.Ev} (hr : r ∈ L.rules) :
    r.holds (B.view (bases pre) (L.evStream x)) (L.memory.read (evs pre (L.evStream x))) x = true :=
  rejectionL_none.mp h.inr_parts.2.2.1 r hr

/-- **The rule named `n` held for a layer event of a valid combined log**, by its name (found by `rfl`). -/
theorem ValidX.holdsNamed {pre post : L.XLog} {x : L.Ev} (h : ValidX (pre ++ .inr x :: post)) (n : String)
    {r : Layer.Rule B.View L.memory.V L.Ev} (hr : L.rules.find? (·.reason == n) = some r := by rfl) :
    r.holds (B.view (bases pre) (L.evStream x)) (L.memory.read (evs pre (L.evStream x))) x = true :=
  h.holds (List.mem_of_find?_eq_some hr)

/-- **A base event of a valid combined log held every guard** of the layer. -/
theorem ValidX.guardHolds {pre post : L.XLog} {e : B.Ev} (h : ValidX (pre ++ .inl e :: post))
    {g : Layer.Rule B.View L.memory.V B.Ev} (hg : g ∈ L.guards) :
    g.holds (B.view (bases pre) (B.stream e)) (L.memory.read (evs pre (B.stream e))) e = true := by
  have : (rejectionX pre (.inl e)).isNone = true := Service.Valid.okAt h
  have := (Option.or_eq_none_iff.mp (Option.isNone_iff_eq_none.mp this)).2
  exact rejectionG_none.mp this g hg

/-- **The guard named `n` held for a base event of a valid combined log**, by its name (found by `rfl`). -/
theorem ValidX.guardHoldsNamed {pre post : L.XLog} {e : B.Ev} (h : ValidX (pre ++ .inl e :: post)) (n : String)
    {g : Layer.Rule B.View L.memory.V B.Ev} (hg : L.guards.find? (·.reason == n) = some g := by rfl) :
    g.holds (B.view (bases pre) (B.stream e)) (L.memory.read (evs pre (B.stream e))) e = true :=
  h.guardHolds (List.mem_of_find?_eq_some hg)

/-- **A reference rule of a layer event of a valid combined log held**, reading the tags of the stream's events before
it. -/
theorem ValidX.refHolds {pre post : L.XLog} {x : L.Ev} (h : ValidX (pre ++ .inr x :: post))
    {r : Layer.RefRule L.Ev} (hr : r ∈ L.refRules) :
    r.holds (fun n => nth ((onStreamX pre (L.evStream x)).map tagX) n) x = true :=
  rejectionR_none.mp h.inr_parts.2.2.2 r hr

/-- **The reference rule named `n` held**, by its name (found by `rfl`). -/
theorem ValidX.refHoldsNamed {pre post : L.XLog} {x : L.Ev} (h : ValidX (pre ++ .inr x :: post)) (n : String)
    {r : Layer.RefRule L.Ev} (hr : L.refRules.find? (·.reason == n) = some r := by rfl) :
    r.holds (fun n => nth ((onStreamX pre (L.evStream x)).map tagX) n) x = true :=
  h.refHolds (List.mem_of_find?_eq_some hr)

/-! ## References, for every layer -/

/-- **`ref_earlier`**: every reference of a layer event in a valid log names an event earlier in the same stream: a
position below the event's own (`(onStreamX pre s).length`), holding an event of that stream that came before it. So
references are well founded: none points forward, to itself, or to another stream, and none forms a cycle. -/
theorem ValidX.ref_earlier {pre post : L.XLog} {x : L.Ev} (h : ValidX (pre ++ .inr x :: post)) {n : Nat}
    (hn : n ∈ evRefs x) : n < (onStreamX pre (L.evStream x)).length ∧
      ∃ y, (onStreamX pre (L.evStream x))[n]? = some y ∧ y ∈ pre ∧ streamX y = L.evStream x := by
  have hc := h.inr_parts.2.1
  unfold refCheck at hc
  split at hc
  · rename_i hall
    have hlt : n < (onStreamX pre (L.evStream x)).length := by
      have := List.all_eq_true.mp hall n hn; simpa using this
    refine ⟨hlt, (onStreamX pre (L.evStream x))[n], List.getElem?_eq_getElem hlt, ?_⟩
    have hm := List.getElem_mem hlt
    simp only [onStreamX, List.mem_filter, beq_iff_eq] at hm
    exact hm
  · cases hc

/-- **`ref_target_fixed`**: the event at a position of a stream never changes, whatever is appended. -/
theorem ref_target_fixed {log : L.XLog} {s : Id} {n : Nat} {y : L.XEv} (h : (onStreamX log s)[n]? = some y)
    (post : L.XLog) : (onStreamX (log ++ post) s)[n]? = some y := by
  have hlt : n < (onStreamX log s).length := by
    rcases Nat.lt_or_ge n (onStreamX log s).length with h1 | h1
    · exact h1
    · rw [List.getElem?_eq_none h1] at h; cases h
  simp only [onStreamX, List.filter_append] at h hlt ⊢
  rw [List.getElem?_append_left hlt]; exact h

/-- **`ref_target_valid`**: the event a reference names is an accepted event of the stream: the log before the
referring event is `p1 ++ y :: p2` with `p1 ++ [y]` valid, so every theorem of accepted events holds of `y`. -/
theorem ValidX.ref_target_valid {pre post : L.XLog} {x : L.Ev} (h : ValidX (pre ++ .inr x :: post)) {n : Nat}
    (hn : n ∈ evRefs x) : ∃ y p1 p2, (onStreamX pre (L.evStream x))[n]? = some y ∧ pre = p1 ++ y :: p2 ∧
      streamX y = L.evStream x ∧ ValidX (p1 ++ [y]) := by
  obtain ⟨-, y, hy, hm, hs⟩ := h.ref_earlier hn
  obtain ⟨p1, p2, rfl⟩ := List.append_of_mem hm
  exact ⟨y, p1, p2, hy, rfl, hs, Service.Valid.prefix h (p1 ++ [y]) (p2 ++ .inr x :: post) (by simp)⟩

/-- **A layer event is accepted after a valid log iff** the base admits its actor, its references name events already
in the stream, and every rule and reference rule holds for it. -/
theorem ValidX.snoc_inr_iff {pre : L.XLog} (h : ValidX pre) {x : L.Ev} :
    ValidX (pre ++ [.inr x]) ↔ B.admits (B.view (bases pre) (L.evStream x)) (evActor x) = none ∧
      refCheck (onStreamX pre (L.evStream x)).length x = none ∧
      (∀ r ∈ L.rules, r.holds (B.view (bases pre) (L.evStream x)) (L.memory.read (evs pre (L.evStream x))) x = true) ∧
      ∀ r ∈ L.refRules, r.holds (fun n => nth ((onStreamX pre (L.evStream x)).map tagX) n) x = true := by
  constructor
  · intro hv
    obtain ⟨a, b, c, d⟩ := ValidX.inr_parts (post := []) hv
    exact ⟨a, b, rejectionL_none.mp c, rejectionR_none.mp d⟩
  · rintro ⟨ha, hc, hr, hq⟩
    exact Service.Valid.snoc h (Option.isNone_iff_eq_none.mpr (Option.or_eq_none_iff.mpr
      ⟨ha, Option.or_eq_none_iff.mpr ⟨hc, Option.or_eq_none_iff.mpr ⟨rejectionL_none.mpr hr, rejectionR_none.mpr hq⟩⟩⟩))

/-- **A base event is accepted after a valid log iff the base accepts it and every guard holds for it.** -/
theorem ValidX.snoc_inl_iff {pre : L.XLog} (h : ValidX pre) {e : B.Ev} :
    ValidX (pre ++ [.inl e]) ↔ B.rejection (bases pre) e = none ∧
      ∀ g ∈ L.guards, g.holds (B.view (bases pre) (B.stream e)) (L.memory.read (evs pre (B.stream e))) e = true := by
  constructor
  · intro hv
    have : (rejectionX pre (.inl e)).isNone = true := Service.Valid.okAt (post := []) hv
    have := Option.or_eq_none_iff.mp (Option.isNone_iff_eq_none.mp this)
    exact ⟨this.1, rejectionG_none.mp this.2⟩
  · rintro ⟨hb, hg⟩
    refine Service.Valid.snoc h (Option.isNone_iff_eq_none.mpr ?_)
    exact Option.or_eq_none_iff.mpr ⟨hb, rejectionG_none.mpr hg⟩

end Layer

/-- `ValidX.base` from `L.service.Valid`: `h.base.base` goes down two levels of a tower. -/
theorem Service.Valid.base {B : Base} {L : Layer B} {log : L.XLog} (h : L.service.Valid log) :
    B.Valid (Layer.bases log) := Layer.ValidX.base h

/-! ## The core's guarantees, for every layer on it -/

namespace Layer
variable {L : Layer coreBase}

/-- The actor of a combined event over the core. -/
def actorX : L.XEv → Id
  | .inl e => e.actor
  | .inr x => evActor x

/-- **Every layer event is on an open, unclosed stream**, in a valid combined log over the core. -/
theorem ValidX.admitted_open {pre post : L.XLog} {x : L.Ev} (h : ValidX (pre ++ .inr x :: post)) :
    Past.opened (Layer.cores pre) (L.evStream x) = true ∧ Past.closed (Layer.cores pre) (L.evStream x) = false := by
  simpa [Past.view] using (View.admits_none (a := evActor x)).mp h.admitted

/-- **In every layer, every close is by the stream's opener**: in a valid combined log over the core, the actor of a
close is the opener of its stream, as the core's events before it say. A layer can only refuse more, so no layer can
let anyone else close a stream. -/
theorem ValidX.close_by_opener {pre post : L.XLog} {a t : Id} {m : Meta}
    (h : ValidX (pre ++ .inl (Event.streamClosed a t m) :: post)) : Past.opener (Layer.cores pre) t = some a := by
  have hc : Valid (Layer.cores pre ++ Event.streamClosed a t m :: Layer.cores post) := by
    simpa [Layer.cores] using h.cores
  exact Provenstream.close_by_opener hc

/-- **In every layer, a stream's opener never changes**: in a valid combined log over the core, two openings of a
stream are by one opener, with one revision. -/
theorem ValidX.opener_fixed {log : L.XLog} (h : ValidX log) {t a₁ a₂ : Id} {u₁ u₂ : String} {m₁ m₂ : Meta}
    (h₁ : .inl (Event.streamOpened a₁ t u₁ m₁) ∈ log) (h₂ : .inl (Event.streamOpened a₂ t u₂ m₂) ∈ log) :
    a₁ = a₂ ∧ u₁ = u₂ :=
  Provenstream.opener_fixed h.cores (mem_bases.mpr h₁) (mem_bases.mpr h₂)

/-- **Nothing is appended after a close**, by the core or by any layer: in a valid combined log over the core, no event
after a stream's close is on that stream. -/
theorem ValidX.close_final {pre mid post : L.XLog} {a t : Id} {m : Meta} {x : L.XEv}
    (h : ValidX (pre ++ .inl (Event.streamClosed a t m) :: mid ++ x :: post)) : streamX x ≠ t := by
  cases x with
  | inl e =>
    have hc : Valid (Layer.cores pre ++ Event.streamClosed a t m :: Layer.cores mid ++ e :: Layer.cores post) := by
      simpa [Layer.cores, List.append_assoc] using h.cores
    exact Provenstream.close_final hc
  | inr x =>
    intro hs
    have h' : ValidX ((pre ++ .inl (Event.streamClosed a t m) :: mid) ++ .inr x :: post) := by
      simpa [List.append_assoc] using h
    have := (ValidX.admitted_open h').2
    simp only [streamX_inr] at hs
    rw [hs] at this
    simp [Past.closed, closes, List.any_append] at this

/-- **No layer can change a stream's proof revision**: in a valid combined log over the core, every opening of a
stream carries the revision of the core's events. -/
theorem ValidX.proof_revision_unique {log : L.XLog} (h : ValidX log) {a t : Id} {u : String}
    {m : Meta} (hc : .inl (Event.streamOpened a t u m) ∈ log) : proofRevision (Layer.cores log) t = some u :=
  Provenstream.proof_revision_unique h.cores (mem_bases.mpr hc)

end Layer

end Provenstream
