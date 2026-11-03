# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""`provenstream init <name>`: a layer project on the core's interface, ready to `provenstream check` and `build`.

The project is a Lake package requiring provenstream (by path to a checkout, or by git URL and commit), with one layer
(a stream of notes: any principal adds a note to an open stream, once per id), one theorem, worked examples, and the engine.
"""
from __future__ import annotations
import json, os, re
from typing import Optional

from .project import REPO, TOOLCHAIN

LAYER = '''-- {name}: a layer on the provenstream core.
import Provenstream.Interface

/-!
# {ns}: notes on a stream

`note.add {{stream_id, note_id, meta?}}` → `note.added`: any principal adds a note to an open stream, its id new on the
stream. The core admits the event first (the stream exists and is not closed; it asks nothing of the actor); then the
rule `note_id_must_be_new`. A rule that reads `v.opener` (the stream's opener) would say who may add one.
-/

namespace {ns}
open Provenstream Provenstream.Layer

inductive NoteEvent where
  | added (actor stream note : Id) («meta» : Meta)
  deriving DecidableEq

inductive NoteCommand where
  | add (stream note : Id) («meta» : Meta)
  deriving DecidableEq

def marks : NoteEvent → List Fact
  | .added _ _ n _ => [("note", n)]

abbrev layer : Layer where
  Cmd := NoteCommand
  Ev := NoteEvent
  toRequest | .added a t n m => (a, .add t n m)
  ofRequest | (a, .add t n m) => .added a t n m
  stream | .add t .. => t
  schema := [{{ name := "note.add", event := "note.added", who := some "anyone, on an open stream",
               fields := [("stream_id", .uuid), ("note_id", .uuid), ("meta", .metaOpt)] }}]
  toVals | .add t n m => ("note.add", [.s t, .s n, .m m])
  ofVals
    | "note.add", [.s t, .s n, .m m] => some (.add t n m)
    | _, _ => none
  memory := Memory.facts marks
  rules := [⟨"note_id_must_be_new", ["note.add"], fun _ w e => match e with | .added _ _ n _ => !w "note" n⟩]

end {ns}
'''

THEOREMS = '''import {ns}.Layer

namespace {ns}
open Provenstream Provenstream.Layer

/-- Every note is added to an open, unclosed stream (the core's admission, inherited). -/
theorem note_on_open_stream {{pre post : layer.XLog}} {{a t n : Id}} {{m : Meta}}
    (h : ValidX (pre ++ .inr (NoteEvent.added a t n m) :: post)) :
    Past.opened (cores pre) t = true ∧ Past.closed (cores pre) t = false := by
  simpa using h.admitted_open

end {ns}
'''

EXAMPLES = '''import {ns}.Theorems

namespace {ns}.Examples
open Provenstream Provenstream.Layer {ns}

def url : String := "https://example.org/{name}/commit/0123456789abcdef0123456789abcdef01234567"
def ann : Id := "a0000000-0000-4000-8000-000000000001"
def dee : Id := "d0000000-0000-4000-8000-000000000004"
def S : Id := "50000000-0000-7000-8000-000000000001"
def N : Id := "60000000-0000-7000-8000-000000000001"

abbrev Sv := layer.service

def story : List (Sv.Req × Option String) :=
  [ (.inr (ann, .add S N none, []), some "stream_must_exist"),
    (.inl (ann, .streamOpen url none, [S]), none),
    (.inr (dee, .add S N (some "hello"), []), none),
    (.inr (ann, .add S N none, []), some "note_id_must_be_new"),
    (.inl (dee, .streamClose S none, []), some "only_opener_can_close"),
    (.inl (ann, .streamClose S none, []), none) ]

def allOk : Bool :=
  (Sv.run (story.map (·.1))).2.zip story |>.all fun (x, (_, want)) =>
    match x, want with
    | .accepted _, none => true
    | .rejected r, some r' => r == r'
    | _, _ => false

#guard allOk

end {ns}.Examples
'''

MAIN = '''import {ns}.Examples
import Provenstream.Engine.Step
import {ns}Revision

def main (args : List String) : IO UInt32 :=
  Provenstream.Engine.Layered.mainAt {ns}.layer "{engine}" (pure {ns}.Examples.allOk) {ns}.built args
'''

LAKEFILE = '''name = "{name}"
version = "0.1.0"
defaultTargets = ["{ns}", "{engine}"]

{require}

[[lean_lib]]
name = "{ns}"

[[lean_lib]]
name = "{ns}Revision"

[[lean_exe]]
name = "{engine}"
root = "Main"
'''


def namespace_of(name: str) -> str:
    parts = re.split(r"[^A-Za-z0-9]+", name)
    ns = "".join(p[:1].upper() + p[1:] for p in parts if p)
    if not ns or not ns[0].isalpha():
        raise ValueError("%r: a project name starts with a letter" % name)
    return ns


def init(name: str, directory: Optional[str] = None, core_path: Optional[str] = None,
         core_git: Optional[str] = None, core_rev: Optional[str] = None) -> str:
    ns = namespace_of(name)
    d = os.path.abspath(directory or name)
    if os.path.exists(d) and os.listdir(d):
        raise FileExistsError("%s exists and is not empty" % d)
    engine = re.sub(r"[^a-z0-9]+", "-", name.lower()).strip("-") + "-engine"
    if core_git:
        if not core_rev:
            raise ValueError("--core-git needs --core-rev (a commit): an engine is built from pinned sources")
        require = '[[require]]\nname = "provenstream"\ngit = "%s"\nrev = "%s"' % (core_git, core_rev)
    else:
        core = core_path or REPO
        if core is None:
            raise ValueError("no provenstream checkout found: pass --core PATH, --core-git URL --core-rev COMMIT, or set "
                             "PROVENSTREAM_HOME")
        require = '[[require]]\nname = "provenstream"\npath = "%s"' % os.path.abspath(core)
    os.makedirs(os.path.join(d, ns))
    files = {
        "lakefile.toml": LAKEFILE.format(name=name, ns=ns, engine=engine, require=require),
        "lean-toolchain": TOOLCHAIN + "\n",
        os.path.join(ns, "Layer.lean"): LAYER.format(name=name, ns=ns),
        os.path.join(ns, "Theorems.lean"): THEOREMS.format(ns=ns),
        os.path.join(ns, "Examples.lean"): EXAMPLES.format(ns=ns, name=name),
        ns + ".lean": "import %s.Layer\nimport %s.Theorems\nimport %s.Examples\n" % (ns, ns, ns),
        "Main.lean": MAIN.format(ns=ns, engine=engine),
        ".gitignore": ".lake/\n/%sRevision.lean\n" % ns,
        "provenstream.json": json.dumps({"name": name, "engine": engine, "namespaces": [ns],
                                        "layer_modules": ["%s/Layer.lean" % ns, "%s/Theorems.lean" % ns,
                                                          "%s/Examples.lean" % ns],
                                        "audit_roots": ["%s.layer" % ns], "revision_module": "%sRevision.lean" % ns,
                                        "revision_def": "%s.built" % ns}, indent=2) + "\n",
    }
    for rel, text in files.items():
        with open(os.path.join(d, rel), "w", encoding="utf-8") as f:
            f.write(text)
    return d
