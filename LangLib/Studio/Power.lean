import Lean.Data.Json

/-!
# The Power export (`studio/power-schema.md`)

What every rule-based module (Nen, Magic, Death Note, ...) hands the Studio's
Power view: its moves in story order, each with every precondition evaluated,
the state after it, and the counterfactual runs it proves fail. This file is
only the shape and its JSON; each module fills it from its own Lean (for Nen,
`World/Examples/FightPower.lean`), and `langlib power <dir>` prints it.
-/

namespace LangLib.Studio.Power
open Lean

/-- One precondition of a move, evaluated. `why` is what the module says when it fails. -/
structure Check where
  id : String
  kind : String
  label : String
  pass : Bool
  why : String
  deriving Inhabited

structure Field where
  key : String
  label : String
  value : Json

structure PMark where
  kind : String
  by_ : String
  via : String
  note : String := ""

structure PActor where
  id : String
  status : List String := []
  resources : List (String × Nat) := []
  fields : List Field := []
  marks : List PMark := []

structure Active where
  by_ : String
  what : String
  on : List String := []

structure Relation where
  src : String
  dst : String
  kind : String
  label : String

structure Clock where
  id : String
  label : String
  actor : String
  target : String
  start : Nat
  due : Nat
  status : String

structure Knows where
  who : String
  of_ : String := ""
  what : String
  holds : Bool
  true_ : Bool

structure PState where
  actors : List PActor
  active : List Active := []
  relations : List Relation := []
  clocks : List Clock := []
  knowledge : List Knows := []

structure Move where
  i : Nat
  para : String
  at_ : Option Nat := none
  actor : String
  kind : String
  text : String
  raw : String
  targets : List String := []
  t : Option Nat := none
  ok : Bool
  why : String
  checks : List Check
  state : PState

structure Counterfactual where
  id : String
  label : String
  theorem_ : String
  change : String
  move : Option Nat
  para : String
  why : String
  checks : List Check

structure ActorDef where
  id : String
  name : String
  kind : String
  of_ : Option String := none

structure Export where
  system : String
  title : String
  story : String
  source : String
  actors : List ActorDef
  resources : List (String × String × List (String × Nat)) := []
  glossary : List (String × String) := []
  start : PState
  moves : List Move
  counterfactuals : List Counterfactual := []

/-- The first failing check agrees with the module's verdict and its words. -/
def agrees (cs : List Check) (ok : Bool) (why : String) : Bool :=
  match cs.find? (!·.pass) with
  | some c => !ok && c.why == why
  | none => ok

def Check.toJson (c : Check) : Json :=
  Json.mkObj [("id", c.id), ("kind", c.kind), ("label", c.label), ("pass", c.pass), ("why", c.why)]

def PState.toJson (s : PState) : Json :=
  Json.mkObj [
    ("actors", Json.mkObj (s.actors.map fun a => (a.id, Json.mkObj [
      ("status", Lean.toJson a.status),
      ("resources", Json.mkObj (a.resources.map fun (k, n) => (k, Lean.toJson n))),
      ("fields", Json.arr (a.fields.map fun f => Json.mkObj [("key", f.key), ("label", f.label), ("value", f.value)]).toArray),
      ("marks", Json.arr (a.marks.map fun m => Json.mkObj [("kind", m.kind), ("by", m.by_), ("via", m.via), ("note", m.note)]).toArray)]))),
    ("active", Json.arr (s.active.map fun x => Json.mkObj [("by", x.by_), ("what", x.what), ("on", Lean.toJson x.on)]).toArray),
    ("relations", Json.arr (s.relations.map fun r => Json.mkObj [("from", r.src), ("to", r.dst), ("kind", r.kind), ("label", r.label)]).toArray),
    ("clocks", Json.arr (s.clocks.map fun c => Json.mkObj [("id", c.id), ("label", c.label), ("actor", c.actor),
      ("target", c.target), ("start", c.start), ("due", c.due), ("status", c.status)]).toArray),
    ("knowledge", Json.arr (s.knowledge.map fun k => Json.mkObj [("who", k.who), ("of", k.of_), ("what", k.what),
      ("holds", k.holds), ("true", k.true_)]).toArray)]

def optNat : Option Nat → Json | some n => Lean.toJson n | none => Json.null

def Export.toJson (x : Export) : Json :=
  let checks (cs : List Check) := Json.arr (cs.map Check.toJson).toArray
  let failure := x.moves.find? (!·.ok)
  Json.mkObj [
    ("schema", 1), ("system", x.system), ("title", x.title), ("story", x.story), ("source", x.source),
    ("valid", failure.isNone),
    ("failure", match failure with | some m => Json.mkObj [("move", m.i), ("why", m.why)] | none => Json.null),
    ("actors", Json.arr (x.actors.map fun a => Json.mkObj ([("id", Lean.toJson a.id), ("name", Lean.toJson a.name), ("kind", Lean.toJson a.kind)] ++
      (match a.of_ with | some o => [("of", Lean.toJson o)] | none => []))).toArray),
    ("resources", Json.arr (x.resources.map fun (id, label, max) => Json.mkObj [("id", id), ("label", label),
      ("max", Json.mkObj (max.map fun (k, n) => (k, Lean.toJson n)))]).toArray),
    ("glossary", Json.mkObj (x.glossary.map fun (k, v) => (k, Lean.toJson v))),
    ("start", x.start.toJson),
    ("moves", Json.arr (x.moves.map fun m => Json.mkObj [
      ("i", m.i), ("para", m.para), ("at", optNat m.at_), ("actor", m.actor), ("kind", m.kind), ("text", m.text),
      ("raw", m.raw), ("targets", Lean.toJson m.targets), ("t", optNat m.t), ("ok", m.ok), ("why", m.why),
      ("checks", checks m.checks), ("agrees", agrees m.checks m.ok m.why), ("state", m.state.toJson)]).toArray),
    ("counterfactuals", Json.arr (x.counterfactuals.map fun c => Json.mkObj [
      ("id", c.id), ("label", c.label), ("theorem", c.theorem_), ("change", c.change), ("move", optNat c.move),
      ("para", c.para), ("why", c.why), ("checks", checks c.checks)]).toArray)]

end LangLib.Studio.Power
