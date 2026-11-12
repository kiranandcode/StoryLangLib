import LangLib.Basic
import LangLib.Render
import LangLib.Story.Scene

/-!
# From annotated text to scene events

Reads events off a checked langlib document. Each phrase whose head child is a
VERB leaf is a clause; its participants come from the reference layer:

* subject: the `nsubj` child of the nearest enclosing clause (so coordinated
  verb phrases share it, and a pronoun subject is already resolved by its `ref`);
* object: the `obj` child's entity;
* obliques: each `obl` prepositional phrase, as (preposition, entity).

A lexicon maps a verb's lemma and these participants to a scene event, and a
resolver maps entity ids to the scene's characters, places and objects. Every
event keeps the token span of its verb, so a scene fact can be traced back to
the words that asserted it.
-/

namespace LangLib.Scene

/-- A clause: its verb and participants, by entity id. -/
structure Clause where
  verb : String
  /-- token index of the verb -/
  at_ : Nat
  subj : Option EntityId := none
  obj : Option EntityId := none
  obls : List (String × EntityId) := []
  /-- the object's head noun, when it is not an entity ("a kiss") -/
  objNoun : Option String := none
  /-- obliques whose noun is not an entity: (preposition, noun) -/
  oblNouns : List (String × String) := []
  /-- token index of the verb of this clause's complement (`xcomp`/`ccomp`) -/
  comp : Option Nat := none
  /-- this clause is the complement of another, not an event of its own -/
  embedded : Bool := false
  /-- words of the clause's (and its enclosing clause's) adverbials: "meanwhile",
  "an hour earlier" -/
  advs : List String := []
  deriving Repr, Inhabited

private def refOf : Tree → Option EntityId
  | .leaf w => w.ref
  | .node i kids => i.ref <|> (kids.findSome? fun
      | .node j _ => if j.cat == .NP then j.ref else none
      | .leaf w => w.ref)

private def roleOf : Tree → Option Role
  | .leaf w => w.role
  | .node i _ => i.role

private def headVerb : List Tree → Option Word
  | kids => kids.findSome? fun
    | .leaf w => if w.upos == .VERB && w.role == some .head then some w else none
    | _ => none

private def oblique : Tree → Option (String × EntityId)
  | t@(.node i kids) =>
    if i.cat == .PP then
      let prep := kids.findSome? fun
        | .leaf w => if w.role == some .case then some w.form.toLower else none
        | _ => none
      match prep, (kids.filter (roleOf · == some .head)).findSome? refOf with
      | some p, some e => some (p, e)
      | _, _ => none
    else (refOf t).map ("", ·)
  | .leaf w => w.ref.map ("", ·)

private partial def headNoun : Tree → Option String
  | .leaf w => if w.upos == .NOUN || w.upos == .PROPN then some (w.lemma.getD w.form).toLower else none
  | .node _ kids => kids.findSome? fun
    | t@(.leaf w) => if w.role == some .head then headNoun t else none
    | t@(.node i _) => if i.role == some .head then headNoun t else none

private def obliqueNoun : Tree → Option (String × String)
  | t@(.node i kids) =>
    if i.cat == .PP && (refOf t).isNone then
      let prep := kids.findSome? fun
        | .leaf w => if w.role == some .case then some w.form.toLower else none
        | _ => none
      match prep, (kids.filter (roleOf · == some .head)).findSome? headNoun with
      | some p, some n => some (p, n)
      | _, _ => none
    else none
  | .leaf _ => none

private def words (t : Tree) : List String := t.leaves.map (·.form.toLower)

private def isComp (t : Tree) : Bool := roleOf t == some .xcomp || roleOf t == some .ccomp

/-- Clauses of a tree, left to right, with the subject inherited from `subj`. -/
partial def _root_.LangLib.Tree.clauses (t : Tree) (subj : Option EntityId) (start : Nat)
    (embedded : Bool := false) (advs : List String := []) : List Clause × Nat :=
  match t with
  | .leaf _ => ([], start + 1)
  | .node i kids =>
    let subj := if i.cat == .S || i.cat == .SBAR then
        ((kids.find? (roleOf · == some .nsubj)).bind refOf) <|> subj
      else subj
    let advs := advs ++ (kids.filter fun k =>
        roleOf k == some .advmod || (roleOf k == some .obl && (refOf k).isNone &&
          k.leaves.all (·.upos != .ADP))).flatMap words
    -- token offset of each child
    let (offs, stop) := kids.foldl (fun (acc, p) k => (acc ++ [p], p + k.render.length))
      (([] : List Nat), start)
    let here := match headVerb kids with
      | some w =>
        let at_ := ((kids.zip offs).findSome? fun (k, o) => match k with
          | .leaf v => if v.form == w.form && v.role == some .head then some o else none
          | _ => none).getD start
        let objT := kids.find? (roleOf · == some .obj)
        let compAt := (kids.zip offs).findSome? fun (k, o) =>
          if isComp k then ((k.clauses subj o true).1.head?).map (·.at_) else none
        [{ verb := (w.lemma.getD w.form).toLower, at_, subj,
           obj := objT.bind refOf,
           objNoun := if (objT.bind refOf).isNone then objT.bind headNoun else none,
           obls := (kids.filter (roleOf · == some .obl)).filterMap oblique,
           oblNouns := (kids.filter (roleOf · == some .obl)).filterMap obliqueNoun,
           comp := compAt, embedded, advs : Clause }]
      | none => []
    let inner := (kids.zip offs).flatMap fun (k, o) =>
      (k.clauses subj o (embedded || isComp k)
        (if isComp k then [] else advs)).1
    (here ++ inner, stop)

def _root_.LangLib.Doc.clauses (d : Doc) : List Clause :=
  (d.sentences.foldl (fun (acc, p) s =>
    let (cs, p') := s.tree.clauses none p
    (acc ++ cs, p')) (([] : List Clause), 0)).1

variable {C P O : Type}

/-- How entity ids name the scene's characters, places and objects. -/
structure Resolver (C P O : Type) where
  char : EntityId → Option C
  place : EntityId → Option P
  obj : EntityId → Option O

private def obl (c : Clause) (preps : List String) : Option EntityId :=
  (c.obls.find? fun (p, _) => preps.contains p).map (·.2)

/-- The verb lexicon: which clauses are which scene events. -/
def Clause.event (R : Resolver C P O) (c : Clause) : Option (Event C P O) := do
  let s ← c.subj >>= R.char
  match c.verb with
  | "go" | "slip" | "walk" | "run" | "creep" | "return" =>
    return .move s (← obl c ["to", "into", "toward", "towards"] >>= R.place)
  | "take" | "grab" =>
    match c.obj >>= R.obj with
    | some o => return .take s o
    | none => return .grab s (← c.obj >>= R.char)
  | "hide" => return .hide s (← c.obj >>= R.obj)
  | "shout" | "yell" | "scream" => return .shout s (← obl c ["at"] >>= R.char)
  | "gag" => return .gag s (← c.obj >>= R.char)
  | "drink" => return .drink s
  | _ => none

/-- Events of a document, each with the clause it came from. -/
def _root_.LangLib.Doc.events (R : Resolver C P O) (d : Doc) : List (Clause × Event C P O) :=
  d.clauses.filterMap fun c => (c.event R).map (c, ·)

end LangLib.Scene
