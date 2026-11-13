import Lean.Data.Json
import LangLib.Studio.World

/-!
# Reading a story file

`story.json` names everything by id; events are one-line strings, one verb
and its arguments:

```
move theo roof          take mara note          give theo kiran note
tell mara kiran theoLikesMara                   lie mara kiran !maraReadNote
notice mara noteForMara assumed                 realise kiran noteForKiran
flirt theo kiran        confide theo kiran      argue kiran mara
askAct theo kiran kiss  agree kiran theo kiss   withdraw kiran theo kiss
act kiran theo kiss     ask kiran theo noteForKiran
answer theo kiran noteForKiran                  hint kiran theo kiranLikesTheo
sarcasm theo kiran theoLikesKiran               promise theo kiran at(theo,roof)
adopt theo at(theo,roof)                        intend theo roofPlan
```

A literal is an atom id, `!` for its denial, or a built-in fact:
`at(c,p)`, `objAt(o,p)`, `holds(c,o)`, `did(a,b,act)`. Evidence is one of
`seen sensed inferred assumed rumour self told:c relayed:c`.
-/

namespace LangLib.Studio
open Lean LangLib.World

def _root_.LangLib.World.Trait.ofString? : String → Option Trait
  | "timid" => some .timid | "shy" => some .shy | "brash" => some .brash
  | "confident" => some .confident | "cautious" => some .cautious | "romantic" => some .romantic
  | "loyal" => some .loyal | "proud" => some .proud | "dominant" => some .dominant
  | "submissive" => some .submissive | "honest" => some .honest | "secretive" => some .secretive
  | "gullible" => some .gullible | "skeptical" => some .skeptical | "paranoid" => some .paranoid
  | "stubborn" => some .stubborn | "openMinded" => some .openMinded | _ => none

def _root_.LangLib.World.Value.ofString? : String → Option Value
  | "safety" => some .safety | "loyalty" => some .loyalty | "pride" => some .pride
  | "desire" => some .desire | "duty" => some .duty | "honesty" => some .honesty
  | "power" => some .power | "curiosity" => some .curiosity | _ => none

def _root_.LangLib.World.Act.ofString? : String → Option Act
  | "holdHands" => some .holdHands | "kiss" => some .kiss | "touch" => some .touch
  | "undress" => some .undress | "sex" => some .sex | _ => none

def _root_.LangLib.World.Act.name : Act → String
  | .holdHands => "holdHands" | .kiss => "kiss" | .touch => "touch"
  | .undress => "undress" | .sex => "sex"

def _root_.LangLib.World.Dim.ofString? : String → Option Dim
  | "trust" => some .trust | "attraction" => some .attraction
  | "affection" => some .affection | "tension" => some .tension | _ => none

def _root_.LangLib.World.Dim.name : Dim → String
  | .trust => "trust" | .attraction => "attraction" | .affection => "affection" | .tension => "tension"

def dims : List Dim := [.trust, .attraction, .affection, .tension]

/-- Names, for reading ids and printing them back. -/
structure Names where
  chars : List String
  places : List String
  objects : List String
  atoms : List String
  plans : List String := []

def Spec.names (s : Spec) : Names :=
  { chars := s.chars.map (·.id), places := s.places, objects := s.objects,
    atoms := s.atoms.map (·.id), plans := s.plans.map (·.id) }

private def idx (kind : String) (xs : List String) (x : String) : Except String Nat :=
  match xs.idxOf? x with
  | some i => pure i
  | none => throw s!"unknown {kind} \"{x}\" (known: {", ".intercalate xs})"

def Names.ch (n : Names) := idx "character" n.chars
def Names.pl (n : Names) := idx "place" n.places
def Names.ob (n : Names) := idx "object" n.objects

private def args (s : String) (pre : String) : Option (List String) :=
  if s.startsWith pre && s.endsWith ")" then
    some ((((s.drop pre.length).dropEnd 1).toString.splitOn ",").map (·.trimAscii.toString))
  else none

def Names.fact (n : Names) (s : String) : Except String Fact := do
  if let some [c, p] := args s "at(" then return .at_ (← n.ch c) (← n.pl p)
  if let some [o, p] := args s "objAt(" then return .objAt (← n.ob o) (← n.pl p)
  if let some [c, o] := args s "holds(" then return .holds (← n.ch c) (← n.ob o)
  if let some [a, b, x] := args s "did(" then
    let some x := Act.ofString? x | throw s!"unknown act \"{x}\""
    return .did (← n.ch a) (← n.ch b) x
  return .atom (← idx "fact" n.atoms s)

def Names.lit (n : Names) (s : String) : Except String (Fact × Bool) :=
  if s.startsWith "!" then return (← n.fact (s.drop 1).toString, false)
  else return (← n.fact s, true)

def Names.evid (n : Names) (s : String) : Except String (Evid Nat) :=
  match s with
  | "seen" => pure .seen | "sensed" => pure .sensed | "inferred" => pure .inferred
  | "assumed" => pure .assumed | "rumour" => pure .rumour | "self" => pure .self
  | _ =>
    if s.startsWith "told:" then return .told (← n.ch (s.drop 5).toString)
    else if s.startsWith "relayed:" then return .relayed (← n.ch (s.drop 8).toString)
    else throw s!"unknown evidence \"{s}\""

private def act (x : String) : Except String Act :=
  match Act.ofString? x with | some a => pure a | none => throw s!"unknown act \"{x}\""

def Names.ev (n : Names) (str : String) : Except String Ev := do
  let ws := (str.splitOn " ").filter (· != "")
  let bad : Except String Ev := throw s!"cannot read event \"{str}\""
  match ws with
  | ["move", c, p] => return .move (← n.ch c) (← n.pl p)
  | ["take", c, o] => return .take (← n.ch c) (← n.ob o)
  | ["drop", c, o] => return .drop (← n.ch c) (← n.ob o)
  | ["give", c, d, o] => return .give (← n.ch c) (← n.ch d) (← n.ob o)
  | ["tell", c, d, l] => return .tell (← n.ch c) (← n.ch d) (← n.lit l)
  | ["whisper", c, d, l] => return .whisper (← n.ch c) (← n.ch d) (← n.lit l)
  | ["lie", c, d, l] => return .lie (← n.ch c) (← n.ch d) (← n.lit l)
  | ["notice", c, l, e] => return .notice (← n.ch c) (← n.lit l) (← n.evid e)
  | ["realise", c, l] => return .realise (← n.ch c) (← n.lit l)
  | ["flirt", a, b] => return .flirt (← n.ch a) (← n.ch b)
  | ["confide", a, b] => return .confide (← n.ch a) (← n.ch b)
  | ["argue", a, b] => return .argue (← n.ch a) (← n.ch b)
  | ["askAct", a, b, x] => return .askAct (← n.ch a) (← n.ch b) (← act x)
  | ["agree", b, a, x] => return .agree (← n.ch b) (← n.ch a) (← act x)
  | ["withdraw", b, a, x] => return .withdraw (← n.ch b) (← n.ch a) (← act x)
  | ["act", a, b, x] => return .act (← n.ch a) (← n.ch b) (← act x)
  | ["ask", c, d, f] =>
    if let some x := Act.ofString? f then return .askAct (← n.ch c) (← n.ch d) x
    return .ask (← n.ch c) (← n.ch d) (← n.fact f)
  | ["answer", d, c, l] => return .answer (← n.ch d) (← n.ch c) (← n.lit l)
  | ["hint", c, d, l] => return .hint (← n.ch c) (← n.ch d) (← n.lit l)
  | ["sarcasm", c, d, l] => return .sarcasm (← n.ch c) (← n.ch d) (← n.lit l)
  | ["promise", c, d, l] => return .promise (← n.ch c) (← n.ch d) (← n.lit l)
  | ["request", c, d, l] => return .request (← n.ch c) (← n.ch d) (← n.lit l)
  | ["adopt", c, l] => return .adopt (← n.ch c) (← n.lit l)
  | ["dropGoal", c, l] => return .dropGoal (← n.ch c) (← n.lit l)
  | ["intend", c, p] => return .intend (← n.ch c) (← idx "plan" n.plans p)
  | ["abandon", c, l] => return .abandon (← n.ch c) (← n.lit l)
  | _ => bad

/-! ## Printing back -/

def Names.chS (n : Names) (i : Nat) : String := n.chars.getD i s!"?{i}"
def Names.plS (n : Names) (i : Nat) : String := n.places.getD i s!"?{i}"
def Names.obS (n : Names) (i : Nat) : String := n.objects.getD i s!"?{i}"

def Names.factS (n : Names) : Fact → String
  | .at_ c p => s!"at({n.chS c},{n.plS p})"
  | .objAt o p => s!"objAt({n.obS o},{n.plS p})"
  | .holds c o => s!"holds({n.chS c},{n.obS o})"
  | .did a b x => s!"did({n.chS a},{n.chS b},{x.name})"
  | .atom i => n.atoms.getD i s!"?{i}"

def Names.litS (n : Names) (l : Fact × Bool) : String := (if l.2 then "" else "!") ++ n.factS l.1

def Names.evidS (n : Names) : Evid Nat → String
  | .self => "self" | .seen => "seen" | .sensed => "sensed" | .inferred => "inferred"
  | .assumed => "assumed" | .rumour => "rumour"
  | .told c => s!"told:{n.chS c}" | .relayed c => s!"relayed:{n.chS c}"

def Names.evS (n : Names) : Ev → String
  | .move c p => s!"move {n.chS c} {n.plS p}"
  | .take c o => s!"take {n.chS c} {n.obS o}"
  | .drop c o => s!"drop {n.chS c} {n.obS o}"
  | .give c d o => s!"give {n.chS c} {n.chS d} {n.obS o}"
  | .tell c d l => s!"tell {n.chS c} {n.chS d} {n.litS l}"
  | .whisper c d l => s!"whisper {n.chS c} {n.chS d} {n.litS l}"
  | .lie c d l => s!"lie {n.chS c} {n.chS d} {n.litS l}"
  | .notice c l e => s!"notice {n.chS c} {n.litS l} {n.evidS e}"
  | .realise c l => s!"realise {n.chS c} {n.litS l}"
  | .flirt a b => s!"flirt {n.chS a} {n.chS b}"
  | .confide a b => s!"confide {n.chS a} {n.chS b}"
  | .argue a b => s!"argue {n.chS a} {n.chS b}"
  | .askAct a b x => s!"askAct {n.chS a} {n.chS b} {x.name}"
  | .agree b a x => s!"agree {n.chS b} {n.chS a} {x.name}"
  | .withdraw b a x => s!"withdraw {n.chS b} {n.chS a} {x.name}"
  | .act a b x => s!"act {n.chS a} {n.chS b} {x.name}"
  | .ask c d f => s!"ask {n.chS c} {n.chS d} {n.factS f}"
  | .answer d c l => s!"answer {n.chS d} {n.chS c} {n.litS l}"
  | .hint c d l => s!"hint {n.chS c} {n.chS d} {n.litS l}"
  | .sarcasm c d l => s!"sarcasm {n.chS c} {n.chS d} {n.litS l}"
  | .promise c d l => s!"promise {n.chS c} {n.chS d} {n.litS l}"
  | .request c d l => s!"request {n.chS c} {n.chS d} {n.litS l}"
  | .adopt c l => s!"adopt {n.chS c} {n.litS l}"
  | .dropGoal c l => s!"dropGoal {n.chS c} {n.litS l}"
  | .intend c p => s!"intend {n.chS c} {n.plans.getD p s!"?{p}"}"
  | .abandon c l => s!"abandon {n.chS c} {n.litS l}"

/-- Which characters an event involves (for the storyline and colouring). -/
def Ev.parties : Ev → List Nat
  | .move c _ | .take c _ | .drop c _ | .notice c _ _ | .realise c _ | .adopt c _
  | .dropGoal c _ | .intend c _ | .abandon c _ => [c]
  | .give c d _ | .tell c d _ | .whisper c d _ | .lie c d _ | .flirt c d | .confide c d
  | .argue c d | .askAct c d _ | .agree c d _ | .withdraw c d _ | .act c d _ | .ask c d _
  | .answer c d _ | .hint c d _ | .sarcasm c d _ | .promise c d _ | .request c d _ => [c, d]

/-! ## The story file -/

private def str (j : Json) (k : String) : Option String := (j.getObjValAs? String k).toOption
private def strs (j : Json) (k : String) : List String :=
  ((j.getObjValAs? (Array String) k).toOption.getD #[]).toList
private def arr (j : Json) (k : String) : List Json :=
  match j.getObjVal? k with | .ok (.arr a) => a.toList | _ => []
private def obj (j : Json) (k : String) : List (String × Json) :=
  match j.getObjVal? k with | .ok (.obj kvs) => kvs.toList | _ => []

private def need {α} (what : String) : Option α → Except String α
  | some a => pure a | none => throw s!"missing {what}"

private def enumList {α} (kind : String) (f : String → Option α) (xs : List String) :
    Except String (List α) :=
  xs.mapM fun x => match f x with | some a => pure a | none => throw s!"unknown {kind} \"{x}\""

def specOfJson (j : Json) : Except String Spec := do
  let chars ← (arr j "characters").mapM fun c => do
    let id ← need "character id" (str c "id")
    pure ({ id, name := (str c "name").getD id, pron := (str c "pron").getD "she",
            traits := ← enumList "trait" Trait.ofString? (strs c "traits"),
            values := ← enumList "value" Value.ofString? (strs c "values") } : CharSpec)
  let places ← (arr j "places").mapM fun p => need "place id" (str p "id")
  let objects ← (arr j "objects").mapM fun p => need "object id" (str p "id")
  let atoms ← (arr j "atoms").mapM fun a => do
    let id ← need "atom id" (str a "id")
    pure ({ id, label := (str a "label").getD id,
            truth := (a.getObjValAs? Bool "truth").toOption.getD true,
            group := (str a "group").getD "" } : AtomSpec)
  let n0 : Names := { chars := chars.map (·.id), places, objects, atoms := atoms.map (·.id),
                      plans := (arr j "plans").filterMap (str · "id") }
  let lore ← (arr j "lore").mapM fun r => do
    pure ((← (strs r "if").mapM n0.lit), ← n0.lit (← need "lore then" (str r "then")))
  let plans ← (arr j "plans").mapM fun p => do
    pure ({ id := ← need "plan id" (str p "id"), agent := ← n0.ch (← need "plan agent" (str p "agent")),
            goal := ← n0.lit (← need "plan goal" (str p "goal")),
            steps := ← (strs p "steps").mapM n0.ev } : PlanSpec)
  let st := (j.getObjVal? "start").toOption.getD (Json.mkObj [])
  let startAt ← (obj st "at").mapM fun (c, p) => do
    pure (← n0.ch c, ← n0.pl (← need "place" p.getStr?.toOption))
  let startObjAt ← (obj st "objAt").mapM fun (o, p) => do
    pure (← n0.ob o, ← n0.pl (← need "place" p.getStr?.toOption))
  let startHeld ← (obj st "holds").mapM fun (o, c) => do
    pure (← n0.ob o, ← n0.ch (← need "holder" c.getStr?.toOption))
  let bonds ← (obj st "bonds").flatMapM fun (pair, v) => do
    let (a, b) ← match pair.splitOn ">" with
      | [a, b] => pure (a.trimAscii.toString, b.trimAscii.toString)
      | _ => throw s!"bond key \"{pair}\" should be \"from>to\""
    let a ← n0.ch a; let b ← n0.ch b
    match v with
    | .obj kvs => kvs.toList.mapM fun (k, n) => do
      let some d := Dim.ofString? k | throw s!"unknown bond dimension \"{k}\""
      pure (a, b, d, (n.getNat?.toOption.getD 0))
    | _ => throw s!"bond \"{pair}\" should be an object"
  let knows ← (obj st "knows").flatMapM fun (c, v) => do
    let c ← n0.ch c
    match v with
    | .arr ls => ls.toList.mapM fun l => do pure (c, ← n0.lit (← need "literal" l.getStr?.toOption))
    | _ => pure []
  let goals ← (obj st "goals").flatMapM fun (c, v) => do
    let c ← n0.ch c
    match v with
    | .arr ls => ls.toList.mapM fun l => do pure (c, ← n0.lit (← need "literal" l.getStr?.toOption))
    | _ => pure []
  pure { chars, places, objects, atoms, lore, plans, startAt, startObjAt, startHeld, bonds, knows, goals }

end LangLib.Studio
