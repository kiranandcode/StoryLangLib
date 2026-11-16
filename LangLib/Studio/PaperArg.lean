import Lean.Data.Json
import LangLib.World.Argument

/-!
# A paper's argument as a graph, for the Studio

`langlib argument <dir> <lore-json>` reads a paper's moves
(`paragraphs/NN.argument.json`, written by `tools/argument_gen.py`) with terms
as strings, runs them through `World/Argument` from the reader's lore, and
prints the argument graph:

- **nodes**: each proposition the paper puts forward (claimed, inferred,
  cited, exemplified, evaluated, hedged, denied or conceded), each definition
  a premise rests on, and each move that bears on a proposition: a citation
  (prior work), a worked example (the reader), a measurement (the data), a
  denial, a concession, a promise, a contribution, a hedge and a delivery;
- **edges**: `support` (a citation, example or measurement for its claim; a
  premise for what is inferred from it; a lore rule's body for its head),
  `attack` (a denial or concession against the proposition), `contrast`
  (two terms set against each other), `delivers` (a promise or hedge to the
  move that pays it off);
- each node's **grounded label** (Dung 1995; Caminada 2006): `in` when every
  attacker is out, `out` when some attacker is in, `undec` otherwise; and,
  for propositions, how the reader **holds** it at the end (`accepted`:
  outright; `authors' word`: conservatively; `denied`; `noted`) with
  `Mind.explain`'s reasons.

The lore JSON is `{"lore": [...], "excerpt": [...], "rules": [[body, head], ...]}`
(the paper's `argument.py`). Validity and gaps are World/Argument's own;
`Argument.lean` proves them by `decide +kernel`.
-/

namespace LangLib.Studio.PaperArg
open Lean LangLib.World LangLib.World.Argument

abbrev M := Move String

private def strs (j : Json) (k : String) : List String :=
  match j.getObjVal? k with
  | .ok (.arr a) => a.toList.filterMap (·.getStr?.toOption)
  | _ => []
private def str (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""
private def nat (j : Json) (k : String) : Nat := (j.getObjValAs? Nat k).toOption.getD 0

def moveOf (j : Json) : Except String M := do
  let t := str j "t"
  let u := strs j "uses"
  match str j "move" with
  | "claim" => pure (.claim t u) | "cite" => pure (.cite t u) | "define" => pure (.define t u)
  | "motivate" => pure (.motivate t u) | "example" => pure (.«example» t u)
  | "contrast" => pure (.contrast (str j "a") (str j "b") u)
  | "promise" => pure (.promise t (nat j "sec") u)
  | "contribute" => pure (.contribute t (nat j "sec") u)
  | "deliver" => pure (.deliver t u) | "concede" => pure (.concede t u)
  | "deny" => pure (.deny t u) | "hedge" => pure (.hedge t (nat j "sec") u)
  | "infer" => pure (.infer t (strs j "premises") u)
  | "evaluate" => pure (.evaluate t u) | "heading" => pure (.heading (nat j "sec"))
  | m => throw s!"unknown move {m}"

structure Node where
  id : String
  kind : String
  t : String
  para : String
  voice : String := "author"
  note : String := ""
  label : String := "in"
  held : String := ""
  support : List Json := []

structure Edge where
  src : String
  tgt : String
  kind : String
  why : String := ""

/-- The grounded labelling of `ids` under `attacks` (src attacks tgt): the
least fixed point, reached in at most `ids.length` rounds. -/
def grounded (ids : List String) (attacks : List (String × String)) : List (String × String) := Id.run do
  let mut lab : List (String × String) := ids.map (·, "undec")
  for _ in [0:ids.length + 1] do
    let get (x : String) := ((lab.find? (·.1 == x)).map (·.2)).getD "undec"
    lab := lab.map fun (x, l) =>
      if l != "undec" then (x, l) else
      let att := attacks.filter (·.2 == x) |>.map (·.1)
      if att.all (get · == "out") then (x, "in")
      else if att.any (get · == "in") then (x, "out") else (x, "undec")
  return lab

def moveJ (i : Nat) (m : M) (ok : Bool) (why : String) : Json :=
  let base : List (String × Json) := [("i", i), ("ok", ok), ("why", if ok then "" else why)]
  let f : List (String × Json) := match m with
    | .claim k u => [("move", "claim"), ("t", k), ("uses", toJson u)]
    | .cite k u => [("move", "cite"), ("t", k), ("uses", toJson u)]
    | .define k u => [("move", "define"), ("t", k), ("uses", toJson u)]
    | .motivate k u => [("move", "motivate"), ("t", k), ("uses", toJson u)]
    | .«example» k u => [("move", "example"), ("t", k), ("uses", toJson u)]
    | .contrast a b u => [("move", "contrast"), ("a", a), ("b", b), ("uses", toJson u)]
    | .promise k s u => [("move", "promise"), ("t", k), ("sec", s), ("uses", toJson u)]
    | .contribute k s u => [("move", "contribute"), ("t", k), ("sec", s), ("uses", toJson u)]
    | .deliver k u => [("move", "deliver"), ("t", k), ("uses", toJson u)]
    | .concede k u => [("move", "concede"), ("t", k), ("uses", toJson u)]
    | .deny k u => [("move", "deny"), ("t", k), ("uses", toJson u)]
    | .hedge k s u => [("move", "hedge"), ("t", k), ("sec", s), ("uses", toJson u)]
    | .infer k ps u => [("move", "infer"), ("t", k), ("premises", toJson ps), ("uses", toJson u)]
    | .evaluate k u => [("move", "evaluate"), ("t", k), ("uses", toJson u)]
    | .heading n => [("move", "heading"), ("sec", n)]
  Json.mkObj (f ++ base)

section
variable [Lore (AFact String)]

def evidS : Evid Voice → String
  | .told .author => "the authors' word" | .relayed .prior => "prior work" | .told .data => "the data"
  | .inferred => "the reader's own inference" | .self => "the reader's background"
  | e => (reprStr e).replace "LangLib.World.Evid." ""

/-- Each report the reader has of `k` (or its denial): its source, its reasons and
their total, and the attitude it was taken with (`Mind.explain`, structured). -/
def supportOf (w : AW String) (k : String) : List Json :=
  w.base.filterMap fun h => match litOf h.b with
    | some (AFact.holds k', pos) =>
      if k' != k then none else some (Json.mkObj [
        ("src", evidS h.src), ("for", pos),
        ("reasons", toJson (h.reasons.map fun (r, n) => s!"{Reason.text (AFact String) r} {if n ≥ 0 then "+" else ""}{n}")),
        ("strength", toJson (h.reasons.map (·.2)).sum),
        ("attitude", (reprStr h.up).replace "LangLib.World.Upgrade." "")])
    | _ => none

/-- The graph of a paper's moves, paragraph by paragraph. -/
def report (w0 : AW String) (paras : List (String × List M)) : Json := Id.run do
  let mut w := w0
  let mut nodes : Array Node := #[]
  let mut edges : Array Edge := #[]
  let mut parasJ : Array Json := #[]
  let mut i := 0
  let mut failure : Option (Nat × String) := none
  -- the open promise or hedge of each term, and its node
  let mut opens : List (String × String) := []
  let prop (t : String) := s!"P:{t}"
  let addN (ns : Array Node) (n : Node) : Array Node := if ns.any (·.id == n.id) then ns else ns.push n
  for (nm, ms) in paras do
    let mut mj : Array Json := #[]
    for m in ms do
      let ok := argOk w m
      let why := argWhy w m
      mj := mj.push (moveJ i m ok why)
      if !ok && failure.isNone then failure := some (i, why)
      let src (kind _voice t : String) := s!"{kind}:{t}:{nm}:{i}"
      match m with
      | .claim k _ => nodes := addN nodes { id := prop k, kind := "claim", t := k, para := nm }
      | .infer k ps _ =>
        nodes := addN nodes { id := prop k, kind := "claim", t := k, para := nm }
        for p in ps do
          if !(nodes.any (·.id == prop p)) then
            let kind := if w0.base.any (·.b == .atom (.known p)) then "lore" else "definition"
            nodes := addN nodes { id := prop p, kind := kind, t := p, para := nm }
          edges := edges.push { src := prop p, tgt := prop k, kind := "support", why := "a reason given for it" }
      | .cite k _ =>
        nodes := addN nodes { id := prop k, kind := "claim", t := k, para := nm }
        nodes := nodes.push { id := src "cite" "prior" k, kind := "cite", t := k, para := nm, voice := "prior" }
        edges := edges.push { src := src "cite" "prior" k, tgt := prop k, kind := "support", why := "published prior work" }
      | .«example» k _ =>
        nodes := addN nodes { id := prop k, kind := "claim", t := k, para := nm }
        nodes := nodes.push { id := src "example" "reader" k, kind := "example", t := k, para := nm, voice := "reader" }
        edges := edges.push { src := src "example" "reader" k, tgt := prop k, kind := "support", why := "the reader works the example through" }
      | .evaluate k _ =>
        nodes := addN nodes { id := prop k, kind := "claim", t := k, para := nm }
        nodes := nodes.push { id := src "evaluate" "data" k, kind := "evaluate", t := k, para := nm, voice := "data" }
        edges := edges.push { src := src "evaluate" "data" k, tgt := prop k, kind := "support", why := "measured" }
        if let some (_, o) := opens.find? (·.1 == k) then
          edges := edges.push { src := o, tgt := src "evaluate" "data" k, kind := "delivers", why := "answered by the evaluation" }
          opens := opens.filter (·.1 != k)
      | .deny k _ =>
        let anti := !putForward w k
        nodes := addN nodes { id := prop k, kind := "claim", t := k, para := nm, note := (if anti then "put forward only to be denied" else "") }
        nodes := nodes.push { id := src "deny" "author" k, kind := "deny", t := k, para := nm, note := (if anti then "antithesis: nobody put it forward" else "contrast: denies what was put forward") }
        edges := edges.push { src := src "deny" "author" k, tgt := prop k, kind := "attack", why := "the authors rule it out" }
      | .concede k _ =>
        nodes := addN nodes { id := prop k, kind := "claim", t := k, para := nm }
        nodes := nodes.push { id := src "concede" "author" k, kind := "concede", t := k, para := nm, note := "a limitation the authors admit" }
        edges := edges.push { src := src "concede" "author" k, tgt := prop k, kind := "attack", why := "conceded" }
      | .contrast a b _ =>
        for t in [a, b] do
          if !(nodes.any (·.id == prop t)) then
            nodes := addN nodes { id := prop t, kind := "term", t := t, para := nm }
        edges := edges.push { src := prop a, tgt := prop b, kind := "contrast", why := "set against each other" }
      | .define t _ => nodes := addN nodes { id := prop t, kind := "definition", t := t, para := nm }
      | .promise t s _ | .contribute t s _ | .hedge t s _ =>
        let kind := match m with | .promise .. => "promise" | .contribute .. => "contribution" | _ => "hedge"
        let id := src kind "author" t
        nodes := nodes.push { id := id, kind := kind, t := t, para := nm, note := (if s == 0 then "later" else s!"section {s}") }
        opens := opens ++ [(t, id)]
        if kind == "hedge" then
          nodes := addN nodes { id := prop t, kind := "claim", t := t, para := nm }
      | .deliver t _ =>
        let id := src "deliver" "author" t
        nodes := nodes.push { id := id, kind := "deliver", t := t, para := nm }
        if let some (_, o) := opens.find? (·.1 == t) then
          edges := edges.push { src := o, tgt := id, kind := "delivers", why := "the promise paid off" }
          opens := opens.filter (·.1 != t)
      | .motivate _ _ | .heading _ => pure ()
      w := argStep w m
      i := i + 1
    parasJ := parasJ.push (Json.mkObj [("name", nm), ("moves", Json.arr mj)])
  -- lore rules between propositions in the graph: what the reader would infer
  for r in Lore.rules (Φ := AFact String) do
    if let (.holds h, true) := r.head then
      for (b, pos) in r.body do
        if let .holds bt := b then
          if pos && nodes.any (·.id == prop bt) && nodes.any (·.id == prop h) then
            edges := edges.push { src := prop bt, tgt := prop h, kind := "support", why := "the reader would infer it" }
  -- what is still open at the end
  nodes := nodes.map fun n =>
    if (n.kind == "promise" || n.kind == "contribution" || n.kind == "hedge") && opens.any (·.2 == n.id) then
      let p := w.pending.find? (·.t == n.t)
      { n with note := match p with
          | some p => if deferred w p then s!"deferred ({n.note})" else s!"never paid ({n.note})"
          | none => n.note }
    else n
  -- grounded labelling over the attacks
  let lab := grounded (nodes.toList.map (·.id)) (edges.toList.filter (·.kind == "attack") |>.map fun e => (e.src, e.tgt))
  let gaps := gapsOf w
  nodes := nodes.map fun n =>
    let label := ((lab.find? (·.1 == n.id)).map (·.2)).getD "undec"
    if n.id != prop n.t then { n with label } else
    let held :=
      if accepted w n.t then "accepted"
      else if w.base.any (fun h => h.b == .atom (.holds n.t)) then "authors' word"
      else if w.base.any (fun h => h.b == .neg (.holds n.t)) then "denied"
      else if believes w Voice.reader (.atom (AFact.known n.t)) then "known"
      else ""
    let note := if gaps.contains (.unsupported n.t) then "unsupported at the end of the excerpt"
      else if w.pending.any (fun p => p.t == n.t && deferred w p) && !accepted w n.t then "support deferred to a later section"
      else n.note
    { n with label, held, note, support := supportOf w n.t }
  let gapJ : Gap String → Json
    | .unsupported k => Json.mkObj [("kind", "unsupported"), ("t", k)]
    | .unpaid t s => Json.mkObj [("kind", "unpaid"), ("t", t), ("sec", s)]
    | .unmotivated k => Json.mkObj [("kind", "unmotivated"), ("t", k)]
    | .unanswered k => Json.mkObj [("kind", "unanswered"), ("t", k)]
  return Json.mkObj [
    ("valid", failure.isNone),
    ("failure", match failure with | some (i, why) => Json.mkObj [("i", i), ("why", why)] | none => Json.null),
    ("coherent", failure.isNone && gaps.isEmpty),
    ("paragraphs", Json.arr parasJ),
    ("nodes", Json.arr (nodes.map fun n => Json.mkObj [("id", n.id), ("kind", n.kind), ("t", n.t), ("para", n.para),
      ("voice", n.voice), ("note", n.note), ("label", n.label), ("held", n.held), ("support", Json.arr n.support.toArray)])),
    ("edges", Json.arr (edges.map fun e => Json.mkObj [("src", e.src), ("tgt", e.tgt), ("kind", e.kind), ("why", e.why)])),
    ("gaps", Json.arr (gaps.map gapJ).toArray),
    ("deferred", Json.arr ((deferredList w).map fun (t, s) => Json.mkObj [("t", t), ("sec", s)]).toArray),
    ("antitheses", toJson (antitheses w)),
    ("contrasts", toJson (contrasts w))]

end

def argumentMain (dir : String) (loreJ : String) : IO Json := do
  let lj ← IO.ofExcept (Json.parse loreJ)
  let lore := strs lj "lore"
  let excerpt := match lj.getObjVal? "excerpt" with
    | .ok (.arr a) => a.toList.filterMap (·.getNat?.toOption) | _ => []
  let rules : List (LoreRule (AFact String)) := match lj.getObjVal? "rules" with
    | .ok (.arr a) => a.toList.filterMap fun r => match r with
      | .arr #[body, .str head] => some
        { body := (match body with | .arr b => b.toList.filterMap (fun (x : Json) => x.getStr?.toOption) | _ => []).map
            fun t => (AFact.holds t, true),
          head := (AFact.holds head, true) }
      | _ => none
    | _ => []
  let pdir := System.FilePath.mk dir / "paragraphs"
  let files ← pdir.readDir
  let names := (files.toList.filterMap fun f =>
    if f.fileName.endsWith ".argument.json" then some ((f.fileName.splitOn ".").head!) else none).mergeSort (· ≤ ·)
  let paras ← names.mapM fun nm => do
    let j ← IO.ofExcept (Json.parse (← IO.FS.readFile (pdir / s!"{nm}.argument.json")))
    let ms ← match j.getObjVal? "moves" with
      | .ok (.arr a) => IO.ofExcept (a.toList.mapM moveOf)
      | _ => pure []
    pure (nm, ms)
  let _ : Lore (AFact String) := ⟨rules⟩
  pure (report (start lore excerpt) paras)

end LangLib.Studio.PaperArg
