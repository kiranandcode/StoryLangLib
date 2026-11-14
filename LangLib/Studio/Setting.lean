import LangLib.Basic
import LangLib.Render
import LangLib.Studio.Parse

/-!
# The setting, held to the prose

Every noun in a paragraph's annotation must be accounted for, closed-world:

* it names an entity (its own `ref`, or, as the head or a compound of a
  phrase, the phrase's `ref`), or
* it carries a `sense` saying what it is instead: `abstract time event body
  weather light sound substance digital figurative part person offstage`
  (`offstage` only inside a quote: something named in speech that is not in
  the scene, like "the hotel bar").

A named entity that is a place or object must be one the world declares (a
place, fixture, scenery or plot object, by id). For each mention of a declared
thing the tree gives, deterministically:

* the head noun, which must be one of the thing's words;
* its modifiers (adjectives, noun compounds), each one of the thing's
  attribute values or words unless marked `"sense": "impression"`;
* its possessor ("her desk", "Kiran's laptop", "my scarf" inside a quote),
  which must be the thing's owner;
* its number (a numeral must equal the declared count; a plural head cannot
  name a thing declared single);
* whether it is quoted: a fixture named outside speech must be in a place
  someone is in during the paragraph.

`usesOf` reads these off a document; `settingIssues` judges them against the
spec, the paragraph's scene and its staging (spatial relations the reading
says the prose asserts, which must follow from the layout). Both are plain
functions, so a story's Lean file restates the verdict and proves it by
`decide`.
-/

namespace LangLib.Studio
open LangLib

/-- What a mention resolves to. -/
inductive Target where
  | spot (x : Spot)
  | char (c : Nat)
  /-- an entity the world does not have, with its declared kind -/
  | other (id kind : String)
  deriving DecidableEq, Repr, BEq

structure Use where
  at_ : Nat
  form : String
  /-- the head noun's lemma, lower case -/
  head : String
  target : Target
  /-- adjectives and noun compounds: (token, lower-case lemma) -/
  mods : List (Nat × String) := []
  owner : Option Target := none
  num : Option Nat := none
  plural : Bool := false
  quoted : Bool := false
  deriving DecidableEq, Repr, BEq

/-- A noun that names no entity, with its sense if it has one. -/
structure Bare where
  at_ : Nat
  form : String
  sense : Option String
  quoted : Bool
  deriving DecidableEq, Repr, BEq

structure Uses where
  uses : List Use := []
  bare : List Bare := []
  deriving DecidableEq, Repr, BEq

instance : Inhabited Uses := ⟨{}⟩

def senses : List String :=
  ["abstract", "time", "event", "body", "weather", "light", "sound", "substance", "digital",
   "figurative", "part", "person", "offstage"]

def numberWord : String → Option Nat
  | "one" => some 1 | "two" => some 2 | "three" => some 3 | "four" => some 4 | "five" => some 5
  | "six" => some 6 | "seven" => some 7 | "eight" => some 8 | "nine" => some 9 | "ten" => some 10
  | "twelve" => some 12 | "a" => none | w => w.toNat?

def Spec.resolve (s : Spec) (d : Doc) (e : String) : Target :=
  let n := s.names
  match n.chars.idxOf? e with
  | some c => if c < n.chars.length then .char c else .other e ""
  | none => match n.spot? e with
    | some x => .spot x
    | none => .other e (((d.entities.find? (·.id == e)).map (·.kind.name)).getD "undeclared")

private def lemmaOf (w : Word) : String := (w.lemma.getD w.form).toLower

private def isNoun (w : Word) : Bool := w.upos == .NOUN || w.upos == .PROPN

private def plural (w : Word) : Bool :=
  w.feats.contains ("Number", "Plur") ||
  (w.lemma.isSome && lemmaOf w != w.form.toLower && w.form.toLower.endsWith "s")

/-- Width of a subtree, in tokens. -/
private def width (t : Tree) : Nat := t.render.length

/-- What a head noun's siblings say of it: modifiers, possessor, numeral. -/
structure Ctx where
  mods : List (Nat × String) := []
  owner : Option Target := none
  num : Option Nat := none

private def Ctx.add (s : Spec) (d : Doc) (speaker : Option String) (c : Ctx) (t : Tree) (p : Nat) : Ctx :=
  match t with
  | .leaf w =>
    if w.sense == some "impression" then c
    else if w.role == some .amod || w.role == some .compound then { c with mods := c.mods ++ [(p, lemmaOf w)] }
    else if w.role == some .poss then
      let o := match w.ref with
        | some e => some (s.resolve d e)
        | none => if ["my", "mine"].contains w.form.toLower then speaker.map (s.resolve d) else none
      { c with owner := o }
    else if w.role == some .nummod then { c with num := numberWord w.form.toLower }
    else c
  | .node i _ =>
    if i.role == some .amod && i.sense != some "impression" then
      -- an adjective phrase: its adjectives that are not marked as impressions
      let ws : List (Nat × String) := (t.leaves.zipIdx).filterMap fun (w, j) =>
        if w.upos == .ADJ && w.sense != some "impression" then some (p + j, lemmaOf w) else none
      { c with mods := c.mods ++ ws }
    else if i.role == some .poss then
      let e := i.ref <|> (t.leaves.findSome? (·.ref))
      { c with owner := e.map (s.resolve d) }
    else c

/-- Walk a tree from token `pos`; `speaker` is set inside a quote. -/
partial def usesIn (s : Spec) (d : Doc) (speaker : Option String) (quoted : Bool) :
    Tree → Nat → Uses × Nat
  | .leaf _, p => ({}, p + 1)
  | .node i kids, p =>
    let (speaker, quoted) := if i.cat == .QUOTE then (i.speaker <|> speaker, true) else (speaker, quoted)
    -- start position of each child
    let starts := (kids.foldl (fun (acc, q) k => (acc ++ [q], q + width k)) ([], p)).1
    let placed := kids.zip starts
    let here : Uses := placed.foldl (fun (u : Uses) (k, q) =>
      match k with
      | .leaf w =>
        if !isNoun w then u else
        let sibs := placed.filter fun (_, q') => q' != q
        let mk (e : String) : Use :=
          let c := sibs.foldl (fun c (t, q) => c.add s d speaker t q) ({} : Ctx)
          { at_ := q, form := w.form, head := lemmaOf w, target := s.resolve d e, mods := c.mods,
            owner := c.owner, num := c.num, plural := plural w, quoted }
        match w.ref, w.sense with
        | some e, _ => { u with uses := u.uses ++ [mk e] }
        | none, some x => { u with bare := u.bare ++ [{ at_ := q, form := w.form, sense := some x, quoted }] }
        | none, none =>
          match i.ref, i.sense with
          | some e, _ =>
            if w.role == some .head || w.role == none then { u with uses := u.uses ++ [mk e] }
            else if w.role == some .compound || w.role == some .flat then u  -- a modifier of the head
            else { u with bare := u.bare ++ [{ at_ := q, form := w.form, sense := none, quoted }] }
          | none, some x => { u with bare := u.bare ++ [{ at_ := q, form := w.form, sense := some x, quoted }] }
          | none, none => { u with bare := u.bare ++ [{ at_ := q, form := w.form, sense := none, quoted }] }
      | .node .. => u) {}
    let inner := placed.foldl (fun (u : Uses) (k, q) =>
      let (v, _) := usesIn s d speaker quoted k q
      { uses := u.uses ++ v.uses, bare := u.bare ++ v.bare }) here
    (inner, p + width (.node i kids))

def usesOf (s : Spec) (d : Doc) : Uses :=
  (d.sentences.foldl (fun ((u : Uses), p) st =>
    let (v, p') := usesIn s d none false st.tree p
    ({ uses := u.uses ++ v.uses, bare := u.bare ++ v.bare }, p')) ({}, 0)).1

/-! ## Judging -/

def Spec.spotWords (s : Spec) : Spot → List String
  | .place p => s.names.places.getD p "" :: ((lookup s.placeInfo p).map (·.words)).getD []
  | .thing t => (s.things[t]?.map fun x => x.id.toLower :: x.words).getD []
  | .obj o => s.names.objects.getD o "" :: (lookup s.objWords o).getD []

def Spec.spotAttrs (s : Spec) : Spot → List (String × String)
  | .place p => ((lookup s.placeInfo p).map (·.attrs)).getD []
  | .thing t => (s.things[t]?.map (·.attrs)).getD []
  | .obj _ => []

def Spec.spotOwner (s : Spec) : Spot → Option Nat
  | .thing t => (s.things[t]?).bind (·.owner)
  | _ => none

def Spec.spotCount (s : Spec) : Spot → Option Nat
  | .thing t => (s.things[t]?).bind (·.count)
  | .place _ | .obj _ => some 1

def Spec.spotWhat (s : Spec) : Spot → String
  | .place p => s!"the {s.names.places.getD p "?"}" ++
      (((lookup s.placeInfo p).map fun i => if i.kind == "" then "" else s!" ({i.kind})").getD "")
  | .thing t => (s.things[t]?.map fun x => if x.what == "" then x.id else x.what).getD "?"
  | .obj o => s!"the {s.names.objects.getD o "?"}"

/-- Is a fixed spot in one of `scene`'s places? Places and unfixed things always are. -/
def Spec.inScene (s : Spec) (scene : List Nat) : Spot → Bool
  | .thing t => match (s.things[t]?).bind (·.place) with
    | some p => scene.contains p
    | none => true
  | _ => true

def Spec.useIssues (s : Spec) (scene : List Nat) (u : Use) : List String :=
  let n := s.names
  let tok := s!"'{u.form}' (token {u.at_})"
  match u.target with
  | .char _ => []
  | .other e k =>
    if ["object", "place", "animal", "undeclared"].contains k then
      [s!"{tok} names \"{e}\", which the world does not have: declare it in story.json " ++
        "(a fixture of a place, scenery, or a plot object, with that id), or cut it"]
    else []
  | .spot x =>
    let what := s.spotWhat x
    let words := s.spotWords x
    let attrs := s.spotAttrs x
    (if words.contains u.head then [] else
      [s!"{tok} calls {n.spotS x} ({what}) '{u.head}'; the world's words for it: {", ".intercalate words}"]) ++
    (u.mods.filterMap fun (i, m) =>
      if words.contains m || attrs.any (·.2 == m) then none else
      some (s!"'{m}' (token {i}) is said of {n.spotS x} ({what}), which is not declared so" ++
        (if attrs.isEmpty then "" else
          s!"; its attributes: {", ".intercalate (attrs.map fun (k, v) => s!"{k} {v}")}") ++
        ": declare the attribute, mark the word \"sense\": \"impression\", or change the prose")) ++
    (match u.owner with
      | some (.char c) =>
        if s.spotOwner x == some c then [] else
        [s!"{tok}: the prose gives {n.spotS x} to {n.chS c}, but " ++
          match s.spotOwner x with
          | some o => s!"it is {n.chS o}'s"
          | none => "it has no owner in story.json"]
      | _ => []) ++
    (match u.num with
      | some k => if s.spotCount x == some k then [] else
        [s!"{tok}: the prose says {k} of {n.spotS x}; story.json says " ++
          match s.spotCount x with | some m => toString m | none => "nothing about how many"]
      | none => []) ++
    (if u.plural && s.spotCount x == some 1 then
      [s!"{tok} is plural, but there is one {n.spotS x}"] else []) ++
    (if u.quoted || s.inScene scene x then [] else
      [s!"{tok} is {what}, but nobody is there in this paragraph"])

def bareIssues (b : Bare) : List String :=
  let tok := s!"'{b.form}' (token {b.at_})"
  match b.sense with
  | none => [s!"{tok} is a noun with neither a ref to a world thing nor a sense: give it (or its phrase) " ++
      s!"a ref, or a sense ({", ".intercalate senses})"]
  | some x =>
    if !senses.contains x then [s!"{tok} has sense '{x}', which is not one of {", ".intercalate senses}"]
    else if x == "offstage" && !b.quoted then
      [s!"{tok} is marked offstage, but it is not in speech: a thing in the scene must be declared"]
    else []

def Spec.stageIssues (s : Spec) (st : Fixed) : List String :=
  if (Rel.closure s.layout).contains st then [] else
  let (_, a, b) := st
  let says := (Rel.closure s.layout).filter fun (_, x, y) => x != y && (x == a || x == b || y == a || y == b)
  [s!"the prose stages '{s.names.fixedS st}', which the layout does not have" ++
    (if says.isEmpty then "" else s!"; the layout says: {"; ".intercalate (says.eraseDups.map s.names.fixedS)}") ++
    ": change the prose, or the layout in story.json"]

def Spec.settingIssues (s : Spec) (scene : List Nat) (u : Uses) (staging : List Fixed) : List String :=
  u.uses.flatMap (s.useIssues scene) ++ u.bare.flatMap bareIssues ++ staging.flatMap s.stageIssues

def Spec.settingOk (s : Spec) (scene : List Nat) (u : Uses) (staging : List Fixed) : Bool :=
  (s.settingIssues scene u staging).isEmpty

/-! ## The layout's laws -/

def Spec.layoutIssues (s : Spec) : List String :=
  let n := s.names
  let c := Rel.closure s.layout
  let has (r : Rel) (a b : Spot) := c.contains (r, a, b)
  -- `r a b` with `r' a b` (or `r' b a` when `flip`)
  let clash (r r' : Rel) (flip : Bool) (why : String) := s.layout.filterMap fun (x, a, b) =>
    let (a', b') := if flip then (b, a) else (a, b)
    if x == r && has r' a' b' then
      some s!"layout: {r.name} {n.spotS a} {n.spotS b} and {r'.name} {n.spotS a'} {n.spotS b'}: {why}" else none
  let dups := (n.places ++ n.things ++ n.objects).filter fun x =>
    ((n.places ++ n.things ++ n.objects).filter (· == x)).length > 1
  (dups.eraseDups.map fun x => s!"\"{x}\" names two places or things") ++
  (s.layout.filterMap fun (r, a, b) => if a == b then some s!"layout: {r.name} {n.spotS a} {n.spotS a} relates a thing to itself" else none) ++
  clash .leftOf .leftOf true "each is left of the other" ++ clash .above .above true "each is above the other" ++
  clash .near .farFrom false "near and far" ++ clash .facing .backToBack false "facing and back to back" ++
  (s.layout.filterMap fun (r, a, b) =>
    if (r == .in_ || r == .on || r == .partOf) && c.contains (r, b, a) then
      some s!"layout: {r.name} {n.spotS a} {n.spotS b} both ways" else none) ++
  (s.layout.filterMap fun (r, a, b) =>
    match r, b with
    | .leadsTo, .place _ => none
    | .leadsTo, _ => some s!"layout: leadsTo {n.spotS a} {n.spotS b}: a way leads to a place"
    | _, _ =>
      match s.spotPlace a, s.spotPlace b with
      | some p, some q =>
        if p == q then none
        else some s!"layout: {r.name} {n.spotS a} {n.spotS b}: they are in different places ({n.plS p}, {n.plS q})"
      | _, _ => none)

def Spec.layoutOk (s : Spec) : Bool := s.layoutIssues.isEmpty

def Spec.hasSetting (s : Spec) : Bool := !s.things.isEmpty || !s.placeInfo.isEmpty

end LangLib.Studio
