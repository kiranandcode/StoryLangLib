/-!
# What places are and have

A story's plot needs only place and object ids. Its setting says more: what
kind of place each one is, the fixed things in it (fixtures), the things people
carry that the plot never moves (scenery), how the fixed things are laid out,
and, for each thing, the nouns that name it, its owner, how many there are and
its attributes. `Setting.lean` holds the prose to all of it.

A `Spot` is anything the prose can name: a place, a thing (fixture or
scenery) or a plot object. Layout relations are between spots, with laws
(`Rel.closure`, `layoutIssues`): the symmetric ones hold both ways, `leftOf`
and `rightOf` (`above`, `below`) are inverse, and `leftOf` implies `beside`.
-/

namespace LangLib.Studio

inductive Spot where
  | place (i : Nat)
  | thing (i : Nat)
  | obj (i : Nat)
  deriving DecidableEq, Repr, BEq

inductive Rel where
  | beside | backToBack | facing | near | farFrom | across
  | leftOf | rightOf | above | below
  | in_ | on | at_ | partOf | leadsTo
  deriving DecidableEq, Repr, BEq

def Rel.all : List Rel :=
  [.beside, .backToBack, .facing, .near, .farFrom, .across, .leftOf, .rightOf, .above, .below,
   .in_, .on, .at_, .partOf, .leadsTo]

def Rel.name : Rel → String
  | .beside => "beside" | .backToBack => "backToBack" | .facing => "facing" | .near => "near"
  | .farFrom => "farFrom" | .across => "across" | .leftOf => "leftOf" | .rightOf => "rightOf"
  | .above => "above" | .below => "below" | .in_ => "in" | .on => "on" | .at_ => "at"
  | .partOf => "partOf" | .leadsTo => "leadsTo"

def Rel.ofString? (s : String) : Option Rel := Rel.all.find? (·.name == s)

def Rel.symmetric : Rel → Bool
  | .beside | .backToBack | .facing | .near | .farFrom | .across => true
  | _ => false

def Rel.inverse : Rel → Option Rel
  | .leftOf => some .rightOf | .rightOf => some .leftOf
  | .above => some .below | .below => some .above
  | _ => none

abbrev Fixed := Rel × Spot × Spot

/-- Everything a layout entails: each relation, its mirror (symmetric
relations), its inverse, and `beside` from `leftOf`/`rightOf`. -/
def Rel.closure (xs : List Fixed) : List Fixed :=
  xs.flatMap fun (r, a, b) =>
    [(r, a, b)] ++ (if r.symmetric then [(r, b, a)] else []) ++
    (match r.inverse with | some r' => [(r', b, a)] | none => []) ++
    (if r == .leftOf || r == .rightOf then [(.beside, a, b), (.beside, b, a)] else [])

/-- A fixture, or scenery (no place), with what the prose may say of it. -/
structure ThingSpec where
  id : String
  what : String := ""
  /-- the place it is a fixture of; `none` for scenery, which goes where its owner goes -/
  place : Option Nat := none
  owner : Option Nat := none
  /-- how many (`none`: not said) -/
  count : Option Nat := none
  /-- the nouns that name it (lower-case lemmas) -/
  words : List String := []
  /-- (dimension, value), e.g. ("size", "big"); the values are the adjectives
  and noun modifiers the prose may use of it -/
  attrs : List (String × String) := []
  deriving Repr, DecidableEq

structure PlaceInfo where
  kind : String := ""
  desc : String := ""
  words : List String := []
  attrs : List (String × String) := []
  deriving Repr, DecidableEq

end LangLib.Studio
