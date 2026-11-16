import LangLib.World.Examples.Fight
import LangLib.Studio.Power

/-!
# The fight as a Power export (`studio/power-schema.md`)

Chrollo against Hisoka, move by move, for the Studio's Power view: each move's
paragraph, every precondition of `useWhy` and `nenWhy` evaluated (in their
order, so the first that fails is the module's own `why`; `agrees` checks it),
the Nen state after it (aura, techniques, hands, the book, marks, controlled
and mobile bodies, active abilities, likenesses, what each person believes of
the Nen facts), and the key turns this file's parent proves fail.

`langlib power stories/hxh-chrollo-hisoka` prints it.
-/

namespace LangLib.World.Fight
open LangLib.World LangLib.Studio.Power Lean Ch Pl Ab

def chName : Ch → String
  | chrollo => "Chrollo" | hisoka => "Hisoka" | judge => "the judge" | fan => "the spectator"
  | c1 => "copy 1" | c2 => "copy 2" | c3 => "copy 3" | c4 => "copy 4"

def techName : Tech → String
  | .ten => "Ten" | .zetsu => "Zetsu" | .ren => "Ren" | .gyo => "Gyo" | .in_ => "In" | .en => "En"
  | .ken => "Ken" | .ko => "Ko" | .ryu => "Ryu"

def handName : Hand → String | .left => "left hand" | .right => "right hand" | .both => "both hands"
def abName (a : Ab) : String := (defs a).name

def litText (l : Fact × Bool) : String :=
  let s := match l.1 with
    | .space (.at_ c p) => s!"{chName c} is at the {nm p}"
    | .space _ => "?"
    | .nen x => match x with
      | .can c a => s!"{chName c} has {abName a}" | .active c a => s!"{chName c}'s {abName a} is up"
      | .marked x k => s!"{chName x} bears a {nm k}" | .looksLike x y => s!"{chName x} wears {chName y}'s face"
      | .is x y => s!"{chName x} is {chName y}" | .needsBothHands a => s!"{abName a} needs both hands free"
      | .usesBothHands a => s!"{abName a} is worked with both hands" | .gone x => s!"{chName x} is gone"
  if l.2 then s else s!"not: {s}"

/-- A move, in words. -/
def E.text : E → String
  | .space (.move c p) => s!"{chName c} goes to the {nm p}"
  | .space _ => "a move in space"
  | .mind (.tell c d l) => s!"{chName c} tells {chName d}: {litText l}"
  | .mind (.notice c l e) => s!"{chName c} {if e == .inferred then "concludes" else "notices"}: {litText l}"
  | .mind _ => "a change of mind"
  | .nen x => match x with
    | .tech c t => s!"{chName c} takes up {techName t}" | .untech c t => s!"{chName c} lets {techName t} go"
    | .openBook c a => s!"{chName c} opens the book at {abName a}" | .closeBook c => s!"{chName c} shuts the book"
    | .bookmark c a => s!"{chName c} puts the bookmark in {abName a}"
    | .use c a t h => s!"{chName c} uses {abName a} on {chName t}, {handName h}"
    | .charge c t => s!"{chName c} holds the seal on {chName t}: a complete bomb"
    | .release c a => s!"{chName c} releases {abName a}"
    | .order c x => s!"{chName c} commands {chName x}" | .behead c x => s!"{chName c} takes {chName x}'s head"
    | .detonate x y => if x == y then s!"the seals on {chName x} meet" else s!"the sun on {chName x} meets the moon on {chName y}"
    | .spot c x => s!"{chName c} sees the hidden aura on {chName x}"
    | .strike c t n => s!"{chName c} strikes {chName t} ({n})" | .lose c h => s!"{chName c} loses the {handName h}"
    | .hide c => s!"{chName c} blends into the crowd" | .emerge c => s!"{chName c} comes out of the crowd"

def E.actor : E → String
  | .space (.move c _) => nm c | .mind (.tell c _ _) | .mind (.notice c _ _) => nm c
  | .nen x => match x with
    | .tech c _ | .untech c _ | .openBook c _ | .closeBook c | .bookmark c _ | .use c _ _ _ | .charge c _
    | .release c _ | .order c _ | .behead c _ | .spot c _ | .strike c _ _ | .lose c _ | .hide c | .emerge c => nm c
    | .detonate _ _ => ""
  | _ => ""

def E.targets : E → List String
  | .mind (.tell _ d _) => [nm d]
  | .nen (.use _ _ t _) | .nen (.charge _ t) | .nen (.order _ t) | .nen (.behead _ t) | .nen (.spot _ t)
  | .nen (.strike _ t _) => [nm t]
  | .nen (.detonate x y) => if x == y then [nm x] else [nm x, nm y]
  | _ => []

def E.kind : E → String
  | .space _ => "move" | .mind (.tell ..) => "tell" | .mind (.notice ..) => "notice" | .mind _ => "mind"
  | .nen x => ((E.show (.nen x)).splitOn " ").headD "nen"

/-- `c x` reads `cond`; it fails with `why`. -/
def ck (id kind label : String) (pass : Bool) (why : String) : Check := { id, kind, label, pass, why }

/-- Every precondition of a Nen move, in `useWhy`/`nenWhy` order. Conditions that
only bear on some abilities (a copy, a puppet target, a holding limit) are
listed only for those. -/
def nenChecks (w : W) : NenEv Ch Ab → List Check
  | .use c a t h =>
    let st := w.nen
    let d := st.defs a
    let reach := if d.effect == .copy then st.orig t else t
    let handsOk := match d.hands with | .none => true | .one => st.free c h | .both => st.free c .both
    let handsWhy := if d.hands == .both then s!"{d.name} needs both hands free" ++ (if (st.book c).held then " (the right one holds the book)" else "")
      else if h == .right && (st.book c).held then "the right hand holds the book" else "that hand is not free"
    [ck "alive" "status" s!"{chName c} is alive" (st.present c) "they are dead",
     ck "zetsu" "status" s!"{chName c} is not in Zetsu" (!st.has c .zetsu) "in Zetsu no aura flows, so no Hatsu",
     ck "owns" "possession" s!"{chName c} has {d.name}" ((st.owns c).contains a) s!"they do not have {d.name}",
     ck "owner" "possession" (if d.stolen then s!"{d.name}'s owner lives, or it is post-mortem Nen" else s!"{d.name} is {chName c}'s own")
       (d.ownerAlive || d.postMortem) s!"the owner of {d.name} is dead, so it has gone from the book",
     ck "support" "support" (if d.stolen then s!"the book is open at {d.name} in the right hand, or its page holds the bookmark" else "an own ability needs no book")
       (st.supported c a) s!"the book is neither open at {d.name} nor bookmarked there"] ++
    (if d.effect == .seal then [ck "seal-hand" "body" "a seal is made with one hand" (h != .both)
       "a seal is made with one hand: the sun with the left, the moon with the right"] else []) ++
    [ck "hands" "body" (match d.hands with
        | .none => s!"{d.name} needs no hand"
        | .one => s!"the {handName h} is free" ++ (if h == .right then " (the right holds the book when it is open)" else "")
        | .both => "both hands are free (the book shut)") handsOk handsWhy,
     ck "aura" "resource" s!"aura {st.aura c} ≥ cost {d.cost}" (st.aura c ≥ d.cost) s!"not enough aura ({st.aura c} < {d.cost})",
     ck "reach" "position" s!"{chName reach} is here, with {chName c}" (w.loc reach == w.loc c && st.present reach) "the target is out of reach"] ++
    (if d.effect == .copy then [ck "unmade" "target" s!"{chName t} is a copy not yet made" (st.body t == .copy && !st.present t)
       "only a copy not yet made can be made"] else []) ++
    (if d.target == .puppet then [ck "puppet" "target" s!"{chName t} is a puppet with its head" (st.body t == .copy && st.headed t)
       s!"{d.name} only works on a puppet with its head"] else []) ++
    (if d.target == .person then [ck "person" "target" s!"{chName t} is a person" (st.body t == .person)
       s!"{d.name} only works on people"] else []) ++
    (if d.limit != 0 then [ck "limit" "rule" s!"{chName c} holds fewer than {d.limit} with {d.name}"
       (!(d.limit ≤ holdsCount st Cast.all c a)) s!"{d.name} holds at most {d.limit} at once"] else [])
  | .tech c t =>
    let st := w.nen
    [ck "alive" "status" s!"{chName c} is alive" (st.present c) "they are dead",
     ck "new" "rule" s!"{techName t} is not up yet" (!st.has c t) "they already have it up",
     ck "compatible" "rule" s!"{techName t} can be held with what is up" (!(st.techs c).any (Tech.excludes t)) "it cannot be held with what they already have up",
     ck "aura" "resource" s!"aura {st.aura c} ≥ cost {t.cost}" (st.aura c ≥ t.cost) s!"not enough aura ({st.aura c} < {t.cost})"]
  | .untech c t => [ck "up" "rule" s!"{techName t} is up" (w.nen.has c t) "they do not have it up"]
  | .openBook c a =>
    let st := w.nen
    [ck "alive" "status" s!"{chName c} is alive" (st.present c) "they are dead",
     ck "page" "possession" s!"{abName a} is a page of {chName c}'s book" ((st.owns c).contains a && (st.defs a).stolen) "that is not a page of their book",
     ck "right" "body" s!"{chName c} has a right hand" ((st.hands c).contains .right) "the book is held in the right hand",
     ck "zetsu" "status" s!"{chName c} is not in Zetsu" (!st.has c .zetsu) "in Zetsu no aura flows, so no book"]
  | .closeBook c => [ck "held" "support" s!"{chName c} holds the book" (w.nen.book c).held "they are not holding the book"]
  | .bookmark c a => [ck "open" "support" s!"the book is held open at {abName a}" ((w.nen.book c).held && (w.nen.book c).page == some a)
      "the bookmark goes in the page the book is open at"]
  | .charge c t =>
    let st := w.nen
    [ck "alive" "status" s!"{chName c} is alive" (st.present c) "they are dead",
     ck "reach" "position" s!"{chName t} is here, with {chName c}" (w.loc c == w.loc t) "the target is out of reach",
     ck "seal" "target" s!"a seal of {chName c}'s on {chName t}, not yet complete"
       ((st.marks t).any fun m => m.by_ == c && (m.kind == .sun || m.kind == .moon) && !m.full) "there is no seal of theirs on it to hold",
     ck "aura" "resource" s!"aura {st.aura c} ≥ 1" (st.aura c ≥ 1) "not enough aura"]
  | .release c a => [ck "active" "rule" s!"{abName a} is up" (w.nen.active.contains (c, a)) "it is not active"]
  | .order c x => [ck "control" "rule" s!"{chName c} controls {chName x} (an antenna, or a stamp on a headed puppet)"
      (w.nen.controlledBy c x) "they do not control that body"]
  | .behead c x =>
    let st := w.nen
    [ck "alive" "status" s!"{chName c} is alive" (st.present c) "they are dead",
     ck "other" "target" s!"{chName x} is not {chName c}" (c != x) "not themselves",
     ck "reach" "position" s!"{chName x} is here, with {chName c}" (w.loc c == w.loc x && st.present x) "the target is out of reach",
     ck "head" "body" s!"{chName x} has a head" (st.headed x) "it has no head"]
  | .detonate x y =>
    let st := w.nen
    let sun := (st.marks x).filter (·.kind == .sun)
    let moon := (st.marks y).filter (·.kind == .moon)
    [ck "present" "status" s!"{chName x} and {chName y} are still there" (st.present x && st.present y) "a sealed body is gone",
     ck "together" "position" "the sealed bodies are in one place" (w.loc x == w.loc y) "the seals are not together",
     ck "pair" "target" s!"a sun on {chName x} and a moon on {chName y}, of one ability and user"
       (sun.any fun s => moon.any fun m => s.by_ == m.by_ && s.ab == m.ab) "no sun on the one and moon on the other",
     ck "mobile" "body" "one of the bodies can move (a person, or controlled)" (st.mobile x || st.mobile y)
       "neither body can move to bring the seals together (a puppet without its head, nobody controlling it)"]
  | .spot c x =>
    let st := w.nen
    [ck "gyo" "rule" s!"{chName c} has Gyo up" (st.has c .gyo) "without Gyo, aura hidden by In cannot be seen",
     ck "sight" "position" s!"{chName x} is in sight" (w.loc c == w.loc x) "it is out of sight",
     ck "hidden" "target" s!"hidden aura on {chName x}" ((st.marks x).any (·.hidden)) "there is no hidden aura on it"]
  | .strike c t _ =>
    let st := w.nen
    [ck "alive" "status" s!"{chName c} is alive" (st.present c) "they are dead",
     ck "other" "target" s!"{chName t} is not {chName c}" (c != t) "not themselves",
     ck "reach" "position" s!"{chName t} is here, with {chName c}" (w.loc c == w.loc t && st.present t) "the target is out of reach"]
  | .lose c h => [ck "has" "body" s!"{chName c} still has the {handName h}" ((w.nen.hands c).contains h) "they have already lost it"]
  | .hide c => [ck "open" "rule" s!"{chName c} is in the open" (!w.nen.hidden c) "they are already hidden"]
  | .emerge c => [ck "hidden" "rule" s!"{chName c} is hidden" (w.nen.hidden c) "they are not hidden"]

/-- Every precondition of a move of the story: Nen's in full; space and minds as one check each. -/
def checksOf (w : W) : E → List Check
  | .nen x => nenChecks w x
  | e => [ck "allowed" "rule" (match e with | .space _ => "the move is possible" | _ => "the mind can take it in")
      (Domain.ok w e) (Domain.why w e)]

def markOf (m : Mark Ch Ab) : PMark :=
  { kind := nm m.kind, by_ := nm m.by_, via := abName m.ab,
    note := ", ".intercalate ((if m.full then ["a complete bomb"] else []) ++ (if m.hidden then ["hidden by In"] else [])) }

/-- The state as the view reads it. -/
def stateOf (w : W) : PState :=
  let st := w.nen
  let cs : List Ch := Cast.all
  let people := cs.filter fun c => st.body c == .person
  let actor (c : Ch) : PActor :=
    let person := st.body c == .person
    { id := nm c
      status := (if st.present c then ["present"] else ["gone"]) ++ (if st.hidden c then ["hidden"] else []) ++
        (if st.present c && st.mobile c then ["mobile"] else []) ++ (if st.controlled c then ["controlled"] else []) ++
        (if !st.headed c then ["headless"] else []) ++ (if st.sealed c then ["sealed (post-mortem Nen)"] else [])
      resources := if person && !(st.owns c).isEmpty then [("aura", st.aura c)] else []
      fields := [{ key := "place", label := "where", value := toJson (nm (w.loc c)) }] ++
        (if person && !(st.owns c).isEmpty then
          [{ key := "type", label := "Nen type", value := toJson (nm (st.type c)) },
           { key := "abilities", label := "abilities (power %)", value := toJson ((st.owns c).filter (st.can c) |>.map fun a => s!"{abName a} {st.power c a}") },
           { key := "techs", label := "techniques up", value := toJson ((st.techs c).map techName) },
           { key := "hands", label := "hands", value := toJson ((st.hands c).map handName) }] else []) ++
        (if (st.owns c).any (fun a => (st.defs a).stolen) then
          let b := st.book c
          [{ key := "book", label := "the book", value := toJson
              ((if b.held then s!"held in the right hand, open at {(b.page.map abName).getD "?"}" else "shut") ++
               s!"; bookmark: {(b.mark.map abName).getD "none"}") }] else []) ++
        (if st.hurt c > 0 then [{ key := "hurt", label := "hurt", value := toJson (st.hurt c) }] else []) ++
        (if st.looks c != c then [{ key := "looks", label := "wears the face of", value := toJson (chName (st.looks c)) }] else [])
      marks := (st.marks c).map markOf }
  { actors := cs.map actor
    active := st.active.map fun (c, a) =>
      { by_ := nm c, what := abName a, on := cs.filter (fun x => (st.marks x).any fun m => m.by_ == c && m.ab == a) |>.map nm }
    relations := (people.flatMap fun c => cs.filterMap fun x =>
        if c != x && st.controlledBy c x then some { src := nm c, dst := nm x, kind := "controls", label := "controls" } else none) ++
      (cs.filterMap fun x => if st.looks x != x && st.present x then
        some { src := nm x, dst := nm (st.looks x), kind := "looks-like", label := s!"wears {chName (st.looks x)}'s face" } else none)
    knowledge := people.flatMap fun c => (view w c).filterMap fun (φ, b) => match φ with
      | .nen _ => some { who := nm c, what := litText (φ, b), holds := b, true_ := truthLit w (φ, b) }
      | _ => none }

def paras : List (String × List E) :=
  [("01", p1), ("02", p2), ("03", p3), ("04", p4), ("05", p5), ("06", p6), ("07", p7), ("08", p8), ("09", p9)]

/-- Each move with its paragraph: the story's `NN.events.json` lists it under `"nen"`. -/
def tagged : List (String × E) := paras.flatMap fun (n, es) => es.map (n, ·)

def paraOfIndex (i : Nat) : String := Id.run do
  let mut k := 0
  for (n, es) in paras do
    if i < k + es.length then return n
    k := k + es.length
  return ""

/-- The moves of a run with their verdicts, checks and the state after each. -/
def movesOf (w0 : W) (es : List (String × E)) : List Move := Id.run do
  let mut w := w0
  let mut out : Array Move := #[]
  let mut i := 0
  for (para, e) in es do
    let ok := Domain.ok w e
    let why := if ok then "" else Domain.why w e
    let cs := checksOf w e
    w := next w e
    out := out.push
      { i, para, actor := e.actor, kind := e.kind, text := e.text, raw := E.show e,
        targets := e.targets, ok, why, checks := cs, state := stateOf w }
    i := i + 1
  return out.toList

/-- A counterfactual run, where it fails, and that move's checks. -/
def cf (id label thm change : String) (w0 : W) (es : List E) : Counterfactual :=
  match firstFailure w0 es 0 with
  | some (k, why) =>
    let w := run w0 (es.take k)
    { id, label, theorem_ := thm, change, move := some k, para := paraOfIndex k, why,
      checks := match es[k]? with | some e => checksOf w e | none => [] }
  | none => { id, label, theorem_ := thm, change, move := none, para := "", why := "it does not fail", checks := [] }

def counterfactuals : List Counterfactual :=
  [cf "moon_needs_the_book_shut" "The moon with the right hand while the book is still open"
     "LangLib.World.Fight.moon_needs_the_book_shut" "¶01, the first 3 moves of ¶02, then the moon with the right hand"
     start (p1 ++ (p2.take 3 ++ [nn (.use chrollo sunMoon judge .right)])),
   cf "left_hand_while_holding_the_book" "Giving his own face (the right hand) with the book open"
     "LangLib.World.Fight.left_hand_while_holding_the_book" "¶01–03, open at Convert Hands, then the right hand on the spectator"
     start (p1 ++ p2 ++ p3 ++ [nn (.openBook chrollo convertHands), sp (.move chrollo stands), nn (.use chrollo convertHands fan .right)]),
   cf "gallery_fake_needs_the_bookmark" "Gallery Fake with the book open in his hand"
     "LangLib.World.Fight.gallery_fake_needs_the_bookmark" "¶01–04, open at Gallery Fake, then use it with both hands"
     start (p1 ++ p2 ++ p3 ++ p4 ++ [nn (.openBook chrollo galleryFake), nn (.use chrollo galleryFake c1 .both)]),
   cf "the_elders_nen_outlives_him" "Sun and Moon were not post-mortem Nen"
     "LangLib.World.Fight.the_elders_nen_outlives_him" "the whole fight, with Sun and Moon an ordinary stolen ability of a dead man"
     (startWith mortal) fight,
   cf "gyo_sees_in" "Chrollo never takes up Gyo"
     "LangLib.World.Fight.gyo_sees_in" "¶01–06 without Chrollo's Gyo"
     start (p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6.filter (· != nn (.tech chrollo .gyo))),
   cf "headless_bomb_needs_a_carrier" "No controlled copy to carry the headless bomb"
     "LangLib.World.Fight.headless_bomb_needs_a_carrier" "¶01–08 without the antenna in copy 3 or its order"
     start (p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7 ++
       p8.filter fun e => e != nn (.use chrollo blackVoice c3 .left) && e != nn (.order chrollo c3))]

def powerExport : Export :=
  { system := "nen", title := "Nen: Chrollo against Hisoka", story := "hxh-chrollo-hisoka"
    source := "LangLib/World/Examples/Fight.lean"
    actors := (Cast.all : List Ch).map fun c =>
      { id := nm c, name := chName c, kind := if isCopy c then "copy" else "person",
        of_ := if isCopy c then some (nm fan) else none }
    resources := [("aura", "aura", [("chrollo", start.nen.aura chrollo), ("hisoka", start.nen.aura hisoka)])]
    glossary := [("in", "In: hides aura from all but Gyo"), ("gyo", "Gyo: aura in the eyes, sees what In hides"),
      ("zetsu", "Zetsu: aura shut off"), ("ko", "Ko: all aura in one point"), ("ken", "Ken: aura spread to guard")]
    start := stateOf start
    moves := movesOf start tagged
    counterfactuals }

end LangLib.World.Fight
