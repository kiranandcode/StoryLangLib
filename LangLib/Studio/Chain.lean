import LangLib.Studio.End

/-!
# Chained chapters, proved: the next chapter opens where the last one ends

`langlib end` and `workflows.py chain-check` compare a chapter's end with the
next chapter's opening in the CLI. Here the same comparison is a theorem. Each
reading's state is projected to sorted lines of plain names (`mainLines`,
`xLines`, `consentLines`): where everyone is, what they hold, their bonds,
beliefs (with the evidence that holds them), goals and state atoms; ties,
needs, names, pronouns, secrets, feelings, examined and recognised anomalies and
conviction counts; what each has never done, and the kinds of relationship.
`langlib chain-lean <prev> <next> <ns>` writes `Chain.lean` into the next
chapter: the previous chapter's spec and readings as literals (each checked
against its files by `#guard`, through `include_str` of the previous
directory), the next chapter's spec, and three theorems proved by `decide
+kernel`, each replaying the previous chapter once:

* `chain_main : mainLines prev (run prev.start events) = mainLines next next.start`;
* `chain_ext : xLines prevX (xEnd prevX paras) = xLines nextX nextX.start`;
* `chain_consent : consentLines (run prevC prevEvs) = consentLines nextC`.

The projection forgets what does not cross a break by design: who perceived
what when, scenes, grants and plans in progress.
-/

namespace LangLib.Studio
open Lean LangLib LangLib.World

private def sortLines (l : List String) : List String :=
  sortBy (fun a b => decide (a ≤ b)) l.eraseDups

/-- The main reading's state as lines of names; state atoms only those in `states`. -/
def mainLines (s : Spec) (w : W s) (states : List String) : List String :=
  let n := s.names
  let isAtom : SFact s × Bool → Bool := fun l => match l.1.f with | .atom _ => true | _ => false
  let at_ := s.chs.filterMap fun c =>
    if (w.loc c).i < s.places.length then some s!"at {n.chS c.i} {n.plS (w.loc c).i}" else none
  let holds := (List.range s.objects.length).filterMap fun o =>
    (w.holder ⟨o⟩).map fun c => s!"holds {n.obS o} {n.chS c.i}"
  let objAt := (List.range s.objects.length).filterMap fun o =>
    if (w.holder ⟨o⟩).isNone && w.objKnown.contains ⟨o⟩ then some s!"objAt {n.obS o} {n.plS (w.objLoc ⟨o⟩).i}" else none
  let bonds := (pairs s).flatMap fun (a, b) => dims.filterMap fun d =>
    let v := HasBonds.bond w a b d
    if v > 0 then some s!"bond {n.chS a.i}>{n.chS b.i} {d.name} {v}" else none
  let knows := s.chs.flatMap fun c =>
    ((view w c).filter isAtom).map fun l => s!"knows {n.chS c.i} {heldShown s w c l}"
  let goals := s.chs.flatMap fun c => (goalsOf w c).map fun g => s!"goal {n.chS c.i} {n.litS (unlit g)}"
  let st := (s.atoms.zipIdx.filter fun (a, _) => a.state && states.contains a.id).map fun (a, i) =>
    s!"state {a.id} {w.atomNow i}"
  sortLines (at_ ++ holds ++ objAt ++ bonds ++ knows ++ goals ++ st)

/-- The ext reading's state as lines of names (what a chapter break carries). -/
def xLines (x : XSpec) (w : XW x) : List String :=
  let ch := x.chS
  let emo (e : Nat) := x.emotions.getD e s!"?{e}"
  let tieS (r : Nat) := (x.ties[r]?.map (·.id)).getD "?"
  sortLines <|
    (w.needs.flatMap fun (c, ks) => ks.map fun k => s!"need {ch c} {x.needs.getD k.i "?"}") ++
    ((w.ties.filter (·.2.2.2 > 0)).map fun (r, a, b, n) => s!"tie {ch a} {tieS r} {ch b} {n}") ++
    (w.names.map fun (a, b, n) => s!"name {ch a.i} {ch b.i} {n}") ++
    (w.pron.map fun (a, b, p) => s!"pron {ch a.i} {ch b.i} {p.name}") ++
    (w.secrets.map fun (a, b, s) => s!"secret {ch a.i} {ch b.i} {s}") ++
    ((w.affect.filter (·.2.2 > 0)).map fun (c, e, n) => s!"feel {ch c} {emo e} {n}") ++
    (w.examined.map fun (c, e, n) => s!"examined {ch c.i} {emo e.i} {n}") ++
    (w.recognised.map fun (c, e) => s!"recognised {ch c.i} {emo e.i}") ++
    (w.data.map fun (c, q, n) => s!"data {ch c.i} {q} {n}") ++
    (w.dismissed.map fun (c, q, n) => s!"dismissed {ch c.i} {q} {n}") ++
    (w.conceded.map fun (c, q) => s!"conceded {ch c.i} {q}")

/-- The consent reading's state as lines: what each has never done, and the kinds that hold. -/
def consentLines (n : Names) (w : CWorld) : List String :=
  let never := w.c.never.filter fun (ch, x) => !w.c.done.any fun (p, q, y) => y == x && (p == ch || q == ch)
  sortLines <|
    (never.map fun (c, x) => s!"never {n.chS c} {x.name}") ++
    (w.r.holds.map fun (a, b, k) =>
      let (a, b) := if a ≤ b then (a, b) else (b, a)
      s!"rel {n.chS a} {n.chS b} {k.name}")

/-- The opening of a story's consent reading, from its story.json (as `loadConsent` reads it). -/
def consentStartOf (story : String) : Option CWorld := Id.run do
  let .ok j := Json.parse story | return none
  let .ok s := specOfJson j | return none
  let n := s.names
  let cj := (j.getObjVal? "consent").toOption.getD (Json.mkObj [])
  let never : Except String (List (Nat × Intim)) := match cj.getObjVal? "never" with
    | .ok (.obj kvs) => kvs.toList.flatMapM fun (c, v) => do
      let ci ← n.ch c
      ((v.getArr?.toOption.getD #[]).toList.filterMap (·.getStr?.toOption)).mapM fun x => do pure (ci, ← n.intim x)
    | _ => pure []
  let rels : Except String (List (Nat × Nat × RelKind)) := match cj.getObjVal? "relations" with
    | .ok (.arr rs) => rs.toList.mapM fun r => do
      match (r.getArr?.toOption.getD #[]).toList.filterMap (·.getStr?.toOption) with
      | [a, b, k] => pure (← n.ch a, ← n.ch b, ← n.relKind k)
      | _ => throw "a relation is [a, b, kind]"
    | _ => pure []
  match never, rels with
  | .ok nv, .ok rl => some { c := { never := nv }, r := { holds := rl } }
  | _, _ => none

/-- A paragraph's reading (or plan) still gives these consent events. -/
def cevsMatch (story para : String) (evs : List CEv) : Bool :=
  match Json.parse story >>= specOfJson, Json.parse para with
  | .ok s, .ok j =>
    let lines := match j.getObjVal? "consent" with
      | .ok (.arr a) => a.toList.filterMap fun (e : Json) => e.getStr?.toOption <|> (e.getObjValAs? String "e").toOption
      | _ => []
    (lines.mapM s.names.cev).toOption == some evs
  | _, _ => false

private def rs {α : Type} [Repr α] (a : α) : String := (repr a).pretty 1000000
private def lean (s : String) : String := ((s.replace "LangLib.Studio." "").replace "LangLib.World." "")

/-- `langlib chain-lean <prev> <next> <ns>`: the link between two chapters as a Lean file. -/
def chainLean (prev next : System.FilePath) (ns : String) : IO String := do
  let pl ← loadStory prev
  let nl ← loadStory next
  let ps := pl.spec
  let (story, _) := storyOf (s := ps) pl.paras
  let some timed := story.solved | throw (IO.userError "the previous chapter's time constraints have no solution")
  let told : List Nat := List.range story.told.length
  if timed.timeline.byEffect != told then
    throw (IO.userError "the previous chapter is told out of order; chain-lean replays it in told order")
  let up := s!"../{prev.fileName.getD ""}"
  let rel (p : String) := s!"{up}/{p}"
  let states := ps.atoms.filter (·.state) |>.map (·.id)
  let mut out := s!"import LangLib.Studio\n\n/-!\n# {ns}: this chapter opens where {prev.fileName.getD ""} ends\n\n" ++
    "Generated by `langlib chain-lean`. The previous chapter's spec and readings are restated as\n" ++
    "literals and `#guard`ed against its files; each theorem replays it once (`LangLib/Studio/Chain.lean`).\n-/\n\n" ++
    s!"namespace {ns}\nopen LangLib.World LangLib.Studio\n\nset_option maxRecDepth 100000\n\n"
  out := out ++ s!"def prevSpec : Spec := {lean (rs ps)}\n#guard specMatches (include_str \"{rel "story.json"}\") prevSpec\n\n"
  let mut names : List String := []
  for p in pl.paras do
    let src := if p.items.any (·.src != "plan") then s!"paragraphs/{p.name}.events.json" else s!"paragraphs/{p.name}.plan.json"
    out := out ++ s!"def q{p.name} : List Ev := {lean (rs (p.items.map (·.ev)))}\n" ++
      s!"#guard eventsMatch prevSpec (include_str \"{rel src}\") q{p.name}\n"
    names := names ++ [s!"q{p.name}"]
  out := out ++ s!"\ndef prevEvs : List Ev := {if names.isEmpty then "[]" else " ++ ".intercalate names}\n"
  out := out ++ s!"\ndef nextSpec : Spec := {lean (rs nl.spec)}\n#guard specMatches (include_str \"story.json\") nextSpec\n\n"
  out := out ++ s!"def states : List String := {rs states}\n\n"
  out := out ++ "/-- The main reading: where everyone is, what they hold and believe, bonds, goals, states. -/\n" ++
    "theorem chain_main : mainLines prevSpec (run prevSpec.start (prevEvs.map (Ev.toE prevSpec))) states =\n" ++
    "    mainLines nextSpec nextSpec.start states := by decide +kernel\n\n"
  -- the ext reading
  let (s1, x1, xps) ← extInputs prev.toString
  let (_, _, _, beats) ← extParas prev.toString
  let paras ← (xps.zip beats).mapM fun ((_, ej, d), b) => match xparaOfAt s1 x1 b ej d with
    | .ok p => pure p | .error e => throw (IO.userError e)
  let (_, x2, _) ← extInputs next.toString
  out := out ++ s!"def prevX : XSpec := {rs x1}\n#guard xspecMatches (include_str \"{rel "story.json"}\") prevX\n\n"
  for (((nm, ej, d), p), b) in (xps.zip paras).zip beats do
    out := out ++ s!"def x{nm} : XPara prevX := {rs p}\n"
    if ej.isSome && d.isSome then
      out := out ++ s!"#guard xparaMatchesAt prevX (include_str \"{rel "story.json"}\") {rs b} " ++
        s!"(include_str \"{rel s!"paragraphs/{nm}.events.json"}\") (include_str \"{rel s!"paragraphs/{nm}.json"}\") x{nm}\n"
  out := out ++ s!"def prevParas : List (XPara prevX) := [{", ".intercalate (xps.map fun (nm, _, _) => s!"x{nm}")}]\n\n"
  out := out ++ s!"def nextX : XSpec := {rs x2}\n#guard xspecMatches (include_str \"story.json\") nextX\n\n"
  out := out ++ "/-- The ext reading: ties, needs, names, secrets, feelings, anomalies, convictions. -/\n" ++
    "theorem chain_ext : xLines prevX (xEnd prevX prevParas) = xLines nextX nextX.start := by decide +kernel\n\n"
  -- the consent reading
  let pc ← loadConsent prev
  let nc ← loadConsent next
  out := out ++ s!"def prevC : CWorld := {lean (rs pc.start)}\n" ++
    s!"#guard consentStartOf (include_str \"{rel "story.json"}\") == some prevC\n"
  let mut cnames : List String := []
  for (nm, evs) in pc.paras do
    let src := if ← (prev / "paragraphs" / s!"{nm}.events.json").pathExists then s!"paragraphs/{nm}.events.json" else s!"paragraphs/{nm}.plan.json"
    out := out ++ s!"def k{nm} : List CEv := {lean (rs (evs.map (·.2)))}\n" ++
      s!"#guard cevsMatch (include_str \"{rel "story.json"}\") (include_str \"{rel src}\") k{nm}\n"
    cnames := cnames ++ [s!"k{nm}"]
  out := out ++ s!"def prevCEvs : List CEv := {if cnames.isEmpty then "[]" else " ++ ".intercalate cnames}\n"
  out := out ++ s!"def nextC : CWorld := {lean (rs nc.start)}\n#guard consentStartOf (include_str \"story.json\") == some nextC\n\n"
  out := out ++ "/-- The consent reading: what each has never done, the kinds of relationship. -/\n" ++
    "theorem chain_consent : consentLines prevSpec.names (run prevC prevCEvs) = consentLines nextSpec.names nextC := by\n" ++
    "  decide +kernel\n"
  pure (out ++ s!"\nend {ns}\n")

end LangLib.Studio
