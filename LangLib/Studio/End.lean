import LangLib.Studio.Load
import LangLib.Studio.Ext
import LangLib.Studio.Consent

/-!
# A story's end state, as the opening of the next chapter

A long story outgrows one directory: every proof and every check replays its
paragraphs, so their cost grows with the story. A series is written as
chained directories instead, chapter `n` opening where chapter `n − 1` ends.
`langlib end <dir>` prints the end state of a directory's three readings in
the vocabulary `story.json` opens with, so the next chapter's opening can be
written from it (and checked against it: `studio/workflows.py chain-check`):

* `start`: where everyone is, what they hold, their bonds, what they believe
  (their views, as their own knowledge: the evidence behind a belief does not
  cross a chapter break) and their goals; `states`: the state atoms' values;
* `ext`: ties, needs, names, pronouns, secrets, feelings, the anomalies
  examined and recognised, and the convictions' signs and concessions;
* `consent`: what each character has still never done, and the kinds of
  relationship that hold.

Paragraphs not yet written are read from their plans, so a series can be
chained, and its plot checked, before any prose.
-/

namespace LangLib.Studio
open Lean LangLib LangLib.World

/-- The ext reading walked to its end, every event applied (as `xreport` walks it). -/
def xEnd (x : XSpec) (ps : List (XPara x)) : XW x :=
  ps.foldl (fun w p => p.events.foldl (fun w (_, e) => slowNote x w (Domain.step w e) p.beat e) w) x.start

private def sArr (xs : List String) : Json := Json.arr (xs.map Json.str).toArray

def xEndJson (x : XSpec) (w : XW x) : Json :=
  let ch := x.chS
  let emo (e : Nat) := x.emotions.getD e s!"?{e}"
  Json.mkObj [
    ("needs", Json.mkObj (w.needs.filterMap fun (c, ks) =>
      if ks.isEmpty then none else some (ch c, sArr (ks.map fun k => x.needs.getD k.i "?")))),
    ("ties", Json.arr ((w.ties.filter (·.2.2.2 > 0)).reverse.map fun (r, a, b, n) =>
      sArr [ch a, (x.ties[r]?.map (·.id)).getD "?", ch b, toString n]).toArray),
    ("names", Json.arr (w.names.reverse.map fun (a, b, n) => sArr [ch a.i, ch b.i, n]).toArray),
    ("pron", Json.arr (w.pron.reverse.map fun (a, b, p) => sArr [ch a.i, ch b.i, p.name]).toArray),
    ("secrets", Json.arr (w.secrets.reverse.map fun (a, b, s) => sArr [ch a.i, ch b.i, s]).toArray),
    ("feels", Json.arr ((w.affect.filter (·.2.2 > 0)).reverse.map fun (c, e, n) => sArr [ch c, emo e, toString n]).toArray),
    ("examined", Json.arr (w.examined.reverse.map fun (c, e, n) => sArr [ch c.i, emo e.i, toString n]).toArray),
    ("recognised", Json.arr (w.recognised.reverse.map fun (c, e) => sArr [ch c.i, emo e.i]).toArray),
    ("data", Json.arr (w.data.reverse.map fun (c, q, n) => sArr [ch c.i, q, toString n]).toArray),
    ("dismissed", Json.arr (w.dismissed.reverse.map fun (c, q, n) => sArr [ch c.i, q, toString n]).toArray),
    ("conceded", Json.arr (w.conceded.reverse.map fun (c, q) => sArr [ch c.i, q]).toArray)]

/-- The main reading walked to its end, in story-time order (as `report` walks it). -/
def mainEnd (l : Loaded) : W l.spec :=
  let s := l.spec
  let (story, _) := storyOf (s := s) l.paras
  let order : List Nat := match story.solved with
    | some t => if decide (t.timeline.Satisfies story.constraints) && story.metric.all (·.sat t.timeline)
        then t.timeline.byEffect else List.range story.told.length
    | none => List.range story.told.length
  (walk s.start (order.filterMap fun i => (story.told[i]?).map (i, ·))).2

def mainEndJson (s : Spec) (w : W s) : Json :=
  let n := s.names
  let onstage := s.chs.filter fun c => (w.loc c).i < s.places.length
  let isAtom : SFact s × Bool → Bool := fun l => match l.1.f with | .atom _ => true | _ => false
  Json.mkObj [
    ("start", Json.mkObj [
      ("at", Json.mkObj (onstage.map fun c => (n.chS c.i, Json.str (n.plS (w.loc c).i)))),
      ("holds", Json.mkObj ((List.range s.objects.length).filterMap fun o =>
        (w.holder ⟨o⟩).map fun c => (n.obS o, Json.str (n.chS c.i)))),
      ("objAt", Json.mkObj ((List.range s.objects.length).filterMap fun o =>
        if (w.holder ⟨o⟩).isNone && w.objKnown.contains ⟨o⟩ then some (n.obS o, Json.str (n.plS (w.objLoc ⟨o⟩).i)) else none)),
      ("bonds", Json.mkObj ((pairs s).filterMap fun (a, b) =>
        let ds := dims.filterMap fun d => let v := HasBonds.bond w a b d; if v > 0 then some (d.name, Json.num v) else none
        if ds.isEmpty then none else some (s!"{n.chS a.i}>{n.chS b.i}", Json.mkObj ds))),
      -- each belief with the evidence that holds it: own knowledge stays plain, the rest keep
      -- their rank and evidence ("lit@rank:evidence"), so later evidence weighs against them as before
      ("knows", Json.mkObj (s.chs.filterMap fun c =>
        let ls := ((view w c).filter isAtom).eraseDups
        let shown (l : SFact s × Bool) : String :=
          let hs := (HasMinds.beliefs w c).filter fun h => litOf h.b == some l && h.up != .note
          match hs.foldl (fun (best : Option (Held (Ch s) (SFact s))) h =>
              match best with | some b => if h.rank > b.rank then some h else some b | none => some h) none with
          | some h => if h.src == .self || h.up == .hard then n.litS (unlit l)
              else s!"{n.litS (unlit l)}@{h.rank}:{n.evidS (Evid.ofCh h.src)}"
          | none => n.litS (unlit l)
        if ls.isEmpty then none else some (n.chS c.i, sArr (ls.map shown)))),
      ("goals", Json.mkObj (s.chs.filterMap fun c =>
        let gs := goalsOf w c
        if gs.isEmpty then none else some (n.chS c.i, sArr (gs.map fun g => n.litS (unlit g)))))]),
    ("states", Json.mkObj ((s.atoms.zipIdx.filter (·.1.state)).map fun (a, i) => (a.id, Json.bool (w.atomNow i))))]

def consentEndJson (c : ConsentStory) : Json :=
  let w := run c.start c.events
  let n := c.names
  let never := w.c.never.filter fun (ch, x) => !w.c.done.any fun (p, q, y) => y == x && (p == ch || q == ch)
  let who := (never.map (·.1)).eraseDups
  Json.mkObj [
    ("never", Json.mkObj (who.map fun ch => (n.chS ch, sArr ((never.filter (·.1 == ch)).map (·.2.name))))),
    ("relations", Json.arr (w.r.holds.reverse.map fun (a, b, k) => sArr [n.chS a, n.chS b, k.name]).toArray)]

/-- `langlib end <dir>`. -/
def endReport (dir : String) : IO Json := do
  let l ← loadStory dir
  let main := mainEndJson l.spec (mainEnd l)
  let (s, x, ps) ← extInputs dir
  let (_, _, _, beats) ← extParas dir
  let paras ← (ps.zip beats).mapM fun ((_, ej, d), b) => match xparaOfAt s x b ej d with
    | .ok p => pure p | .error e => throw (IO.userError e)
  let c ← loadConsent dir
  pure ((main.setObjVal! "ext" (xEndJson x (xEnd x paras))).setObjVal! "consent" (consentEndJson c))

end LangLib.Studio
