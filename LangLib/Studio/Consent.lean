import Lean.Data.Json
import LangLib.Studio.Parse
import LangLib.World.Consent
import LangLib.World.Relationship

/-!
# The refined consent reading of a story directory

The Studio's world checks `Social`'s five coarse acts. A story can also give
each paragraph a finer consent reading, checked here with `World/Consent`
and `World/Relationship`: in `paragraphs/NN.events.json`,

```
"consent": ["ask robin remy undressTop", "grant remy robin undressTop nod",
            "act robin remy undressTop", "offer remy robin", "take robin remy choke,gag",
            "command robin remy", "checkIn robin remy finger", "grant remy robin finger verbal",
            "wish remy robin penetrate", "withdraw remy robin kiss", "stop remy robin",
            "grant remy robin finishInside verbal once", "close robin remy care",
            "propose robin remy partners", "accept remy robin partners", "consummate robin remy"]
```

(signals: `verbal nod invite blanket pressured`; `once` makes a grant used up
by the act; `take D S` lists the sub's limits, comma-separated, or nothing).
`story.json` may add `"consent": {"never": {"remy": ["penetrate"]},
"relations": [["remy", "robin", "bestFriends"]]}`: what each character had
never done when the story opened, and the kinds of relationship that held.

`langlib consent <dir>` prints each paragraph's verdicts (yes / no / assumed,
with why), the assumptions, firsts and relationship kinds at the end;
`langlib consent <dir> --lean <ns>` prints the same as a Lean file whose
theorems are proved by `decide +kernel`. Characters are the story's, by index.
-/

namespace LangLib.Studio
open Lean LangLib.World

inductive CEv | c (x : ConsentEv Nat) | r (x : RelEv Nat)
  deriving DecidableEq, Repr

structure CWorld where
  c : ConsentState Nat
  r : RelState Nat
  deriving DecidableEq, Repr

instance : HasConsent CWorld Nat := ⟨CWorld.c, fun w s => { w with c := s }⟩
instance : HasRel CWorld Nat := ⟨CWorld.r, fun w s => { w with r := s }⟩

instance : Domain CWorld CEv where
  ok w | .c x => Domain.ok w x | .r x => Domain.ok w x
  ok3 w | .c x => Domain.ok3 w x | .r x => Domain.ok3 w x
  step w | .c x => Domain.step w x | .r x => Domain.step w x
  why w | .c x => Domain.why w x | .r x => Domain.why w x

instance : Perceive CWorld CEv := Perceive.none

def _root_.LangLib.World.RelKind.ofString? (s : String) : Option RelKind :=
  [RelKind.acquaintances, .friends, .bestFriends, .lovers, .partners, .exclusive].find? (·.name == s)

def _root_.LangLib.World.Signal.ofString? : String → Option Signal
  | "verbal" => some .verbal | "nod" => some .nod | "invite" => some .invite
  | "blanket" => some .blanket | "pressured" => some .pressured | _ => none

def _root_.LangLib.World.Signal.name : Signal → String
  | .verbal => "verbal" | .nod => "nod" | .invite => "invite" | .blanket => "blanket"
  | .pressured => "pressured"

private def need {α} (what s : String) : Option α → Except String α
  | some a => pure a | none => throw s!"unknown {what} \"{s}\""

def Names.intim (_ : Names) (s : String) : Except String Intim := need "act" s (Intim.ofString? s)
def Names.relKind (_ : Names) (s : String) : Except String RelKind := need "relationship" s (RelKind.ofString? s)

def Names.cev (n : Names) (str : String) : Except String CEv := do
  let x := n.intim
  match (str.splitOn " ").filter (· != "") with
  | ["ask", a, b, i] => return .c (.ask (← n.ch a) (← n.ch b) (← x i))
  | "grant" :: b :: a :: i :: sg :: rest =>
    return .c (.grant (← n.ch b) (← n.ch a) (← x i) (← need "signal" sg (Signal.ofString? sg)) (rest == ["once"]))
  | ["withdraw", b, a, i] => return .c (.withdraw (← n.ch b) (← n.ch a) (← x i))
  | ["stop", b, a] => return .c (.stop (← n.ch b) (← n.ch a))
  | ["offer", s, d] => return .c (.offer (← n.ch s) (← n.ch d))
  | ["take", d, s] => return .c (.take (← n.ch d) (← n.ch s) [])
  | ["take", d, s, lim] => return .c (.take (← n.ch d) (← n.ch s) (← ((lim.splitOn ",").filter (· != "")).mapM x))
  | ["command", d, s] => return .c (.command (← n.ch d) (← n.ch s))
  | ["checkIn", a, b, i] => return .c (.checkIn (← n.ch a) (← n.ch b) (← x i))
  | ["act", a, b, i] => return .c (.act (← n.ch a) (← n.ch b) (← x i))
  | ["close", d, s, c] => return .c (.close (← n.ch d) (← n.ch s) (c == "care"))
  | ["wish", c, d, i] => return .c (.wish (← n.ch c) (← n.ch d) (← x i))
  | ["propose", a, b, k] => return .r (.propose (← n.ch a) (← n.ch b) (← n.relKind k))
  | ["accept", b, a, k] => return .r (.accept (← n.ch b) (← n.ch a) (← n.relKind k))
  | ["decline", b, a, k] => return .r (.decline (← n.ch b) (← n.ch a) (← n.relKind k))
  | ["end", a, b, k] => return .r (.end (← n.ch a) (← n.ch b) (← n.relKind k))
  | ["consummate", a, b] => return .r (.consummate (← n.ch a) (← n.ch b))
  | _ => throw s!"cannot read consent event \"{str}\""

/-- A consent event as Lean source (characters by index). -/
def CEv.lean : CEv → String
  | .c (.ask a b x) => s!".c (.ask {a} {b} .{x.name})"
  | .c (.grant b a x s o) => s!".c (.grant {b} {a} .{x.name} .{s.name} {o})"
  | .c (.withdraw b a x) => s!".c (.withdraw {b} {a} .{x.name})"
  | .c (.stop b a) => s!".c (.stop {b} {a})"
  | .c (.offer s d) => s!".c (.offer {s} {d})"
  | .c (.take d s l) => s!".c (.take {d} {s} [{", ".intercalate (l.map fun (i : Intim) => s!".{i.name}")}])"
  | .c (.command d s) => s!".c (.command {d} {s})"
  | .c (.checkIn a b x) => s!".c (.checkIn {a} {b} .{x.name})"
  | .c (.act a b x) => s!".c (.act {a} {b} .{x.name})"
  | .c (.close d s care) => s!".c (.close {d} {s} {care})"
  | .c (.wish p d x) => s!".c (.wish {p} {d} .{x.name})"
  | .r (.propose a b k) => s!".r (.propose {a} {b} .{k.name})"
  | .r (.accept b a k) => s!".r (.accept {b} {a} .{k.name})"
  | .r (.decline b a k) => s!".r (.decline {b} {a} .{k.name})"
  | .r (.end a b k) => s!".r (.end {a} {b} .{k.name})"
  | .r (.consummate a b) => s!".r (.consummate {a} {b})"

structure ConsentStory where
  names : Names
  start : CWorld
  /-- per paragraph: its name and its consent events -/
  paras : List (String × List (String × CEv))

private def readJ (p : System.FilePath) : IO (Option Json) := do
  if !(← p.pathExists) then return none
  match Json.parse (← IO.FS.readFile p) with
  | .ok j => return some j
  | .error e => throw (IO.userError s!"{p}: {e}")

def loadConsent (dir : System.FilePath) : IO ConsentStory := do
  let some sj ← readJ (dir / "story.json") | throw (IO.userError s!"no story.json in {dir}")
  let spec ← IO.ofExcept (specOfJson sj)
  let n := spec.names
  let cj := (sj.getObjVal? "consent").toOption.getD (Json.mkObj [])
  let never ← match cj.getObjVal? "never" with
    | .ok (.obj kvs) => kvs.toList.flatMapM fun (c, v) => do
      let ci ← IO.ofExcept (n.ch c)
      let xs := ((v.getArr?.toOption.getD #[]).toList.filterMap (·.getStr?.toOption))
      xs.mapM fun x => do pure (ci, ← IO.ofExcept (n.intim x))
    | _ => pure []
  let rels ← match cj.getObjVal? "relations" with
    | .ok (.arr rs) => rs.toList.mapM fun r => do
      match (r.getArr?.toOption.getD #[]).toList.filterMap (·.getStr?.toOption) with
      | [a, b, k] => pure (← IO.ofExcept (n.ch a), ← IO.ofExcept (n.ch b), ← IO.ofExcept (n.relKind k))
      | _ => throw (IO.userError "a relation is [a, b, kind]")
    | _ => pure []
  let pdir := dir / "paragraphs"
  let files ← if ← pdir.pathExists then pdir.readDir else pure #[]
  let names := (files.toList.filterMap fun e =>
    if e.fileName.endsWith ".events.json" then some ((e.fileName.splitOn ".").head!) else none).mergeSort (· ≤ ·)
  let paras ← names.mapM fun nm => do
    let some ej ← readJ (pdir / s!"{nm}.events.json") | pure (nm, [])
    let lines := match ej.getObjVal? "consent" with
      | .ok (.arr a) => a.toList.filterMap fun (j : Json) => j.getStr?.toOption <|> (j.getObjValAs? String "e").toOption
      | _ => []
    let evs ← lines.mapM fun l => do
      match n.cev l with
      | .ok e => pure (l, e)
      | .error m => throw (IO.userError s!"{nm}: {m}")
    pure (nm, evs)
  pure { names := n, start := { c := { never }, r := { holds := rels } }, paras }

def ConsentStory.events (s : ConsentStory) : List CEv := s.paras.flatMap (·.2.map (·.2))

def consentTriName : Tri → String | .yes => "yes" | .no => "no" | .unknown => "assumed"

def consentReport (dir : System.FilePath) : IO Json := do
  let s ← loadConsent dir
  let mut w := s.start
  let mut out : Array Json := #[]
  for (nm, evs) in s.paras do
    let mut items : Array Json := #[]
    for (l, e) in evs do
      let t := Domain.ok3 w e
      items := items.push (Json.mkObj ([("e", toJson l), ("status", toJson (consentTriName t))] ++
        (if t == .yes then [] else [("why", toJson (Domain.why w e))])))
      w := next w e
    if !evs.isEmpty then out := out.push (Json.mkObj [("name", toJson nm), ("events", Json.arr items)])
  let es := s.events
  let cs := es.filterMap fun | .c x => some x | _ => none
  let n := s.names
  let pairs := (List.range n.chars.length).flatMap fun a =>
    (List.range n.chars.length).filterMap fun b =>
      if a < b && (!(w.r.kinds a b).isEmpty || !(w.r.pending a b).isEmpty) then some (a, b) else none
  pure <| Json.mkObj [
    ("paragraphs", Json.arr out),
    ("plausible", toJson (plausibleB s.start es)),
    ("valid", toJson (validB s.start es)),
    ("assumptions", toJson ((assumptions s.start es 0).map fun (i, why) => Json.mkObj [("i", toJson i), ("why", toJson why)])),
    ("firsts", toJson ((firsts s.start.c cs 0).map fun (_, c, x) => s!"{n.chS c} {x.name}")),
    ("relations", toJson (pairs.map fun (a, b) => Json.mkObj [
      ("pair", toJson s!"{n.chS a} {n.chS b}"),
      ("kinds", toJson ((w.r.kinds a b).map RelKind.name)),
      ("pending", toJson ((w.r.pending a b).map RelKind.name))])),
    ("cared", toJson w.c.cared)]

/-- The consent reading as a Lean file; its theorems are the report's verdicts. -/
def consentLean (dir : System.FilePath) (ns : String) : IO String := do
  let s ← loadConsent dir
  let es := s.events
  let w := run s.start es
  let n := s.names
  let ks (l : List RelKind) := "[" ++ ", ".intercalate (l.map fun k => s!".{k.name}") ++ "]"
  let lines := s.paras.filterMap fun (nm, evs) =>
    if evs.isEmpty then none else
    some (s!"  -- {nm}\n" ++ ",\n".intercalate (evs.map fun (_, e) => s!"  {e.lean}"))
  let never := ", ".intercalate (s.start.c.never.map fun (c, x) => s!"({c}, .{x.name})")
  let rels := ", ".intercalate (s.start.r.holds.map fun (a, b, k) => s!"({a}, {b}, .{k.name})")
  let asm := assumptions s.start es 0
  let pair := (List.range n.chars.length).flatMap fun a => (List.range n.chars.length).filterMap fun b =>
    if a < b && !(w.r.kinds a b).isEmpty then some (a, b) else none
  let relThms := pair.map fun (a, b) =>
    s!"theorem kinds_{n.chS a}_{n.chS b} : (run start story).r.kinds {a} {b} = {ks (w.r.kinds a b)} ∧\n" ++
    s!"    (run start story).r.pending {a} {b} = {ks (w.r.pending a b)} := by decide +kernel\n"
  pure <| s!"import LangLib.Studio.Consent

/-! Generated by `langlib consent <dir> --lean {ns}`: the story's consent reading
and its verdicts. Characters: {", ".intercalate ((n.chars.zipIdx).map fun (c, i) => s!"{i} = {c}")}. -/

namespace {ns}
open LangLib.World LangLib.Studio

def start : CWorld := \{ c := \{ never := [{never}] }, r := \{ holds := [{rels}] } }

def story : List CEv := [
{",\n".intercalate lines}]

theorem plausible : {if plausibleB s.start es then "" else "¬ "}(start ⊨? story) := by decide +kernel
theorem valid : {if validB s.start es then "" else "¬ "}(start ⊨ story) := by decide +kernel
theorem assumed : (assumptions start story 0).map (·.1) = {(asm.map (·.1))} := by decide +kernel
theorem cared : (run start story).c.cared = {w.c.cared} := by decide +kernel
" ++ "\n".intercalate relThms ++ s!"\nend {ns}\n"

end LangLib.Studio
