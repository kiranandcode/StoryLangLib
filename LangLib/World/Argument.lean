import LangLib.World.Mind

/-!
# Argument: a paper read as a story

A paper is a story whose plot is its argument. The characters are the voices
of the argument (`Voice`): the reader, the authors, the prior work they cite,
and the data their evaluation measured. The lore is what the reader brings
(background terms they already know). The events are rhetorical moves
(`Move`): claim, cite, define, motivate, example, contrast, promise (a forward
reference), deliver (its payoff), concede, evaluate, and the listing of a
contribution, which is a promise the paper makes about itself. Three moves
read what plain claims miss: `deny` (an antithesis when nobody put the denied
proposition forward, a contrast when someone did), `hedge` (a stance that
leaves the reader an open question, answered by a later `deliver` or
`evaluate`), and `infer` (a claim with stated reasons, supported when every
reason is granted: an accepted claim, a definition or background). A
proposition counts as put forward when the reader holds it, its negation, or
derives it through the paper's lore rules (an objection the reader would
raise), so rebutting it is a contrast, not an antithesis.

**The reader's mind.** Everything the reader comes to hold goes into their
evidence base through `Mind.learn`, with its source: a definition, a claim, a
concession or a promise is the authors' word (`told author`), a citation is a
second-hand report from prior work (`relayed prior`), a worked example is the
reader's own inference (`inferred`), and an evaluation is the data's word
(`told data`). `argCredence` weighs them: the authors' bare word on a claim
(strength 3) falls short of acceptance (4), so the reader holds it only
conservatively; a citation, an example or a measurement lifts it to an
outright (radical) belief. A claim is *supported* when the reader holds it
radically (`accepted`), so `Mind.explain` says why each claim stands.

**Validity** (`Domain.ok`, so `Valid start moves` is decidable): every term a
move uses is lore, already defined, promised and not yet delivered, or a claim
already made (no use before definition); a promise points forward; a delivery pays off an open
promise; sections only go forward.

**Coherence at the end** (`gaps`): every claim is supported or its support is
promised to a section outside the excerpt; every promise inside the excerpt is
delivered; every listed contribution is delivered (or deferred) and was
motivated (it, or a term it builds on, was motivated). `Coherent start moves := Valid start moves ∧ gapsOf (run start moves) = []`.
-/

namespace LangLib.World.Argument
open LangLib.World

/-- The characters of an argument. -/
inductive Voice | reader | author | prior | data
  deriving DecidableEq, Repr

instance : Cast Voice := ⟨[.reader, .author, .prior, .data]⟩

/-- What the reader can come to hold. -/
inductive AFact (T : Type) where
  /-- the reader knows what `t` means -/
  | known (t : T)
  /-- claim `k` is true -/
  | holds (k : T)
  /-- the reader has been shown why `k` matters -/
  | motivated (k : T)
  /-- the reader has been told `t` is coming -/
  | promised (t : T)
  deriving DecidableEq, Repr

/-- Rhetorical moves. Each lists the terms it `uses`. -/
inductive Move (T : Type) where
  | claim (k : T) (uses : List T)
  | cite (k : T) (uses : List T)
  | define (t : T) (uses : List T)
  | motivate (k : T) (uses : List T)
  | «example» (k : T) (uses : List T)
  | contrast (a b : T) (uses : List T)
  /-- a forward reference to section `sec` (0: later, unspecified) -/
  | promise (t : T) (sec : Nat) (uses : List T)
  /-- a listed contribution, delivered in section `sec` -/
  | contribute (k : T) (sec : Nat) (uses : List T)
  | deliver (t : T) (uses : List T)
  /-- the authors admit that `k` does not hold (a limitation) -/
  | concede (k : T) (uses : List T)
  /-- the authors deny `k` to set up what replaces it ("not X; Y"): an
  antithesis when nobody put `k` forward, a contrast when someone did -/
  | deny (k : T) (uses : List T)
  /-- a hedge or stance that leaves the reader with an open question about `k`
  ("At least, that is the hope."), answered by a later `deliver` or `evaluate`
  of `k`, in section `sec` (0: later, unspecified) -/
  | hedge (k : T) (sec : Nat) (uses : List T)
  /-- claim `k`, giving `premises` as its reasons ("because", "so", "therefore") -/
  | infer (k : T) (premises : List T) (uses : List T)
  | evaluate (k : T) (uses : List T)
  /-- a section heading: the argument is now in section `n` -/
  | heading (n : Nat)
  deriving DecidableEq, Repr

structure Pending (T : Type) where
  t : T
  sec : Nat
  contribution : Bool := false
  /-- an open question from a hedge -/
  hedge : Bool := false
  /-- the terms a contribution builds on -/
  uses : List T := []
  deriving DecidableEq, Repr

/-- The state of an argument: the reader's evidence base and the paper's
open obligations. -/
structure AW (T : Type) where
  base : List (Held Voice (AFact T)) := []
  pending : List (Pending T) := []
  delivered : List T := []
  claims : List T := []
  contributions : List (T × List T) := []
  /-- each denial, and whether it denied something nobody put forward -/
  denials : List (T × Bool) := []
  /-- the section the argument is in -/
  sec : Nat := 0
  /-- the sections the excerpt covers; obligations aimed elsewhere are deferred -/
  excerpt : List Nat := []
  now : Nat := 0
  deriving Repr

variable {T : Type} [DecidableEq T] [Lore (AFact T)]

instance : HasMinds (AW T) Voice (AFact T) where
  beliefs w c := if c == .reader then w.base else []
  setBeliefs w c hs := if c == .reader then { w with base := hs } else w

instance : HasLoc (AW T) Voice Unit := ⟨fun _ _ => ()⟩
/-- The argument world does not judge whether claims are true, only whether
the reader was given grounds to hold them. -/
instance : Truth (AW T) (AFact T) := ⟨fun _ _ => true⟩
instance : Clock (AW T) := ⟨AW.now, fun w => { w with now := w.now + 1 }⟩

/-- The words for the reader's reasons (`Reason.custom i`). -/
instance : ReasonText (AFact T) := ⟨["a definition is a stipulation", "a promise is about the text itself", "a motivation asks only for attention", "the authors rule it out", "published prior work", "measured", "the reader works the example through", "background the reader brings"]⟩

/-- How the reader weighs each voice. -/
instance argCredence : Credence (AW T) Voice (AFact T) where
  reasons _ _ e l := match e, l with
    | .told .author, (.known _, true) => [(.custom 0, 1)]
    | .told .author, (.promised _, true) => [(.custom 1, 1)]
    | .told .author, (.motivated _, true) => [(.custom 2, 1)]
    | .told .author, (_, false) => [(.custom 3, 1)]
    | .relayed .prior, _ => [(.custom 4, 2)]
    | .told .data, _ => [(.custom 5, 2)]
    | .inferred, _ => [(.custom 6, 1)]
    | _, _ => []
  acceptAt _ _ := 4
  stubborn _ _ := false
  onBetrayal w _ _ := w

instance : Perceive (AW T) (Move T) := Perceive.none

/-- Lore: the reader's background, held as their own knowledge. -/
def start (lore : List T) (excerpt : List Nat) : AW T :=
  { excerpt,
    base := (lore.zip (List.range lore.length)).map fun (t, i) =>
      { b := .atom (.known t), src := .self, rank := 10, stamp := i + 1, up := .hard,
        reasons := [(.custom 7, 6)] } }

def isPending (w : AW T) (t : T) : Bool := w.pending.any (·.t == t)

/-- `t` may be used: lore, defined, promised and still open, or a claim or
concession the reader has heard (whether or not they accept it). -/
def usable (w : AW T) (t : T) : Bool :=
  believes w Voice.reader (.atom (AFact.known t)) || isPending w t ||
    believes w Voice.reader (.atom (AFact.holds t)) || believes w Voice.reader (.neg (AFact.holds t))

/-- The reader holds `k` outright (not just on the authors' word). -/
def accepted (w : AW T) (k : T) : Bool :=
  w.base.any fun h => h.b == .atom (.holds k) && (h.up == .radical || h.up == .hard)

/-- What the reader holds, as literals (not what they only noted). -/
def heldLits (w : AW T) : List (AFact T × Bool) :=
  w.base.filterMap fun h => if h.up == .note then none else litOf h.b

/-- A premise the reader can grant: an accepted claim, or a term they know
(a definition, a stipulation, their background). -/
def granted (w : AW T) (k : T) : Bool :=
  accepted w k || believes w Voice.reader (.atom (AFact.known k))

/-- `k` was put forward: claimed, cited, exemplified, ruled out, or held by
the reader (as a belief, either way, or as background) before. -/
def putForward (w : AW T) (k : T) : Bool :=
  believes w Voice.reader (.atom (AFact.holds k)) || believes w Voice.reader (.neg (AFact.holds k)) ||
    believes w Voice.reader (.atom (AFact.known k)) || (closure (heldLits w)).contains (AFact.holds k, true)

def wasMotivated (w : AW T) (k : T) : Bool := believes w Voice.reader (.atom (AFact.motivated k))

def Move.uses : Move T → List T
  | .claim _ u | .cite _ u | .define _ u | .motivate _ u | .«example» _ u | .contrast _ _ u
  | .promise _ _ u | .contribute _ _ u | .deliver _ u | .concede _ u | .evaluate _ u
  | .deny _ u | .hedge _ _ u => u
  | .infer _ ps u => ps ++ u
  | .heading _ => []

/-- Terms the move needs beyond its `uses`. -/
def Move.needs : Move T → List T
  | .contrast a b _ => [a, b]
  | m => m.uses

def hear (w : AW T) (l : AFact T × Bool) (e : Evid Voice) : AW T := learn w Voice.reader (ofLit l) e

def argOk (w : AW T) (m : Move T) : Bool :=
  m.needs.all (usable w) && match m with
    | .promise _ s _ | .contribute _ s _ | .hedge _ s _ => s == 0 || s > w.sec
    | .deliver t _ => isPending w t
    | .heading n => n ≥ w.sec
    | _ => true

def argStep (w : AW T) : Move T → AW T
  | .claim k _ => hear { w with claims := w.claims ++ [k] } (.holds k, true) (.told .author)
  | .cite k _ => hear w (.holds k, true) (.relayed .prior)
  | .define t _ => hear w (.known t, true) (.told .author)
  | .motivate k _ => hear w (.motivated k, true) (.told .author)
  | .«example» k _ => hear w (.holds k, true) .inferred
  | .contrast _ _ _ => w
  | .promise t s _ => hear { w with pending := w.pending ++ [{ t, sec := s }] } (.promised t, true) (.told .author)
  | .contribute k s u =>
    hear { w with pending := w.pending ++ [{ t := k, sec := s, contribution := true, uses := u }],
                  contributions := w.contributions ++ [(k, u)] } (.promised k, true) (.told .author)
  | .deliver t _ =>
    hear { w with pending := w.pending.filter (·.t != t), delivered := w.delivered ++ [t] }
      (.known t, true) (.told .author)
  | .concede k _ => hear w (.holds k, false) (.told .author)
  | .evaluate k _ =>
    hear { w with pending := w.pending.filter (·.t != k) } (.holds k, true) (.told .data)
  | .deny k _ =>
    hear { w with denials := w.denials ++ [(k, !putForward w k)] } (.holds k, false) (.told .author)
  | .hedge k s _ =>
    hear { w with pending := w.pending ++ [{ t := k, sec := s, hedge := true }] } (.promised k, true) (.told .author)
  | .infer k ps _ =>
    hear { w with claims := w.claims ++ [k] } (.holds k, true)
      (if ps.all (granted w) then .inferred else .told .author)
  | .heading n => { w with sec := n }

variable [Repr T]

/-- A term's name without its namespace. -/
def short (t : T) : String := ((reprStr t).splitOn ".").getLast!

def argWhy (w : AW T) (m : Move T) : String :=
  match m.needs.find? (!usable w ·) with
  | some t => s!"uses {short t} before it is defined or promised"
  | none => match m with
    | .promise _ s _ | .contribute _ s _ => s!"points back to section {s} from section {w.sec}: not a promise"
    | .deliver t _ => s!"delivers {short t}, which was never promised (or was already delivered)"
    | .heading n => s!"section {n} after section {w.sec}"
    | _ => "not allowed"

instance : Domain (AW T) (Move T) where
  ok := argOk
  step := argStep
  why := argWhy

/-- Obligations aimed outside the excerpt (or at no section) are deferred. -/
def deferred (w : AW T) (p : Pending T) : Bool := p.sec == 0 || !w.excerpt.contains p.sec

/-- What can be left unpaid at the end. -/
inductive Gap (T : Type) where
  | unsupported (k : T)
  | unpaid (t : T) (sec : Nat)
  | unmotivated (k : T)
  /-- a hedge inside the excerpt never answered -/
  | unanswered (k : T)
  deriving DecidableEq, Repr

/-- What is left unpaid at the end (structured, so the kernel can decide it). -/
def gapsOf (w : AW T) : List (Gap T) :=
  (w.claims.eraseDups.filterMap fun k =>
    if accepted w k || w.pending.any (fun p => p.t == k && deferred w p) then none
    else some (.unsupported k)) ++
  (w.pending.filterMap fun p =>
    if deferred w p then none else some (if p.hedge then .unanswered p.t else .unpaid p.t p.sec)) ++
  (w.contributions.filterMap fun (k, u) =>
    if (k :: u).any (wasMotivated w) then none else some (.unmotivated k))

def Gap.show : Gap T → String
  | .unsupported k => s!"claim {short k} is unsupported"
  | .unpaid t s => s!"promise of {short t} (section {s}) is never delivered"
  | .unmotivated k => s!"contribution {short k} was never motivated"
  | .unanswered k => s!"hedge on {short k} is never answered"

def gaps (w : AW T) : List String := (gapsOf w).map Gap.show

/-- Promises and contributions left for the rest of the paper. -/
def deferredList (w : AW T) : List (T × Nat) :=
  (w.pending.filter (deferred w)).map fun p => (p.t, p.sec)

/-- Denials of what nobody put forward: antitheses ("not X; Y" with no X). -/
def antitheses (w : AW T) : List T := (w.denials.filter (·.2)).map (·.1)
/-- Denials of what was put forward: contrasts. -/
def contrasts (w : AW T) : List T := (w.denials.filter (!·.2)).map (·.1)
/-- Hedges answered so far, and those still open. -/
def openHedges (w : AW T) : List T := (w.pending.filter (·.hedge)).map (·.t)

/-- Valid move by move, and nothing left unpaid at the end. -/
def Coherent (w : AW T) (ms : List (Move T)) : Prop := Valid w ms ∧ gapsOf (run w ms) = []

instance (w : AW T) (ms : List (Move T)) : Decidable (Coherent w ms) := by
  unfold Coherent; infer_instance

/-- Why the reader holds (or only notes) claim `k`. -/
def support (w : AW T) (k : T) : List String := explain w Voice.reader (AFact.holds k, true)

namespace Toy
inductive Tm | coq | repair | invariants | tool | works
  deriving DecidableEq, Repr

open Move
def w0 : AW Tm := start [.coq] [1, 2]

def good : List (Move Tm) :=
  [ heading 1, define .repair [.coq], motivate .tool [.repair], contribute .tool 2 [.repair],
    claim .works [.tool], promise .invariants 3 [], heading 2, deliver .tool [.invariants],
    «example» .works [.tool] ]

/-- "not X; Y" with no X before is an antithesis; a hedge is answered by evaluation;
a claim inferred from accepted claims is supported. -/
def moreMoves : List (Move Tm) :=
  [ heading 1, define .tool [], deny .works [.tool], claim .repair [.tool], «example» .repair [],
    infer .invariants [.repair] [], hedge .tool 0 [], evaluate .tool [], deny .repair [] ]
theorem more_antitheses : antitheses (run w0 moreMoves) = [.works] := by decide +kernel
theorem more_contrasts : contrasts (run w0 moreMoves) = [.repair] := by decide +kernel
theorem more_gaps : gapsOf (run w0 moreMoves) = [] := by decide +kernel

theorem good_coherent : Coherent w0 good := by decide +kernel
/-- Using a term before it is defined or promised. -/
theorem early_use : ¬ Valid w0 ([heading 1, claim .works [.tool]] : List (Move Tm)) := by decide +kernel
/-- The authors' word alone does not support a claim. -/
theorem bare_claim :
    gapsOf (run w0 ([heading 1, define .tool [], claim .works [.tool]] : List (Move Tm))) = [.unsupported .works] := by
  decide +kernel
end Toy

end LangLib.World.Argument
