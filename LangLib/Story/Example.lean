import LangLib.Story.Defeasible

/-!
# Example: a timid character shouting

Kiran is timid and ranks loyalty above safety above pride. Three scenes:

1. at the market, nothing provokes her: shouting is out of character;
2. at the gate, a guard grabs her friend Mara: loyalty beats safety, so she shouts;
3. later she is gagged: shouting is impossible whatever her values.
-/

namespace LangLib.Story.Example

def kiran : Persona := { name := "kiran", values := ["loyalty", "safety", "pride"] }

/-- Rule schemas instantiated for an agent `c` and a target `x`. -/
def rulesFor (c x : String) (allies : List String) : List Rule :=
  [ { name := "timid-stays-quiet", kind := .defeasible, agent := c, value := "safety",
      body := [lit "trait" [c, "timid"]], head := nlit "shouts" [c, x] },
    { name := "drink-loosens", kind := .defeater,
      body := [lit "drunk" [c]], head := lit "shouts" [c, x] },
    { name := "gagged", kind := .strict,
      body := [lit "gagged" [c]], head := nlit "shouts" [c, x] } ] ++
  allies.map fun y =>
    { name := s!"protect-{y}", kind := .defeasible, agent := c, value := "loyalty",
      body := [lit "threatens" [x, y], lit "ally" [c, y], lit "present" [c]],
      head := lit "shouts" [c, x] }

def scene (facts : List Lit) (target : String) : Theory :=
  { facts := [lit "trait" ["kiran", "timid"], lit "ally" ["kiran", "mara"]] ++ facts,
    rules := rulesFor "kiran" target ["mara"],
    personas := [kiran] }

def market := scene [lit "present" ["kiran"]] "merchant"
def gate := scene [lit "present" ["kiran"], lit "threatens" ["guard", "mara"]] "guard"
def gagged := scene [lit "present" ["kiran"], lit "threatens" ["guard", "mara"],
                     lit "gagged" ["kiran"]] "guard"
def tavern := scene [lit "present" ["kiran"], lit "drunk" ["kiran"]] "merchant"

#guard (market.verdict (lit "shouts" ["kiran", "merchant"])).tag == "implausible"
#guard (gate.verdict (lit "shouts" ["kiran", "guard"])).tag == "plausible"
#guard (gagged.verdict (lit "shouts" ["kiran", "guard"])).tag == "impossible"
-- drunk only blocks the timid default; nothing motivates the shout
#guard (tavern.verdict (lit "shouts" ["kiran", "merchant"])).tag == "unexplained"

/--
info: shouts(kiran, merchant) is out of character (timid-stays-quiet [safety]). Revise it, or establish setup first: protect-mara [loyalty] needs threatens(merchant, mara)
-/
#guard_msgs in
#eval IO.println ((market.verdict (lit "shouts" ["kiran", "merchant"])).explain
  (lit "shouts" ["kiran", "merchant"]))

/--
info: shouts(kiran, guard) is plausible by protect-mara [loyalty], overriding timid-stays-quiet [safety]
-/
#guard_msgs in
#eval IO.println ((gate.verdict (lit "shouts" ["kiran", "guard"])).explain
  (lit "shouts" ["kiran", "guard"]))

end LangLib.Story.Example
