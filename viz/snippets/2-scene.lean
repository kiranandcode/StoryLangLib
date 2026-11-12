-- LangLib/Story/Scene.lean
inductive Fact (C P O)  | at_ (c : C) (p : P) | objAt (o : O) (p : P) | holds (c : C) (o : O)

inductive Event (C P O)
  | move (c : C) (p : P) | take (c : C) (o : O) | hide (c : C) (o : O)
  | grab (c v : C) | shout (c d : C) | tell (c d : C) (f : Fact C P O)
  | gag (c v : C) | drink (c : C)

structure Persona (C) where
  traits : List Trait          -- [.timid]
  values : List Value          -- most preferred first: [.loyalty, .safety, .pride]
  allies : List C

structure State (C P O) where
  persona : C → Persona C
  loc : C → P;  holder : O → Option C;  objLoc : O → P
  gagged : C → Bool;  drunk : C → Bool;  threats : List (C × C)
  knows : C → List (Fact C P O)          -- only from witnessing or being told

def pre (s : State C P O) : Event C P O → Bool       -- hard constraints
  | .take c o    => s.holder o == none && s.objLoc o == s.loc c
  | .tell c d f  => s.loc c == s.loc d && !s.gagged c && (s.knows c).contains f
  | .shout c d   => s.loc c == s.loc d && !s.gagged c
  | ...
def State.step : State C P O → Event C P O → State C P O   -- effects + witnessing

inductive InCharacter (s : State C P O) : Event C P O → Prop
  | shout {c d} : NotDef (shoutTheory s c d) (neg (.shouts c d)) → InCharacter s (.shout c d)
  | other {e}   : (∀ c d, e ≠ .shout c d) → InCharacter s e

inductive Valid : State C P O → List (Event C P O) → Prop
  | nil  : Valid s []
  | cons : pre s e = true → InCharacter s e → Valid (s.step e) es → Valid s (e :: es)

theorem validB_sound (s) (es) : validB s es = true → Valid s es

-- LangLib/Story/GateScene.lean
theorem story_valid        : Valid start story        := validB_sound _ _ (by decide +kernel)
theorem tipsy_valid        : Valid start tipsy
theorem leak_invalid       : ¬ Valid start leak        -- Kiran tells what she never learned
theorem unprovoked_invalid : ¬ Valid start unprovoked  -- timidity is Def, so not InCharacter
theorem gagged_invalid     : ¬ Valid start gagged
