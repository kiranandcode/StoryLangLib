# Jev in langlib

Jev (TypeSafe System One, `eval/jev.py`) answers typed questions about a text
with calibrated probabilities: `noul` (0 to 1), `choice` (pick a label), `score`
(a rubric). Key: `JEV_API_KEY` in ~/.zshrc.

Where it plugs in:

1. Reference spot-check (`eval/jev_coref.py`). The token check proves an
   encoding has the source's words; it cannot see a pronoun pointing at the
   wrong entity. Jev picks each pronoun's referent from the document's own
   entities, with the pronoun marked; disagreement flags a ref to re-examine.
2. Graded plausibility (story layer 3). The defeasible theory gives a verdict
   only for actions its rules cover. Jev scores the rest ("how believable is
   this action for this character here"), and a disagreement between a Lean
   verdict and Jev's score signals a missing rule or defeater.
3. Extraction round trip. After prose is generated from a planned event, a
   `noul` per event fact ("the text states that Kiran hands Mara the key")
   checks the prose realises the event and nothing contradicts it.

First probe, timid Kiran (Lean verdict vs Jev in_character / motivated /
plausibility score 0-2):

| scene | Lean | in character | motivated | score |
|---|---|---|---|---|
| market, overcharged | implausible | 0.28 | 0.31 | 0.57 |
| gate, Mara grabbed | plausible | 0.73 | 0.94 | 1.5 |
| tavern, drunk | unexplained | 0.30 | 0.69 | 1.01 |
