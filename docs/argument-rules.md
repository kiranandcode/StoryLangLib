# An argument's inferences as informal rules

`langlib argument` (World/Argument) treats an inference as a claim with
reasons, supported when every reason is granted. It does not ask whether
the step from the reasons to the claim is any good. `LangLib/World/Rules.lean`
adds that question. Each `infer` move can carry a `rule`:

- **kind**: strict (deductive or definitional) or defeasible;
- **scheme**, after Walton, Reed and Macagno, *Argumentation Schemes* (2008):
  example to generalisation, practical reasoning, abduction (best
  explanation), track record → capability, expert opinion, cause to effect,
  analogy, requirement matches capability, counterexample;
- **premises**, each a verbatim quote, tagged with what it rests on when no
  other rule concludes it: fact, example, citation, authors' word, hedge,
  promise;
- the scheme's **critical questions** (`Scheme.cqs`), each marked answered by
  the text, open, or pressed (an attack point a sceptical reader would use);
- **attacks**, ASPIC+ style (Prakken 2010; Modgil and Prakken 2014): a
  rebutter attacks the conclusion, an undercutter the inference (Spectre
  undercuts "the proof is correct, so the system is trustworthy"), an
  underminer a premise.

Positions the text argues against go in `argument.json` as `opponents`, as
rules with the same fields. The root of the tree is `argument.json`'s `root`.

## Typed slots

Each scheme says which slots its premises may fill and which it requires
(`Scheme.spec`): practical reasoning takes a goal, a problem, a means, why it
is feasible and who should act, and requires the goal and the means;
requirement matches capability requires a need and a provision; abduction
requires an observation and a rival explanation; analogy a source case, a
target case and the respect in which they are alike. A premise's `role` in the
rule JSON names its slot.

- **Shaped** (a fault of the *reading*): every premise fills a slot its scheme
  allows, no rule has more than six premises (group them into sub-rules), and
  every scheme has been read. A first reading of a pitch made its conclusion
  rest on twelve parallel reasons with no goal; it was readable rule by rule
  and had no argument. Shaped rejects that reading.
- **Enthymemes** (a finding about the *text*): required slots no premise
  fills. An abduction that never names a rival explanation, a practical
  argument with no stated goal, an analogy that never says how the cases are
  alike. The text may be right to leave them implicit; the view shows each as
  an "unstated" row so the reader can decide.

## Reading a text into rules: the protocol

1. **Top down.** Write the root rule first, from the thesis: for a pitch or
   proposal, practical reasoning (goal, problem, means, feasible, who). Then
   expand each premise into the rules from the text that support it. Reading
   bottom up (a rule per paragraph, then a conclusion over all of them) is how
   the flat reading above happened.
2. **Type every premise.** Give each premise its slot. If no slot fits, the
   scheme is wrong.
3. **Check.** `langlib rules` must say `ok` and `shaped`; `rules_lean.py`
   proves it.
4. **Review by reading the rules.** A fresh agent that did not write the
   reading gets the text and the plain-words view, rule by rule, with each
   scheme's critical questions, and answers for each rule: does each premise
   play its role, does the conclusion follow by this scheme, is the gloss
   faithful to the quote. This is the default review, for every rule.
5. **One blind check, at the top.** Another fresh agent gets only the text and
   writes the argument's top level in five lines (goal, problem, means,
   feasible, who, or whatever the text's own shape is). Compare it with the
   root rule. A reviewer shown a structure checks what is there; only a blind
   reading notices structure that is missing. Disagreements go to Kiran.

## What is decided

Everything below is a Lean function over the rules, decidable, so a
document's results can be restated as theorems and proved by
`decide +kernel` (`tools/house/rules_lean.py <dir> <Ns>` writes that file):

| | function | what it means |
|:--|:--|:--|
| well formed | `RulesOk` | rebutters and undercutters reach only defeasible rules (restricted rebut); an underminer names a non-fact leaf premise; every pressed question is open |
| grounded labelling | `labels` | Dung's grounded extension (Caminada's labelling) over the text's own attacks; an attack on a rule reaches every rule built on its conclusion |
| under the sceptic | `scepticLabels` | the same, with one unanswered attacker per pressed critical question |
| the authors' word alone | `bareRules`, `bareLeaves` | rules whose leaves are only the authors' word, hedges and promises; premises nothing supports |
| shape | `Shaped`, `faults` | every premise fills a slot its scheme allows; at most six premises; every scheme read |
| unstated premises | `enthymemeRules` | required slots no premise fills |
| thin support | `thinRules` | a generalisation from at most two examples or citations, a defeasible rule resting on a promise, or one whose premises all rest on the authors' word |

The two labellings answer different questions. Under the text's own attacks,
a rule is out only when an argument the text itself contains defeats it, so
most of a pitch's own rules come out in and the positions it argues against
come out out. Two rules that rebut each other are both undecided. Under the
sceptic, every question the reading marks as pressed defeats its rule and
everything built on it. What survives is what the text has closed: strict
rules, and defeasible ones whose questions it answers.

## The view

`langlib rules <dir>` prints the rules as JSON. The Studio (Rules tab, next
to Argument) and the deslop UI (Rules tab) draw them with one shared
component, `studio/web/src/Rules.tsx`, as natural-deduction rules: tagged
quotes above the line, the conclusion below, the scheme and kind at the
right, a dashed line for a defeasible rule. Attacks run between rules and
each rule carries its label. Hovering a quote highlights it in the text;
clicking a rule shows its critical questions. `tools/house/rules_md.py <dir>`
exports the same tree as markdown.

## Reading conventions

The reading is a model's judgement, like an annotation. Beyond the protocol:

- A rule's conclusion quote and premise quotes must be verbatim. The
  builder should check every quote against its paragraph.
- Tag a premise by what the text gives for it, not by whether it is true:
  a self-description the reader cannot check ("world-leading expertise") is
  the authors' word, and a named public artefact ("Pyro") is a fact.
- Mark a critical question answered only when the text answers it, and
  say where in the note.
- Press a question only when the text leaves it open *and* the answer
  matters to the conclusion. Pressing everything makes every defeasible rule
  out under the sceptic and says nothing.
- An opponent position assembled from the text's own premises (a pitch
  citing industrial labs' results while arguing industry cannot do the work)
  is a legitimate attacker. Say in its note that it was assembled.
