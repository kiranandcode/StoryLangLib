# Academic style as decidable rules

This note formalises Kiran's principles for writing papers
(`~/Documents/code/prompts/writing-style.md`) and the LLM-isms that show in a
sentence's structure (`llmisms.md`) as rules over checked langlib trees. It
then measures two papers against them: Kiran's own PLDI 2023 paper, *Mostly
Automated Proof Repair for Verified Libraries* (Sisyphus), and Jung, Jourdan,
Krebbers and Dreyer's POPL 2018 paper, *RustBelt: Securing the Foundations of
the Rust Programming Language*, chosen from the PLDB corpus because it is
widely held up as a model of PL writing. Below, "Dreyer" is shorthand for its
four authors.

The code is `LangLib/Style/Academic.lean` (the rules) and
`LangLib/World/Argument.lean` (the argument as a story, below). The papers'
texts and annotations live in `stories/private-papers/{sisyphus,rustbelt}/`,
which git ignores; only numbers and quotes of at most a sentence appear here.

## The texts

For each paper we took the abstract, the introduction and one technical
section: Sisyphus §2 up to the first paragraph of §2.1.1 (the to_array
example, 31 paragraphs in all), and RustBelt §2.2, Mutable References (33
paragraphs). Displayed code was dropped; inline maths was written in ASCII
(`p'`, `phi = {P} {Q}`). Eight annotator subagents encoded every paragraph in
the `eval/prompt.md` format against a shared per-paper glossary of entity ids,
so that "proof repair" in the abstract and in §1 are one entity. All 64
annotations are accepted by `langlib check` (tokens match, every pronoun
resolves).

## The rules

`asentOf` reads each sentence tree once into a record: the entities it
mentions with the word index of each first mention, the entity of the main
clause's subject (`nsubj`, followed down the chain of heads) and where it
starts, whether the sentence is a run-in heading (a `FRAG` root), and counts
of em-dashes, colon setups and antitheses. Every feature below is structural
recursion over the list of records, so `langlib academic <dir> --lean <name>`
prints records that a theorem file restates and the kernel judges.

| rule | definition over the records | Kiran's style requires |
|:--|:--|:--|
| old to new, subjects | a sentence's subject is the authors, the reader, or an entity already mentioned | ≥ 3/4 of tracked subjects |
| old to new, new late | an entity a sentence introduces starts after its subject | ≥ 2/3 of new entities |
| first sentence summarises | in a paragraph of two or more sentences, the first non-heading sentence mentions an entity no other entity outnumbers (counting sentences) | ≥ 2/3 of such paragraphs |
| just in time | an entity used again is used again within three sentences of its introduction | ≥ 1/2 of reused entities |
| callbacks | an entity mentioned again after at least six sentences, in a later paragraph (counted once per entity) | ≥ 1 per 4 paragraphs |
| question, then answer | a sentence ending in "?" or using "wonder" or "question" (not "in question") is answered by the next sentence or the first sentence of the next paragraph: one that is not a question and shares an entity with it | none unanswered |

The LLM-ism rules (`llmismFree`) allow none of each.

| LLM-ism | how it shows in the tree |
|:--|:--|
| em-dashes | a `—` or `--` leaf |
| colons as setup | a `:` followed by more words, not by a list marker (`(`, `•`, a number), not part of `::`, not in a heading |
| "not X but Y" | a negation (`not`, `never`, `no`, `-n't`; not "not only") followed in the same sentence by `but`, `rather`, `instead` or `;` |
| rhetorical questions | a "?" sentence the question rule leaves unanswered |

The thresholds are judgement calls, like the Pratchett style's. They say
where a rule bites, not what Kiran's writing measures; the measurements
follow.

## Measurements

Both `Style.lean` files prove each paper's feature record, and every style's
list of failing rules, by `decide +kernel`.

| | Sisyphus (Kiran) | RustBelt (Dreyer et al.) |
|:--|--:|--:|
| sentences / words | 75 / 2255 | 115 / 3323 |
| words per sentence | 30.1 | 28.9 |
| sentences of ≥ 25 words | 63% | 58% |
| parentheticals per sentence | 0.37 | 0.53 |
| sentences opening with a connective | 13% (10 kinds) | 27% (22 kinds) |
| subjects given | 45/50 (90%) | 60/75 (80%) |
| new entities after the subject | 47/57 (82%) | 60/78 (77%) |
| first sentence summarises | 16/18 (89%) | 26/29 (90%) |
| reused just in time | 29/54 (54%) | 35/56 (63%) |
| entities called back | 34 | 36 |
| questions set up / answered | 1 / 1 | 3 / 3 |
| literal "?" questions | 0 | 1 |
| em-dashes (sentences with one) | 15 (11) | 17 (11) |
| colon setups | 3 | 7 |
| "not X but Y" | 0 | 3 |
| Kiran's principles | holds | holds |
| LLM-ism free | fails: em-dashes, colon setups | fails: em-dashes, colon setups, not-X-but-Y |
| Pratchett (Core) | fails: footnotes, generics, similes | fails: footnotes, generics, similes |
| roof (Core) | fails: parentheticals, interiority, Concepts, dialogue | same four |

Some of the sentences behind the numbers:

- Sisyphus's one question is a setup the next sentence answers: "the reader
  might wonder if it might be simpler to just prove the new version of a
  library function correct from scratch", then "The reason why this is not so
  straightforward is because of the main bane of fully-automated verification".
- RustBelt's literal question is answered a paragraph later, which is why the
  rule looks at the next paragraph's first sentence: "The question remains:
  How can we verify that Rust's extensible approach makes any sense?"
- A colon setup in each: "Our approach is mostly-automated: the verification
  conditions for the invariants are discharged using domain-specific
  automation." and "At the heart of the Rust type system is an idea that has
  emerged in recent years as a unifying concept connecting both academic and
  mainstream language design: ownership."
- RustBelt's antitheses include "The idea is that v is not moved to push, but
  instead borrowed", a definitional contrast rather than a flourish.
- Paragraph openers with new subjects in RustBelt: "Systems programming
  languages like C and C++ give programmers low-level control over resource
  management at the expense of safety, whereas most other modern languages
  give programmers safe, high-level abstractions at the expense of control."
  and "At least, that is the hope."

## The argument

`LangLib/World/Argument.lean` reads a paper as a story whose plot is its
argument. The characters are four voices (the reader, the authors, the prior
work they cite, the data their evaluation measured); the lore is the
background the reader brings; the events are the moves claim, cite, define,
motivate, example, contrast, promise, deliver, contribute, concede and
evaluate. Each move adds to the reader's evidence base through `Mind.learn`,
with its evidential source, and `argCredence` weighs the voices. The authors'
bare word on a claim (strength 3) falls short of acceptance (4); a citation,
a worked example or a measurement lifts it to an outright belief. Validity is
no use of a term before it is lore, defined, promised or claimed, forward
promises and paid-off deliveries. `gapsOf` lists what the excerpt leaves
unpaid: claims on the authors' word alone, promises inside the excerpt never
delivered, contributions never motivated.

I read each paragraph into moves myself (`argument.py`, written out as
`NN.argument.json` and `Argument.lean` beside each paper, rather than into
`story.json`, since the Studio's world has no argument module). Both
arguments are valid move by move, by `decide +kernel`.

| | Sisyphus | RustBelt |
|:--|--:|--:|
| moves | 96 | 129 |
| claims on the authors' word | 4 | 10 |
| promises and contributions deferred past the excerpt | 11 (§3, §4, §5, §6) | 8 (§3 to §7, §9) |
| contributions never motivated | 0 | 0 |

Sisyphus's unsupported claims are the abstract's cost claim, the
"to the best of our knowledge" gap in implementation changes, the size of the
invariant search space, and that dynamic analysis addresses both challenges.
RustBelt's ten are the reasoned steps of its introduction (C++'s type system
is "too weak", designs are "too restrictive or too expressive", unsafe code
"cannot simply be swept aside", the semantic approach is more powerful). Kiran
backs her introduction with citations and one worked example (the
Array.iter refactoring); RustBelt makes more claims (35 against 22) and
argues more of them in prose.

Both papers use their central formalism before defining it, and rely on the
reader's background to carry it. Each `lore_needed_*` theorem proves that
removing a term from the lore makes the argument invalid: Separation Logic is
used in Sisyphus's paragraph 14 and defined in §2.1.1, and ownership is used in
RustBelt's abstract and defined in §1.1.

## Where Kiran and Dreyer differ

Kiran's sentences start from what the reader holds more often (90% of
subjects given against 80%). Six of RustBelt's fifteen new subjects open a
paragraph: Dreyer often starts a paragraph by placing a new frame in front of
the reader ("Systems programming languages like C and C++ ...", "At the heart
of the Rust type system is an idea ...") and then ties it back, where Kiran's
paragraphs start from the last paragraph's entity.

Dreyer steers with connectives and stance (27% of sentences open with one, in
22 kinds, led by "However", "Unfortunately" and "Moreover", with "Luckily" and "Nevertheless"); Kiran steers
with structure (run-in headings such as "Problem Statement.", enumerated
classes (1) to (3), named challenges C1 and C2) and opens only 13% of
sentences with a connective.

Dreyer asks more questions and answers all of them, once across a paragraph
break; Kiran sets up one, in the third person ("the reader might wonder"), and
answers it in the next sentence.

Kiran introduces technical terms earlier than she uses them: the abstract
names dynamic program alignment and proof-driven testing seventeen
paragraphs before §1 explains them. That is consistent with its lower
just-in-time score (54% against RustBelt's 63%), though the score counts every
entity, not only these.

On the LLM-isms both papers are em-dash heavy (15 and 17). Kiran's 2023
paper breaks two of her own current rules (em-dashes, colon setups) and never
uses "not X but Y"; RustBelt uses all three.

Against the formal styles from `Style/Core.lean`, both papers fail the
Pratchett and roof styles on the same rules, which is the right answer: those
styles describe fiction (footnotes, similes, interiority, dialogue), and the
academic rules are what separates the two papers.

## What the formalism misses

- **Composite reference.** "the combined power of deductive machine-assisted
  reasoning and proof automation" (Sisyphus §1) sums up the previous
  paragraph's (a) and (b), exactly the old-to-new bridge Kiran asks for. Entity
  ids are atomic, so the subject counts as new.
- **Summary by a more general term.** "To address C1, we use a trace-based
  program alignment technique." is a topic sentence, but the rest of its
  paragraph talks about programs, inputs and values, so the most-mentioned
  entity is not one it names. Paragraphs 19 and 20 of Sisyphus are flagged for
  this reason.
- **Entities split by number.** The checker's pronoun agreement made
  annotators split "libraries" from a singular "library function" (and
  "shared references" from "a shared reference"), which adds false new subjects
  and hides callbacks.
- **Whether a callback is a motif.** The rule counts recurrence after a gap.
  It cannot tell Kiran's deliberate return to "knowledge about old invariants"
  from a term that simply keeps coming up.
- **Whether a colon or dash is dramatic.** "is a simple one: If ownership of
  an object ... is shared" defines; "Our approach is mostly-automated: ..." is
  closer to a flourish. Both count. The same goes for em-dashes that introduce
  a definition ("the problem known as proof repair").
- **Antithesis against contrast.** "not moved to push, but instead borrowed" is
  the paper's point, not a rhetorical pivot.
- **Questions without question words.** "At least, that is the hope." turns
  the reader's expectation without a "?" or "wonder"; "let us begin by
  exploring what makes Rust's type system so unusual" sets up a question the
  rule cannot see.
- **Need.** "Just in time" is approximated by re-mention within three
  sentences. Whether the information was needed for what follows is a fact
  about the argument, not the trees.
- **Punch, rhythm, register.** Sentence length and depth are measured, but the
  punchy opening sentence, the playful rhythm and the conversational word
  choice inside formal syntax are not formalised.
- **The argument's support is coarse.** A reasoned claim ("because ...") counts
  as the authors' word, absence claims ("to the best of our knowledge") cannot
  be cited, truth is not judged, and the verdict depends on the lore I chose
  for the reader (the `lore_needed_*` theorems show which choices carry
  weight).
- **Annotation detail.** Core's generics need `Tense` features the annotators
  did not add (both papers score 0), and its "like" similes fire on
  exemplification ("languages like C and C++", nine times in RustBelt).

## Reproducing

```
langlib check   stories/private-papers/<p>/paragraphs/NN.txt NN.json   # each paragraph
langlib academic stories/private-papers/<p>                             # features, flags, verdicts
python3 stories/private-papers/tools/style_prove.py    stories/private-papers/<p> <Name>   # Style.lean, proved
python3 stories/private-papers/tools/argument_prove.py stories/private-papers/<p> <Name>   # Argument.lean, proved
python3 stories/private-papers/tools/sent.py stories/private-papers/<p> 12:1             # a flagged sentence
```
