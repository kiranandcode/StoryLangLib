# Academic style as decidable rules

This note formalises Kiran's principles for writing papers
(`~/Documents/code/prompts/writing-style.md`) and the LLM-isms that show in a
sentence's structure (`llmisms.md`) as rules over checked langlib trees. It
then measures two papers against them: Kiran's own PLDI 2023 paper, *Mostly
Automated Proof Repair for Verified Libraries* (Sisyphus), and Jung, Jourdan,
Krebbers and Dreyer's POPL 2018 paper, *RustBelt: Securing the Foundations of
the Rust Programming Language*, chosen from the PLDB corpus because it is
widely held up as a model of PL writing. Below, "Dreyer" is shorthand for its
four authors. Rhythm and register are also compared with the two versions of
the roof story.

The code is `LangLib/Style/Academic.lean` (the rules),
`LangLib/World/Argument.lean` (the argument as a story) and two small additive
changes to `LangLib/Style/Core.lean`. The papers' texts and annotations live
in `stories/private-papers/{sisyphus,rustbelt}/`, which git ignores; only
numbers and quotes of at most a sentence appear here.

## The texts

For each paper we took the abstract, the introduction and one technical
section: Sisyphus §2 up to the first paragraph of §2.1.1 (the to_array
example, 31 paragraphs), and RustBelt §2.2, Mutable References (33
paragraphs). Displayed code was dropped; inline maths was written in ASCII
(`p'`, `phi = {P} {Q}`). Subagents encoded every paragraph in the
`eval/prompt.md` format against a per-paper glossary of entity ids, then
revised every paragraph to carry the marks the rules below read. All 64
annotations are accepted by `langlib check`.

## What the rules read

Nothing is read off raw strings. Where the trees did not carry what a rule
needs, the information is declared and checked.

| mark | where | checked by |
|:--|:--|:--|
| `generic: true` on an entity: a kind, not an individual | the annotation | `langlib check`: a kind (or a group) takes "it" or "they" |
| `of: [ids or "para:N"]` on an entity: a composite ("such changes", "this problem") | the annotation | `langlib academic`: every part is a known entity |
| `VerbForm` on every verb, `Tense` on every finite one | the annotation | the `annotated` style |
| what follows a colon or dash is its next sibling, with a role (`appos`, an argument or list role, or a clause role) | the annotation | the `annotated` style: none unclassified |
| a register (formal, informal, technical, neutral) for every content word | `lexicon.json` | the `annotated` style: none untagged |
| a discourse relation for closed-class forms (contrast, concession, cause, callback, neg, focus, question, quote) | `lexicon.json` | |
| is-a and part-of pairs over entities, and section starts | `discourse.json` | `langlib academic`: every id is a known entity |
| what each paragraph promises | `NN.argument.json` | the argument world |

The lexicons were tagged by subagents (1305 content keys across the four
texts) and the discourse relations by hand. The is-a lore and the argument
readings are mine.

## The rules

`asentOf` reads each sentence tree once into a record; every feature is
structural recursion over the records and the declared lore, so
`langlib academic <dir> --lean <name>` prints records that a theorem file
restates and the kernel judges.

| rule | definition | Kiran's style requires |
|:--|:--|:--|
| old to new, subjects | a sentence's subject is the authors, the reader, an entity already mentioned, or a composite whose parts are | ≥ 3/4 of tracked subjects |
| old to new, new late | an entity a sentence introduces starts after its subject | ≥ 2/3 of new entities |
| first sentence summarises | the first sentence names an entity that covers (is, or subsumes through the is-a lore) at least as many of the paragraph's sentences as its most-mentioned entity | ≥ 2/3 of paragraphs of two or more sentences |
| just in time | an introduced entity is used again within three sentences, or was promised; gaps are also bucketed | ≥ 1/2 of reused entities |
| motifs | an entity leaves and comes back (≥ 6 sentences, a later paragraph), and both the departure and the return are at marked points: a section's first sentence, the first or last sentence of a paragraph of three or more, a sentence with a contrast, concession or callback connective, inside quotation marks | ≥ 1 per 8 paragraphs |
| question, then answer | a sentence ending in "?" or with a question word (not inside a PP: "the program in question") is answered by the next sentence or the first sentence of the next paragraph | none unanswered |

The LLM-ism rules (`llmismFree`):

| LLM-ism | definition |
|:--|:--|
| dramatic dash or colon | the constituent after it is a clause with its own subject (`nsubj`, `csubj` or expletive), after a complete clause. Otherwise the mark is *defining* (it elaborates or names something on the left, introduces a list or a display, or labels a run-in heading) and is allowed |
| "not X but Y" | the tree gives a candidate (a `neg` form, not before `focus` "only", followed by a contrast or concession connective); the argument world decides: an *antithesis* if the denied proposition was never claimed, cited, ruled out or held by the reader, a *contrast* if it was. Only antitheses count |
| rhetorical question | a "?" the question rule leaves unanswered |

`noDashes` keeps Kiran's literal rule (no em-dashes at all), and `annotated`
requires the marks above. The thresholds are judgement calls.

Rhythm and register are measured, not judged: per-paragraph sentence-length
jumps, short-after-long *punches* (≤ 12 words right after ≥ 25), runs of three
or more long sentences, the overall variance, and the share of content words
in each register.

## The argument

`LangLib/World/Argument.lean` reads a paper as a story whose plot is its
argument. The characters are four voices (the reader, the authors, the prior
work they cite, the data their evaluation measured), the lore is the
reader's background, and the events are rhetorical moves. Each move adds to
the reader's evidence base through `Mind.learn`, with its evidential source.
The authors' bare word on a claim (strength 3) falls short of acceptance (4);
a citation, a worked example or a measurement lifts it to an outright belief.

Three moves were added for this round. `deny k` is an antithesis when nobody
put `k` forward, and a contrast when someone did. `hedge k` leaves the reader
an open question about `k`, answered by a later `deliver` or `evaluate`
(otherwise a gap, or deferred past the excerpt). `infer k premises` makes a
claim with stated reasons ("because", "so", "therefore"); the reader accepts
it outright when every premise is already accepted, and otherwise it rests on
the authors' word.

Validity is still no use of a term before it is lore, defined, promised or
claimed, plus forward promises and paid-off deliveries. Both readings are
valid by `decide +kernel`. Each paper's `Paper.lean` proves the exact gaps,
antitheses, contrasts and deferred obligations.

| | Sisyphus | RustBelt |
|:--|--:|--:|
| moves | 102 | 151 |
| claims on the authors' word | 9 | 13 |
| reasoned claims (`infer`) / supported by granted reasons | 5 / 3 | 15 / 10 |
| hedges / answered in the excerpt | 2 / 1 | 6 / 5 |
| antitheses / contrasts | 0 / 0 | 1 / 4 |
| obligations deferred past the excerpt | 12 | 8 |

Reading the reasons honestly cost Sisyphus two supports. In the first reading
I had filed "verified software libraries are a sweet spot for proof repair"
and "we heuristically infer the mapping" as supported by examples. They are
reasoned, and their premises ("library functions are expected to preserve
their API", "p' should still compute the same or similar concrete values")
rest on the authors' word, so the conclusions do too. RustBelt's "the problem
cannot easily be contained" is now supported: its reason, that libraries use
unsafe code widely, was backed by an example two paragraphs earlier.

Both papers still use their central formalism before defining it and rely on
the reader's background to cover it (Separation Logic in Sisyphus, ownership
in RustBelt); the `lore_needed_*` theorems prove it.

## Measurements

Every number in this table is proved by `decide +kernel`: for the papers in
their private `Paper.lean`, for the stories in
`LangLib/Style/AcademicTheorems.lean`.

| | Sisyphus | RustBelt |
|:--|--:|--:|
| sentences / words | 75 / 2255 | 115 / 3323 |
| subjects given (of which bridged / announced) | 49/50 (98%) (1 / 1) | 78/81 (96%) (9 / 0) |
| new entities after the subject | 18/21 (86%) | 15/21 (71%) |
| first sentence summarises | 18/18 | 28/29 |
| just in time (incl. promised) | 31/54 (57%) | 35/55 (64%) |
| introductions the argument uses in their paragraph or the next / never | 35 / 39 | 39 / 67 |
| callbacks / deliberate (demonstrative, quoted or recalled) / motifs | 34 / 1 / 6 | 36 / 8 / 12 |
| questions set up / answered | 1 / 1 | 3 / 3 |
| em-dashes: defining / dramatic | 11 / 0 | 11 / 0 |
| colons: defining / dramatic | 6 / 1 | 12 / 0 |
| not-X-but-Y candidates / antitheses | 0 / 0 | 4 / 1 |
| fronted subjects / short paragraph closers | 21 / 0 | 37 / 5 |
| Kiran's principles | holds | holds |
| LLM-ism free | fails: dramatic colons | fails: not-X-but-Y |
| annotated, grounded (every hedge, denial and stated reason read, every reading on a marked sentence) | hold | hold |
| no em-dashes (literal) | fails | fails |
| Pratchett (Core) | fails: footnotes, similes, Concepts | same |
| roof (Core) | fails: parentheticals, generalisations, interiority, Concepts, dialogue | same |

### Rhythm and register across four texts

| | Sisyphus | RustBelt | roof | roof-pratchett (01–06) |
|:--|--:|--:|--:|--:|
| words per sentence (mean, sd) | 32.7, 13.7 | 29.5, 15.1 | 13.3, 8.6 | 15.8, 9.9 |
| coefficient of variation | 0.42 | 0.51 | 0.65 | 0.63 |
| mean jump between neighbours | 14.1 | 15.6 | 9.3 | 11.9 |
| punches (short after long) | 0 | 4 | 0 | 3 |
| runs of ≥ 3 long sentences (longest) | 4 (4) | 9 (5) | 0 (2) | 0 (2) |
| register: technical / formal / informal / neutral (% of content words) | 44.9 / 4.3 / 1.1 / 49.7 | 42.8 / 5.2 / 1.2 / 50.8 | 1.5 / 0.3 / 3.4 / 94.8 | 0.8 / 0.3 / 2.4 / 96.6 |

The papers write long and steady: about a third of each paper's content
words are technical, and runs of long sentences are common. The stories write
short and varied, in a neutral register with a little informal colour.
Dreyer's lengths vary more than Kiran's (0.51 against 0.42), and he lands
four short sentences after long ones, each naming or settling what the long
one built ("The logic we chose, Iris, is ideally suited to this purpose.";
"Mutable references are always unique pointers."). Sisyphus has none. Its
sentence-length rhythm is even, and its "punchy" openings are punchy in
content, not in length: the opening sentence of the introduction runs to 30
words. Between the two roofs the clearest difference on this measure is the
punches (3 in six paragraphs of Pratchett's, none in nine of the plain one).

Some of the sentences behind the numbers:

- Sisyphus's dramatic colons: "Our approach is mostly-automated: the
  verification conditions for the invariants are discharged using
  domain-specific automation." and "... a sweet spot for proof repair: it is
  not uncommon for library functions to undergo changes in their bodies ...".
  Its dashes all define ("in sync—the problem known as proof repair").
- RustBelt's antitheses deny what nobody proposed: "we will therefore not
  present all these challenges and their solutions in full technical detail
  ... Rather, we aim to highlight the following key challenges", and "the
  problem cannot easily be contained by blessing a fixed set of standard
  libraries". Its contrasts deny what the reader holds: "The idea is that v is
  not moved to push, but instead borrowed" (the reader knows ownership
  transfer from §2.1).
- RustBelt's hedge "At least, that is the hope." is answered within the
  excerpt by the Coq proofs of the fundamental theorem and adequacy; its "The
  question remains: How can we verify that Rust's extensible approach makes
  any sense?" is answered by the next paragraph's first sentence.

## Where Kiran and Dreyer differ

Kiran's sentences start from what the reader holds more often (94% of
subjects given against 85%), and her new entities come after the subject
more often (85% against 79%). Dreyer often opens a paragraph by placing a new
frame in front of the reader: four of RustBelt's twelve new subjects open a
paragraph, against one of Sisyphus's three.

Dreyer has twice as many motifs (12 against 6). His safety, control,
ownership and extensibility leave and return at paragraph openers and
contrastive sentences; Kiran's are proof repair, her challenge labels C1 and
C2, and the old program and new proof.

Dreyer argues in prose: six reasoned claims, five denials, two antitheses.
Kiran argues with citations and one worked example, uses no denials, and
leaves fewer claims on her own word (8 against 14).

Kiran introduces more terms early and pays them off late (19 entities first
reused more than six sentences on, against 15).

On the LLM-isms both papers use about the same number of em-dashes, all
defining. The difference is in colons (2 dramatic against 4) and in
antitheses (none against 2).

## What escaped, and what now handles it

The second round left eleven things the rules could not see. Each now has a
mechanism in the model, the parsing or the annotation.

| what escaped | what handles it now |
|:--|:--|
| cataphoric composites ("Such changes may involve: (1) ...") | a subject that is a composite whose parts the same sentence lists after it is *announced*: acceptable, counted apart |
| summaries that paraphrase | the paragraph's argument: the point read at its first sentence is what at least half its other moves are about or use. RustBelt's "Our core contribution is then to develop an extensible soundness proof for λRust." now passes (and the is-a lore was missing that the semantic model is part of that proof) |
| an instance of a kind is its own entity | *bridging*: a subject that is a part, instance or kind-member of something mentioned is given (1 in Sisyphus, 9 in RustBelt) |
| whether a return is deliberate | a *deliberate* callback returns with a demonstrative determiner ("this problem", declared `demonstrative` in the lexicon), inside quotation marks, or in a sentence with a callback connective |
| a clause after a colon that spells out a term on the left | the annotation marks it `appos` with a ref to that term, and the rule checks the ref is mentioned on the left ("The question remains: How can we verify ...?", "is a simple one: If ownership ..."). Only Sisyphus's "a sweet spot for proof repair: it is not uncommon ..." remains dramatic |
| pre-emptive rebuttals | the paper declares lore rules (objections the reader raises unprompted); a proposition the reader can derive counts as put forward, so rebutting it is a contrast. RustBelt's "cannot easily be contained by blessing a fixed set of standard libraries" now follows from "the libraries use unsafe code" |
| spotting a hedge was my reading | stance markers (`hedge`: "hope", "seems", "at least ,") mark sentences in the tree, and the `grounded` style requires every marked sentence to carry a `hedge` move at that sentence and every `hedge` move to sit on a marked or question sentence. The same two-way check holds for not-X-but-Y and `deny`, and one-way for cause connectives and `infer` |
| whether a term was needed | an introduced entity is *needed* when an argument move uses it in its paragraph or the next; entities the argument never uses are counted |
| reasons that are definitions or background | `infer` grants a reason that is an accepted claim, a definition or background. RustBelt's "because it offers an interpretation of what types mean" now supports the claim that the semantic approach is more powerful |
| register tags words, not uses | multiword entries ("sweet spot", "holy grail", "badge of honor" informal; ", so long as" with no relation) and part-of-speech keys (`lemma/UPOS`) |
| rhythm is only length | fronted subjects (three words or more before the subject) and short paragraph closers |
| the remaining "like" similes | in a paper, a "like" phrase whose object is a tracked entity ("like C++, Rust supports ...") is a literal comparison |

What still escapes: the declared parts (lexicon classes, lore, argument
readings) are mine or a subagent's, and the checks only test that they are
consistent with the trees, not that they are right; bare "so" is too ambiguous
to tag, so only ", so" and "so ," count as cause; and the motif and need rules
depend on how finely the argument's terms match the entities.

## House style: `/writelikeme` and the clarity check

`LangLib/Style/House.lean` states Kiran's writing rules (`/writelikeme`, the
LLM-isms list and its clarity reference, after Williams and Bizup's
characters-and-actions test) as decidable rules over the same trees, with
word classes declared in `lexicon.json` (`cls`: `nominal`, `animate`,
`light`, `be`, `agent`, `significance`, `intensifier`, `buzz`, `us`, `ing`,
`wh`, `that`, `throat`, `inflation`). Subagents tagged the open classes
(nominal, animate, buzz, American spelling, -ing forms); the closed ones are
declared by hand. `langlib house <dir>` reports them.

| rule | definition |
|:--|:--|
| agentless passives (*hidden characters*) | a `be` auxiliary and a participle head (not an `ing` form) with no `by` phrase; at most one clause in ten |
| hidden actions | a subject whose head noun is `nominal` with a `light` verb or a copula ("the implementations ... make widespread use of unsafe operations") |
| inanimate actors | an `object` or `abstract` entity as the subject of an active `animate` verb ("a closed-world method, which assumes ...") |
| noun stacks | three nouns in a row in a phrase that names no tracked entity |
| point first | the subject starts twelve or more words in |
| stacked asides | a sentence of 35 words or more with a parenthetical and a relative clause |
| non-sequitur stacks | neighbouring sentences sharing no entity, joined by no connective |
| slop emphasis, throat-clearing, understated inflation | a short sentence with a `significance` word; a `throat` expression; an `inflation` expression in a copular sentence |
| tricolon with semicolons | two or more semicolons outside parentheticals |
| deferred assertion, emphatic cleft | a copular sentence with a `wh` free relative; expletive "it", a copula and a `that` clause |
| observation-and-response join, tetracolon | "and" before a clause with its own subject; four coordinated clauses |
| initial conjunction, buzz, intensifiers, British spelling | by word class |
| appositive-trailing cadence | an appositive, then a trailing adverbial clause |
| dramatic terminal, summarising pivot, summary closer | a short last sentence that negates or asserts significance; a short sentence whose subject is a composite; a last sentence that adds no entity |
| bare pivot, spurious contrast | a paragraph opening on a contrast connective without the last paragraph's entities; a contrast connective with no entity shared with the previous sentence |

Unsupported claims, antitheses and coined terms used before they are defined
are the argument world's (`Argument.lean`).

| | Sisyphus | RustBelt | roof | roof-pratchett (01–06) |
|:--|--:|--:|--:|--:|
| agentless passives / clauses | 21 / 251 | 31 / 411 | n/a | n/a |
| hidden actions / inanimate actors | 0 / 3 | 1 / 7 | 0 / 2 | 0 / 1 |
| noun stacks / buried subjects / stacked asides | 1 / 9 / 8 | 6 / 2 / 16 | 0 / 0 / 0 | 0 / 0 / 0 |
| non-sequitur stacks | 4 | 14 | 30 | 24 |
| and-joins | 3 | 3 | 11 | 8 |
| tricolons / throat-clearing / summarising pivots / summary closers | 0 / 0 / 0 / 2 | 1 / 1 / 2 / 1 | 0 / 0 / 0 / 4 | 0 / 0 / 0 / 0 |
| initial conjunctions / buzz / intensifiers / American spellings | 1 / 1 / 2 / 0 | 2 / 4 / 9 / 11 | 0 / 0 / 2 / 0 | 0 / 0 / 0 / 0 |
| spurious contrasts | 0 | 1 | 0 | 0 |
| clarity fails | inanimate actors, point first, stacked asides | inanimate actors, stacked asides, non-sequiturs | inanimate actors, non-sequiturs | inanimate actors, non-sequiturs |
| writelikeme fails | initial conjunction, buzz, intensifiers, summary closers | 9 rules (throat-clearing, tricolon, initial conjunctions, buzz, intensifiers, spelling, summarising pivots, summary closers, spurious contrast) | and-joins, intensifiers, summary closers | and-joins |

Kiran's paper passes more of her own house rules than RustBelt does (four
failures against nine), and the differences are the ones her notes predict:
RustBelt spells American ("behavior", "formalized"), clears its throat once
("let us begin by exploring what makes Rust's type system so unusual"),
tricolons with semicolons once, and leans on intensifiers ("actually", nine
times). Sisyphus's failures are a sentence-initial "But", "Crucially", two
intensifiers ("truly", "really") and two paragraphs whose last sentence adds
nothing new. On clarity Sisyphus buries its subject more often (9 against 2:
"Given this setup (the spec is fixed) and the recent advances in automated
deductive verification ..., the reader might wonder"); RustBelt stacks more
asides (16 against 8). The stories fail the non-sequitur rule heavily, which
is the right answer for a rule about argumentative prose: narration links
sentences by time and place, not by shared entities. Their passives are not
measured, because their trees carry no verb forms.

What escapes the house rules: whether a passive is a deliberate emphasis
(the clarity note allows it), whether a "real" or "actually" earns its place,
and every rule whose word class a tagger misjudged (the classes are declared,
not inferred). Tone, the "punchy" register Kiran asks for and the choice of
what to leave out are not formalised.


## Reproducing

```
langlib check    stories/private-papers/<p>/paragraphs/NN.txt NN.json   # each paragraph
langlib academic stories/private-papers/<p>                               # features, flags, verdicts
langlib house    stories/private-papers/<p>                               # house style and clarity
python3 stories/private-papers/tools/argument_prove.py stories/private-papers/<p> <Name>   # Argument.lean
python3 stories/private-papers/tools/style_prove.py    stories/private-papers/<p> <Name>   # Paper.lean, proved
python3 stories/private-papers/tools/sent.py stories/private-papers/<p> 12:1               # a flagged sentence
```
