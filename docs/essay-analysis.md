# Two blog essays, read by every analysis StoryLangLib has

Kiran's two posts on kirancodes.me are read here with the same machinery as
the papers in `docs/style-academic.md` and the stories in the Studio:

- *Bloom filters debunked: Dispelling 30 Years of bad math with Coq!* (2020),
  an empirical argument whose evidence is mechanised proof
  (`stories/essay-bloomfilters`, 58 paragraphs);
- *PL research is dead, the age of PL exploration is just beginning!* (2026),
  an opinion essay, as a contrast (`stories/essay-end-of-pl`, 24 paragraphs).

Both are her published posts, so the prose, the annotations and every
reading are committed. Each essay is two things at once: a Studio story (its
world in `story.json`, its readings in `paragraphs/NN.events.json`, proved
in `Proofs.lean`) and a paper (its argument in `argument.py`, proved in
`Argument.lean`, with the style records in `Paper.lean`).

## The texts

`paragraphs/NN.txt` holds one paragraph of prose per file. What was dropped
or changed:

- figures (13 images in the Bloom post, the screenshots and bit-vector
  diagrams), the post titles, section headings, dates and tags. Headings
  become section starts (`discourse.json`) and beats;
- the Bloom post's display formula (Bose et al.'s expression, after ¶40's
  colon) and its inset Coq link targets. The inset explanation of no false
  negatives is her prose and is kept (¶18);
- the quoted TYPES message after end-of-PL ¶2's colon, which is someone
  else's words;
- footnote markers. The six footnotes are kept as paragraphs 48-58, and each
  marker is read as a promise paid by its footnote;
- inline maths written as ASCII tokens (`(1 - 1/m)^(kn)`, `b1`, `k=2`,
  `P[ b2 is raised | b1 is raised ] != P[ b2 is raised]`); URLs kept as
  tokens;
- definition lists and centred callouts inlined: a `dt` becomes a run-in
  label with a colon ("No false negatives: This states ..."), a bulleted list
  joins the paragraph that introduces it. Typos are kept ("a approximate",
  "ever day", "from the from that", "depedent").

Every paragraph is annotated in the `eval/prompt.md` format with the academic
marks: `generic` and `of` on entities, `VerbForm` and `Tense` on every verb,
a role for whatever follows each colon and dash, a register for every
content word (`lexicon.json`, merged from `lexicon.local.json` over
`tools/house/base-lexicon.json`), and a `~sense` on every noun the world
does not hold. All 82 are accepted by `langlib check`, and by
`workflows.py paragraph-check`, which adds the setting, the reading and
completeness. Seven subagents annotated in parallel; I wrote the worlds, the
beats and the argument readings, and checked every verdict.

## The worlds: the reader and the camps as minds

An essay is a story whose characters are the voices of its argument. Each
`story.json` declares them, with what they hold at the start (`lit@rank:evidence`
for a belief held on weaker grounds):

| essay | at the post (they read it) | elsewhere |
|:--|:--|:--|
| Bloom | Kiran (I, we), the reader (`bloomFormula@1:rumour`), practitioners who use and cite Bloom filters (`bloomFormula@2:told:bloom`), the Hacker News commenter | in the literature: Bloom (`bloomFormula@3:inferred`, `bitsIndependent@3:assumed`), Bose et al., their critics, the reviewers |
| end-of-PL | Kiran, the reader (`plObsolete@1:rumour`), the juniors watching (`plObsolete@2:told:pessimists`) | on the TYPES list: the pessimists (`plObsolete@3:inferred`); elsewhere: SE researchers, the dynestyx colleagues |

The facts are the essays' propositions (21 + 1 for Bloom, 27 + 2 for
end-of-PL), each true or false in Kiran's view, with lore rules such as
"bits independent and the single-bit probability give the cited formula".
Published work reaches the post as a `message` (Bloom's derivation, Bose et
al.'s correction), so the literature does not overhear the post.

What the reader comes to believe, paragraph by paragraph (the Minds view):

- **Bloom.** At ¶7 the reader drops the rumoured cited formula (strength 0)
  for its negation told by Kiran (strength 5: 3 for being told, 1 for
  trusting her, 1 for being open-minded); the practitioners follow at
  strength 3. At ¶10 the reader derives Bose et al.'s formula from the
  certified proof (by lore, no telling). Bits not independent (¶36) and hashes
  not always distinct (¶37) are told outright. In footnote 3 (¶50) the Hacker
  News commenter tells Kiran that Bloom's hashes are distinct; the
  practitioners overhear it and flip, the reader does not, because Kiran's
  concession is read as the commenter's telling and the reader already holds
  the opposite on her word at strength 5.
- **End-of-PL.** The reader flips "PL research is becoming obsolete" at ¶11,
  derived by lore from "the ideas remain" and "applications do not matter".
  The juniors, whom the essay addresses, end the essay still believing it:
  they trust the pessimists, hold everything Kiran says only conservatively
  (strength 2), and the essay gives them nothing but her word to weigh. The
  same holds for every one of her 30 bare claims (below). This depends on the
  trust I declared (reader 2, juniors none); it is the model's way of saying
  the essay persuades by voice, not by evidence.

## Completeness: every clause, connective and modifier judged

Every clause carries a judgement anchored at its head (an event, an anchored
claim, or content, goal, act, speech, hypothetical, generic), every
connective is checked in the model and every adverb carries a sense. Both
essays are complete, with no issue in any paragraph:

| | Bloom | end-of-PL |
|:--|--:|--:|
| clauses / judgements | 319 / 324 | 196 / 197 |
| generic / hypothetical / claim / act / event / content / goal / speech | 97 / 73 / 49 / 36 / 34 / 29 / 4 / 2 | 30 / 27 / 19 / 29 / 44 / 47 / 1 / 0 |
| links read off the trees | 45 (12 during, 12 after, 9 purpose, 6 condition, 3 concession, 3 cause) | 12 (6 purpose, 4 condition, 2 after) |

The difference in kind is the difference in genre. Bloom's clauses are
generalisations about a data structure (present tense, no character as
subject) and hypotheticals ("we can perform", "would return"); end-of-PL's
are her own acts and the content of her beliefs. The cause and time links
(Judgements view) are checked where both sides are world judgements; where
one side is generic or hypothetical the link is not checked, which is most
of an essay's "because" and "as".

## Refinement: sections as beats

Each section (Bloom: nine, end-of-PL: eight) is a beat with a key event
(Bloom's `motivate` is keyed by "Kiran tells the reader browsers use a Bloom
filter as a local proxy", its `refute` by "the bits are not independent").
`workflows.py refine-check` passes for both: the paragraphs' readings
abstract to exactly the beat story, and `plan-check` finds the beats valid.

**Proof status.** `Argument.lean` and `Paper.lean` are proved for both
essays. The story files (`Proofs.lean`) are not yet proved: end-of-PL's
proved before its world gained the literature and thread places and must be
re-run; Bloom's hit a generator bug (`storyLean` built `ParaCtx` with the
2-field anonymous constructor after the structure gained a defaulted `base`
field; fixed in `LangLib/Studio/Load.lean`) and then an oversized bundled
conjunction, because one footnote event was marked `flashback`, which
disqualifies the checkpoint generator. That event is now `main`, and a
re-run of `workflows.py prove` is pending.

## The argument

`argument.py` reads each paragraph into `World/Argument` moves, with the
sentence each move sits on. `tools/essay/prove.py` evaluates it and writes
`Argument.lean`, whose theorems (`valid`, `gaps_are`, `antitheses_are`,
`contrasts_are`, `deferred_are`, the `lore_needed_*` probes) are proved by
`decide +kernel`. The Coq links ("see here for the Coq proof") are read as
`evaluate`: machine-checked proof is this essay's benchmark, the data's
word rather than the author's.

| | Bloom | end-of-PL | Sisyphus | RustBelt |
|:--|--:|--:|--:|--:|
| moves | 122 | 63 | 102 | 151 |
| valid | yes | yes | yes | yes |
| claims on the author's word alone | 8 | 30 | 9 | 13 |
| reasoned claims (`infer`) | 19 | 3 | 5 | 15 |
| evaluations (mechanised proofs) / citations / worked examples | 4 / 18 / 5 | 0 / 3 / 3 | not counted | not counted |
| antitheses / contrasts | 1 / 3 | 2 / 2 | 0 / 0 | 1 / 4 |
| promises never paid in the text | 1 | 0 | not counted | not counted |
| deferred (hedges left open, things left to the paper) | 10 | 5 | 12 | 8 |

**Bloom.** The main claim is that the widely cited false positive rate is
wrong (¶7) and that the true one is now certified (¶10). It is supported:
the cited formula is put forward as Bloom's (¶35), the independence step is
denied (¶36), the counterexample is a worked example (¶37), and "So clearly
this is not the correct expression" (¶38) is inferred from it, so the reader
accepts it outright, not on her word. The certification rests on a citation
of the CAV paper (¶12) and the Coq proof (¶42). The derivation in §2 is a
chain of seven inferences each granted by the last. What rests on her word
alone: that the database of malicious URLs is huge, that browsers implement
the proxy compromise, that few honest URLs are sent, that privacy is kept,
that there have been "30 years of mathematical contention" (¶8: Bloom 1970
and Bose 2008 are cited, the thirty years of contention are not), that the
rate depends on the hashes, that the work matters (¶44) and that fingerprinting
is a risk (¶48). The one unpaid promise is "(more on this later)" (¶22): the
reasons for modelling the hashes as random never arrive. The antithesis is
"it only applies for a single bit not a false positive result" (¶33),
denying what nobody proposed; the contrasts deny what was put forward
(bits independent, the cited formula, the history at risk). Footnote 6
concedes that the asymptotics agree, "so the impact is more an issue of
pedantry", which the model reads as an inference granted by a delivered
term: the essay's own last word on its stakes.

**End-of-PL.** The main claim is the central premise (¶5): shift from
ego-driven defence to exploration. Of 35 distinct claims, 30 rest on her word alone,
including the premise itself, that language models write code well, that
most languages have no users ("literally 0 users", ¶11) and that the field
is entering a transformative moment. Her three projects (¶17-19) and the
counterfactual questions (¶20) are worked examples and support the claim
that LLMs let researchers test counterfactuals fast. The antitheses are "We
don't need to compromise those ideas ..., but ..." (¶9) and "They were not
programming languages researchers but we helped them ..." (¶19); the
contrasts deny that applications matter (put forward by ¶9's "boil down to
practical applications") and that LLMs should affect a newcomer's enthusiasm
(put forward by the pessimists' fear, ¶7). "Since its inception" (¶9) is
temporal, but the lexicon reads bare "since" as a cause, so ¶9 carries an
`infer` with no premises to satisfy the grounded rule.

The `lore_needed_*` theorems prove that without probability, independence and
hashing in the reader's background the Bloom post uses a term before it
defines it, and that end-of-PL relies on the reader already knowing what
ego and exploration mean.

## Style

`Paper.lean` restates the records `langlib academic`, `style` and `house`
print, and proves every verdict below by `decide +kernel`, with the
not-X-but-Y count taken from the argument world.

| style | Bloom fails | end-of-PL fails |
|:--|:--|:--|
| Kiran's principles (`kiran`) | motifs, questions answered | questions answered |
| LLM-ism free | not-X-but-Y, rhetorical questions | not-X-but-Y, rhetorical questions |
| no em-dashes (literal) | holds (see below) | fails |
| annotated, grounded | hold | hold |
| clarity | inanimate actors, point first, stacked asides, non-sequiturs | inanimate actors, non-sequiturs |
| `/writelikeme` | 9 rules | 13 rules |
| Pratchett | footnotes, similes, Concepts | same |
| roof | parentheticals, generalisations, interiority, Concepts, dialogue | same |
| AO3 | sentence length, short sentences, dialogue, check-ins | dialogue, check-ins |

One example per failed rule:

- *questions answered*: "and how can we be certain?" (Bloom ¶11, a promise
  list); "Who the heck cares if anyone uses programming languages?" (end-of-PL ¶11).
- *motifs* (Bloom): six entities leave and return, against the one per eight
  paragraphs the rule asks; the post re-introduces its terms by section.
- *rhetorical questions*: "Seems correct?" (Bloom ¶36); "So why care about
  programming languages at all?" (end-of-PL ¶7).
- *not-X-but-Y*: the antitheses above.
- *em-dashes*: "Ship your interpreters — LLMs are incredibly capable ..."
  (end-of-PL ¶17, a run-in label, defining).
- *inanimate actors*: "this independence argument actually generalises over
  all the hash invocations" (Bloom ¶31); "they can totally verify programs"
  (end-of-PL ¶17, the LLMs).
- *point first*: "In other words, if we get a negative result for a query,
  we can be certain ..." (Bloom ¶18).
- *stacked asides*: "Well, never fear, I am writing this post to inform you
  that ... (pardon the pun) ..." (Bloom ¶10).
- *non-sequiturs*: the question list of Bloom ¶11; end-of-PL has 30, from
  its fragments and exclamations ("This is crazy.").
- *throat-clearing*: "Now, let's have a look at what happens when ..."
  (Bloom ¶27); "Let's dig into the fears of practicing researchers" (end-of-PL ¶6).
- *tetracolon*: Bloom ¶7's four-clause run to "and that is:"; end-of-PL ¶19's
  "This language lacks ..., and ..., but ..., nor ...".
- *sentence-initial conjunctions*: "and how can we be certain?" (Bloom ¶11);
  "So why care ...?" (end-of-PL ¶7).
- *buzz*: "nifty" (Bloom ¶1); "disruptive" (end-of-PL ¶1).
- *intensifiers*: 41 in Bloom ("actually", "rather", "simply"), 26 in
  end-of-PL ("extremely", "absolutely", "crazyyy").
- *summary closers*: "In other words, ... never been inserted into the Bloom
  filter before." (Bloom ¶18); "Humans aren't going to be writing them." (end-of-PL ¶7).
- *bare pivots*: Bloom ¶3 opens on "Conversely" without ¶2's entities.
- *bare relative clauses*: "every URL that a user visits" (Bloom ¶3); "A lot
  of presumptions we build upon" (end-of-PL ¶16).
- *filler*: "In reference to the fact that ..." (Bloom footnote 2).
- end-of-PL only: *emphatic cleft* and *summarising pivot* ("It wouldn't be
  too far to say that ...", ¶2; "Some were positive, but the majority
  opinion was overwhelmingly negative.", ¶2), *British spelling* ("defense",
  ¶5), *dramatic terminal* ("Humans aren't going to be writing them."),
  *abstract significance* ("a genuinely transformative moment", ¶24),
  *manufactured enthusiasm* ("I have never been more excited!", ¶4).

## Blog voice against paper voice

The Sisyphus and RustBelt columns are from `docs/style-academic.md`.

| | Bloom | end-of-PL | Sisyphus | RustBelt |
|:--|--:|--:|--:|--:|
| sentences / words | 87 / 2383 | 86 / 1301 | 75 / 2255 | 115 / 3323 |
| words per sentence (mean, sd) | 26.3, 13.1 | 15.9, 13.4 | 32.7, 13.7 | 29.5, 15.1 |
| coefficient of variation | 0.50 | 0.85 | 0.42 | 0.51 |
| punches (short after long) / runs of ≥ 3 long | 0 / 0 | 1 / 1 | 0 / 4 | 4 / 9 |
| register: technical / formal / informal / neutral (%) | 38.7 / 9.9 / 2.8 / 48.5 | 11.3 / 5.0 / 7.9 / 75.8 | 44.9 / 4.3 / 1.1 / 49.7 | 42.8 / 5.2 / 1.2 / 50.8 |
| subjects given | 55/69 (80%) | 44/52 (85%) | 98% | 96% |
| new entities after the subject | 88/118 (75%) | 36/46 (78%) | 86% | 71% |
| first sentence summarises | 11/13 | 13/18 | 18/18 | 28/29 |
| just in time | 38/62 (61%) | 22/35 (63%) | 57% | 64% |
| motifs | 6 | 7 | 6 | 12 |
| questions set up / answered | 13 / 4 | 11 / 3 | 1 / 1 | 3 / 3 |
| agentless passives / clauses | 32 / 319 | 4 / 196 | 21 / 251 | 31 / 411 |
| intensifiers | 41 | 26 | 2 | 9 |
| first-person clauses | 7 | 44 | not counted | not counted |

Her blog voice is measurably different from her paper voice, in three ways.
It asks questions (13 and 11 against Sisyphus's one) and leaves most of them
for the reader, which her paper never does. It intensifies (41 and 26
intensifiers against 2). And the opinion essay changes register outright:
three quarters of its content words are neutral and 8% informal, against
half and 1% in the papers, with sentence lengths that vary twice as much
(0.85 against 0.42). The Bloom post sits between: it keeps the papers'
technical register (39%) and their long sentences, but drops the old-to-new
discipline (80% of subjects given against 98%). End-of-PL passes every AO3
rhythm rule (mean length, short sentences, punches, intensifiers) and fails
only dialogue and check-ins; Sisyphus passes none of them.

What does not change is the argument's shape where it matters. The Bloom
post supports its thesis the way Sisyphus does, with citations and a worked
example, and leaves about as many claims on her word (8 against 9).

## The Studio

Both essays appear in the Studio's story menu (Paragraphs, Judgements,
Argument, Minds, World, Style, Story, Proofs) and in its papers group
(argument graph with grounded labels, moves, academic style). The papers
view now also lists `stories/essay-*` directories that carry an
`argument.py` (`studio/extras.py`, `studio/server.py`). The Power view does
not apply: it shows a rule-based power system's moves (Nen, Magic, the Death
Note), and an essay has none. Screenshots of every view for Kiran's annotator
scratchpad ("essay analysis") are still to be taken (`tools/essay` has no
script for it yet; a CDP test window on port 9333 worked for the Paragraphs view).

## What the analysis misses

- **Dashes it cannot see.** The academic rule counts "—" and "--"; the Bloom
  post writes its dashes as a spaced "-", so its 30 dashes are invisible to
  the proved counts. Classified by the same rule outside Lean, 5 are
  dramatic (¶2, ¶25, ¶33, ¶37, ¶48: "... than one would expect - in
  particular, tracking ... turns out to be somewhat difficult"). End-of-PL's
  en dashes ("–") are invisible too.
- **Checker workarounds** the annotators flagged: contracted modals
  ("wouldn't", "we'd", "can't") are not read as modal, so such clauses were
  judged generic or by a claim; imperatives have no subject, so "Let's dig",
  "believe me" and "Fuck the users" are generic rather than acts; "as" is
  read as time ("as we're treating the hash functions as random") and passes
  only because the clauses are hypothetical; Bloom ¶54's "this is because"
  is judged generic, since the lore had no rule from "bits not independent"
  to "the cited formula is wrong".
- **The world is coarse.** One fact per proposition, and every telling at
  the post is heard by everyone there. A few readings are loose: "This
  research was just recently presented at CAV2020" is judged by the claim
  "the authors have a certified proof".
- **Readings are mine.** The argument moves, the trust bonds, the starting
  beliefs and the lexicon classes are declared, then checked for consistency
  with the trees; they are not inferred. The juniors' result above is only as
  good as the trust I gave them.
- **What is not formalised.** The figures carried part of the Bloom
  argument (the bit-vector pictures), tone and humour ("pardon the pun"), the
  swearing in end-of-PL ¶12, the date-stamped context (the post was written
  before her transition, per its banner), and whether a claim is true.
- **Not used.** The `ext` readings (ties, care, identity, affect) and the
  consent reading have nothing to read in an essay: no ties form, no needs
  are tended, nobody is misnamed, and no intimacy is asked for.

## Reproducing

```
python3 studio/workflows.py paragraph-check stories/essay-bloomfilters N   # each paragraph
python3 studio/workflows.py refine-check    stories/essay-bloomfilters     # beats
python3 studio/workflows.py prove           stories/essay-bloomfilters     # Proofs.lean
python3 tools/essay/prove.py stories/essay-bloomfilters Bloom              # Argument.lean, Paper.lean
python3 tools/essay/prove.py stories/essay-end-of-pl EndOfPL
```
