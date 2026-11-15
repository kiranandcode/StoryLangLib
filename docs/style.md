# Style as decidable predicates over checked trees

Can a writing style be captured formally in StoryLangLib? Partly. A style is
a set of decidable rules over the trees `langlib check` has already accepted.
The rules separate two tellings of one story cleanly, and the kernel proves
which telling is in which style. What separates them, though, is the
apparatus of the style (footnotes, generalisations, similes, Concepts), not
the part a reader would call the style itself (the jokes, the diction, the
timing). This note says which features did the work, which didn't, and what
a tree can't see.

## The experiment

`stories/roof` is the Kiran and Ran story in close third person. Its
`meta.json` describes it as "interiority over choreography". `stories/roof-pratchett` is the
same world, beats and paragraph plans (`story.json` and the `NN.plan.json`
files are copied), told in the manner of Terry Pratchett. It has footnotes,
an omniscient narrator who generalises in the present tense, capitalised
Concepts, similes that swerve, and, under the jokes, a moral about being asked
and meaning yes. Its sentences are pastiche; none of them are his. Every paragraph
passes `paragraph-check` with the same events as roof (same moves, beliefs,
consent, kiss), so `refine-check` holds against the same beats.

The two tellings share 476 of roof-pratchett's 1,344 words verbatim (55 of
101 sentences, mostly the dialogue and the confession and consent scenes).
That makes this a controlled comparison: the features that differ come from
what the Pratchett telling adds and changes, not from a different plot.

## Conventions the annotation needed

**Footnotes.** In the text, the anchor mark (`*`, then `†`, `‡`) follows the
anchor sentence's final punctuation. The note goes at the end of the paragraph
on its own line and starts with the same mark. The tokenizer already makes each mark one token. In the tree:

* the anchor is a leaf `{"w": "*", "p": "SYM", "r": "dep"}`, a direct child of
  the anchor sentence's root, so no constituent depends on it;
* the note is one tree `{"c": "PRN", "r": "root", "k": [{"w": "*", "p": "SYM",
  "r": "mark"}, S, S, ...]}`.

Why this convention:

* Tokens stay in text order, so the leaves-equal-tokens check needs no change.
* The anchor sentence is a complete tree without the note. That is the
  structural rule `footnotesPaired`: every anchor has exactly one later note
  with the same mark, and the anchor sentence without its mark still has a
  clause head and ends in terminal punctuation.
* The note is a single unit even when it runs to two sentences, so the
  features can measure it and the rule `footnotesGeneric` (every note
  contains a generalisation) can check it.
* Putting the note inline would have split the anchor sentence's tree, and
  the Studio's reader would show a sentence broken in half.

**Generic statements.** A narrator's generalisation is a clause in the present
tense, outside speech, whose own subject refers to nothing in the world:
"People do.", "Kettles know this", "a heron at a pond that has never once
held a fish". The annotation marks the verb, copula or auxiliary with
`"f": {"Tense": "Pres"}`, and gives generic nouns the new sense `kind`.

The completeness checker (`LangLib/Studio/Complete.lean`) required every
clause to have a judgement, and it had no kind for this. It could judge a
clause as an event, a claim, content, a goal, a gesture, speech, a
hypothetical or an external move. A narrator's generalisation is none of
these. So the checker gained a `generic` judgement. It holds only when the
clause is present tense, not quoted or said, and its own subject is neither a
character nor a thing of the setting.

A clause with no tense of its own takes the tense of the clause above, and a
clause with no subject takes that clause's generic subject. This is what lets
"people who are not ready *to go* back into a room" count as generic. Without
it, "go" would inherit Kiran as its subject from the main clause.

A deliberate mislabelling is caught. Marking "He said it plainly" generic
fails with "the clause at 'said' (token 143) is read as generic, but it is
not in the present tense".

## The styles, as stated in Lean

Features (`LangLib/Style/Core.lean`) are computed by `sentOf` from each
sentence tree into a flat record, and summed by `Features.ofSents`. All counts
are Nat, and ratios are compared by cross-multiplying. Rules are `atLeast`,
`atMost`, `ratioAtLeast` and `ratioAtMost`, plus the two structural footnote
rules.

**Pratchett** (`LangLib/Style/Pratchett.lean`):

| rule | as stated | roof-pratchett | roof |
|:--|:--|:--|:--|
| footnotes | footnotes / paras ≥ 1/2 | 8/9 | 0/9 ✗ |
| footnotes anchored | `footnotesPaired` | ✓ | ✓ (vacuous) |
| footnotes generalise | `footnotesGeneric` | ✓ | ✓ (vacuous) |
| footnotes brief | footnoteWords / words ≤ 1/5 | 178/1336 | 0/946 |
| generics | generics / sents ≥ 1/4 | 54/90 | 0/76 ✗ |
| similes | "like" similes / paras ≥ 1/2 | 8/9 | 0/9 ✗ |
| Concepts | concepts / paras ≥ 1/2 | 9/9 | 0/9 ✗ |
| asides over interiority | asides / interior ≥ 2 | 62/12 | 0/11 ✗ |

**Roof**, "close third, interiority over choreography"
(`LangLib/Style/Roof.lean`):

| rule | as stated | roof | roof-pratchett |
|:--|:--|:--|:--|
| close third | pov clauses / character clauses ≥ 1/2 | 48/90 | 49/93 |
| no footnotes | footnotes ≤ 0 | 0 | 8 ✗ |
| no parentheticals | prn ≤ 0 | 0 | 0 |
| few generalisations | generics / sents ≤ 1/20 | 0/76 | 54/90 ✗ |
| interiority over asides | interior / asides ≥ 3 | 11/0 | 12/62 ✗ |
| no Concepts | concepts ≤ 0 | 0 | 9 ✗ |
| dialogue | quote words / words ≥ 1/10 | 147/946 | 136/1336 |
| plain tags | non-"say" tags / tags ≤ 1/3 | 0/9 | 0/9 |

**Theorems** (`LangLib/Style/Theorems.lean`, all by `decide +kernel`, over
records printed by `langlib style <dir> --lean`):

```lean
theorem roof_roof : roofStyle.holds roofFeatures = true
theorem roof_not_pratchett : pratchett.failing roofFeatures =
  ["footnotes", "generics", "similes", "Concepts", "asides over interiority"]
theorem roofPratchett_pratchett : pratchett.holds roofPratchettFeatures = true
theorem roofPratchett_not_roof : roofStyle.failing roofPratchettFeatures =
  ["no footnotes", "few generalisations", "interiority over asides", "no Concepts"]
theorem roof_not_literally_interiority_over_choreography :
  (Rule.ratioAtLeast .interior .choreo 1 1).holds roofFeatures = false
```

`langlib style <dir>` prints the features and each style's verdict, rule by
rule.

## Which features carried the style

* **Generalisations.** 54 generic clauses against 0, the widest margin of
  any feature. The clearest single sentence is a minimal pair. Roof has "Of
  course he had gone. People did." Roof-pratchett has "Of course he had gone.
  People do." In the past tense the line is Kiran's free indirect thought; in
  the present it becomes the narrator's Great Truth, with a footnote to say so.
  The whole stylistic difference is one `Tense` feature on one leaf, and the
  tree sees it.
* **Footnotes.** Eight notes, all paired and all generalising. The structural
  rules hold of every note, and none of the eight needed changing to meet them.
* **Concepts and "like" similes.** 9 against 0 and 8 against 0. Both are
  cheap to detect and both separate the styles.
* **Asides against interiority.** Roof-pratchett has 62 narrator asides
  (generic clauses, parentheticals and footnotes) against 12 clauses of
  Kiran's mind. Roof has 0 asides.

## Which features did not

* **Sentence length and depth.** Roof averages 12.4 words and depth 5.3 per
  sentence; roof-pratchett averages 14.8 words and depth 5.3. Long sentences
  (25 words or more) are 9% of roof and 18% of roof-pratchett. Short
  sentences are about a third of both. The difference is too small and too
  noisy to state as a rule. Pratchett's rhythm is long, then short: the
  generalisation, then the deflation ("Nobody has ever caught a kettle in the
  act."). That is a fact about the order of sentences, and these features
  only see their distribution.
* **Speech tags.** Both stories use only "said" (9 tags, 1 kind). The plain-tag
  rule holds for both.
* **"As if" similes.** Roof has 6 and roof-pratchett 7. Close third uses them
  as much as the narrator does, so only "like" + NP separates the styles.
* **Interiority itself.** Roof has 11 clauses of perceiving, thinking or wanting
  with Kiran as subject, and roof-pratchett has 12. The rule
  "interiority over choreography" is false of roof as stated: 11 against 79
  clauses of physical action. The theorem
  `roof_not_literally_interiority_over_choreography` records this. Roof's
  interiority lives in free indirect lines ("Of course he had gone."), in
  evaluation ("annoyed at how fast her stomach had dropped"), and in what
  she notices. None of that is a verb of the mind. So the roof style is
  stated as interiority over *asides*, which is what actually separates it.
* **Close third.** About half of the clauses with a character subject have
  Kiran as subject in both stories. The Pratchett narrator stays with her too,
  so this rule doesn't separate the styles.
* **Clause-initial connectives.** Roof has 6 openers of 5 kinds and
  roof-pratchett has 7 of 5 kinds. Both are too few to say anything.

## What the checker caught while writing

The model and the completeness checker, not the style rules, forced most of
the rewrites:

* **Pronouns in generalisations.** "They are on the other side", "with their
  whole face", "it is true right up until the moment it is not", "a pond
  that has never once had a fish in it": every third-person pronoun needs a
  `ref`, and a generalisation's "it" refers to nothing in the world. Each of
  these was rewritten ("…which is not the same thing as sympathy", "with the
  whole face", "…holds until somebody comes back up the stairs", "…held a
  fish"). Pratchett's own habit of a pronoun inside the generic would need a
  generic entity kind.
* **A causal "because" between two gestures.** "made herself slow down…,
  because she was not going to arrive out of breath" failed: with the cause
  taken out of the story, the effect still holds. It became two sentences, as
  roof has it.
* **The checker's subject inheritance.** The relative and infinitive clauses
  of similes and generics inherited Kiran or Ran as their subject from the
  main clause. That would have made every simile's relative clause ("a lift
  that knows the way") a claim about a character. The fix is the generic
  subject described above.
* **A reading that over-read the prose.** In the last footnote, "somebody
  asks, somebody says yes, and both mean every word" was first annotated
  with the second and third clauses as conjuncts *under* "asks". The checker
  then took them to be what is asked, which is speech, so they could not be
  generic. The prose was right; the reading was wrong. Re-read as three
  parallel clauses in a coordination, they pass.
* **No judgement for a generalisation.** This one was not a prose problem. The
  checker's closed world had no place for a narrator who comments, so it
  needed a new judgement kind.

## What a tree-level rule can't see

* **Diction.** The register is in the words: "accumulates", "the traditional
  use of a kettle", "resent", the mock-formal set against the domestic. A
  tree has lemmas but no register. A lexical layer could see it: Latinate or
  formal ratios, or word frequencies against a reference corpus.
* **Rhythm.** The timing of the joke: the long setup, the short sentence, the
  footnote placed after the punchline. Features over sentence order (length
  of sentence n+1 against sentence n after a generic, the position of a
  footnote's anchor) would get closer. Syllable and stress counts would get
  closer still.
* **The jokes themselves.** Bathos is an incongruity: a heron, then a pond
  with no fish; a jewellery box, then somebody kicking it over. The tree sees
  "like" + NP + relative clause, which a flat simile has too. Whether a
  simile swerves depends on what the reader expected, which needs a model of
  expectation (a language model's surprisal at the turn, or a human
  judgement recorded as a checked annotation, like `generic`).
* **Warmth.** The Pratchett telling's footnotes 8 and 9 ("Asking is not the
  dull part…", "somebody asks, somebody says yes, and both mean every word")
  are the moral seriousness under the jokes. To the rules they are two more
  generic footnotes. The story model does know that consent was asked and
  given (`consented`, the `agree` events), so a rule could require that a
  generalisation about asking sits in the paragraph where the model records
  consent. That would join style to story. It isn't written yet.
* **Trust.** The kernel recomputes the features from per-sentence records,
  not from the trees: `sentOf` is `partial` and runs only in the CLI. So the
  link from a tree to its record is trusted, and the check is to regenerate
  the records with `--lean`. Every generic count also trusts the annotation's
  `Tense` features. Roof's annotation has none, so roof has 0 generics by
  construction, not by measurement. The completeness checker confirms that a
  clause marked present and judged generic is outside speech and about no
  one, but not that the verb really is present tense.
