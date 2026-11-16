# Verified deslopify: four examples from Wikipedia

Four passages of real LLM-written text, quoted as examples in Wikipedia's
guide [Signs of AI writing](https://en.wikipedia.org/w/index.php?title=Wikipedia:Signs_of_AI_writing&oldid=1385890265),
were each annotated as a langlib document, checked against Kiran's house
style, rewritten until every rule held, and checked again. The
`verified-deslopify` skill (`~/.claude/skills/verified-deslopify`) runs the
same loop on any text.

| example | source | words before / after | rules holding before | after |
|:--|:--|--:|--:|--:|
| [Statistical Institute of Catalonia](idescat/comparison.md) | article, Sept 2024 | 65 / 47 | 29/33 | 33/33 |
| [McAllen Texas Temple](temple/comparison.md) | article, Nov 2024 | 105 / 49 | 28/33 | 33/33 |
| [Somali cuisine](somali/comparison.md) | article, May 2025 | 118 / 61 | 28/33 | 33/33 |
| [Northern English nationalism](northern/comparison.md) | deletion discussion, Aug 2025 | 121 / 126 | 25/33 | 33/33 |

Each directory holds `source.md` (where the text comes from), `original/` and
`rewrite/` (the paragraphs, their annotations in `tools/house/sx.py`
notation, the text's own word classes in `lexicon.local.json`, and the
certification `report.md`), and `comparison.md` (before, after, and every
rule that failed with the sentences it flagged).

## What the check is

`tools/house/certify.py <dir>` runs, in order:

1. `langlib check` on every paragraph: the annotation's leaves must be
   exactly the text's tokens, and every pronoun must have a referent.
2. `langlib house`: the clarity check and the `/writelikeme` ban list
   (`LangLib/Style/House.lean`, described in `docs/style-academic.md`).
3. `langlib academic`, for the LLM-isms it decides: em-dashes, dramatic
   colons, rhetorical questions, and not-X-but-Y candidates (each must be
   rewritten or justified in `contrasts.json` as denying something the text
   put forward). With `--paper`, also the `kiran` and `annotated` styles.
4. An audit of word classes. The rules read classes from the lexicon, so
   a word nobody classified cannot be flagged. `tools/house/base-lexicon.json`
   fixes the closed classes for every text (the AI vocabulary from Wikipedia's
   guide and `llmisms.md`, intensifiers, throat-clearing, American spellings,
   connectives). The audit then lists every verb, every noun that looks like a
   nominalisation and every -ize spelling the text's own lexicon has not
   decided. A text is certified only when that list is empty. An entry that
   removes a base class from a word is printed in the report.

The originals were annotated before any rewriting, with the same conventions
as the rewrites. Each rewrite was drafted against the rules and passed on its
first run, once its word classes were decided and one missing pronoun
referent was added.

## What the rewrites dropped

Deslopping these texts mostly means deleting claims, because most of the slop
is significance asserted without a source. The rewrites keep every concrete
fact and drop:

- Idescat: "a pivotal moment", "a significant shift" and "regional
  statistical independence" (puffery). The decentralisation context stays.
- Temple: the symbolic reading ("a counter-symbol", "a bridge across
  divides", "the spirit of unity", "a sense of connection and shared
  purpose"), which the original attributes to nobody. A version with a cited
  source could put one sentence of it back.
- Somali: "intricate and diverse fusion", "rich tapestry" (twice),
  "vibrant trade and bustling commerce", "cherished and fundamental
  elements". The typo "espicially" is gone with its sentence.
- Northern: nothing. It is an argument rather than puffery, so every claim
  survives, restated without the negative parallelisms ("isn't just X—it's
  Y"), and the rewrite is slightly longer.

The rewrites name actors the originals left implicit: "Catalonia founded",
"Somalis consider", "Editors have dismissed". Each actor is the one the
original's passive or nominalisation implies.

## What the rules missed, and what was added

Annotating the originals showed what the rules missed. Four of those gaps are now closed:

| escape | example | now |
|:--|:--|:--|
| not-X-dash-Y has no "but", so the academic not-X-but-Y rule cannot see it | "The issue here isn't just sourcing—it's framing." | `negDashes`: a negation, then a dash before a clause's subject (`House.lean`) |
| significance words counted only in sentences of six words or fewer | "marking a pivotal moment", "represented a significant shift" | `abstractSig`: a `significance` modifier on a `vague` head noun (`moment`, `shift`, `role`, `elements`, ...) |
| an inanimate subject of the second of two coordinated verbs | "They are considered a delicacy and serve as ... elements" | the inanimate-actor rule reads every active conjunct |
| copula avoidance ("serves as", "stands as") is never copular, so the inflation rule could not fire | "the temple stands as a counter-symbol" | `serve`, `stand`, `boast`, `underscore` and similar are `animate`, so an inanimate subject fails "no inanimate actors" |

Still missed:

- Contractions hide the copula or auxiliary inside one token ("That's not
  just a sourcing issue", "before they're neatly labelled"), so the inflation
  and passive rules cannot see them. The dash rules caught the first; the
  second passes.
- Vague attributions and broader-trend claims with no flagged word: "is seen
  as a bridge across divides" (counted as a passive, but one in twelve clauses
  is within the limit), "This initiative was part of a broader movement
  across Spain".
- A negation inside a quotation still counts as a not-X-but-Y candidate in
  `langlib academic` ("Dismissing these as "not notable" ... while ..."). The
  rewrite removed it, so no justification was needed.
- Empty phrases built from neutral words ("a multitude of", "a direct
  result of", "symbolic features").

## Reproducing

```
python3 tools/house/certify.py docs/deslop/temple/original
python3 tools/house/certify.py docs/deslop/temple/rewrite
python3 tools/house/compare.py docs/deslop/temple/original docs/deslop/temple/rewrite
```
