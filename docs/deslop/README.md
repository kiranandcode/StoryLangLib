# Verified deslopify: eight examples of LLM text

Seven passages of real, published LLM-written text were each annotated as a
langlib document, checked against Kiran's house style, rewritten until every
rule held, and checked again. Three are notorious: the email Vanderbilt's
Peabody College sent after the 2023 Michigan State shooting (it credited
ChatGPT at the bottom), a Wikipedia paragraph about the Algerian town of
Douera, and the bios of Sports Illustrated's AI-generated product reviewers.
Four milder ones are quoted in Wikipedia's guide
[Signs of AI writing](https://en.wikipedia.org/w/index.php?title=Wikipedia:Signs_of_AI_writing&oldid=1385890265). The
`verified-deslopify` skill (`~/.claude/skills/verified-deslopify`) runs the
same loop on any text.

| example | source | words before / after | rules holding before | after |
|:--|:--|--:|--:|--:|
| [Vanderbilt's email after the Michigan State shooting](vanderbilt/comparison.md) | university email, Feb 2023 | 294 / 137 | 31/38 | 38/38 |
| [Douera](douera/comparison.md) | Wikipedia article, June 2023 | 79 / 23 | 34/38 | 38/38 |
| [Sports Illustrated's AI author bios](si-authors/comparison.md) | magazine website, 2023 | 98 / 35 | 36/38 | 38/38 |
| [Apples](apples/comparison.md) | LLM explainer pasted by Kiran, Nov 2026 | 692 / 463 | 31/38 | 38/38 |
| [Statistical Institute of Catalonia](idescat/comparison.md) | article, Sept 2024 | 65 / 50 | 34/38 | 38/38 |
| [McAllen Texas Temple](temple/comparison.md) | article, Nov 2024 | 105 / 49 | 31/38 | 38/38 |
| [Somali cuisine](somali/comparison.md) | article, May 2025 | 118 / 61 | 31/38 | 38/38 |
| [Northern English nationalism](northern/comparison.md) | deletion discussion, Aug 2025 | 121 / 123 | 29/38 | 38/38 |

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
first run, once its word classes were decided and two missing pronoun
referents were added. Extending the inanimate-actor rule to places (below)
later failed the Idescat rewrite, whose "Catalonia founded" made a place the
founder; it now names Catalonia's regional government.

## What the rewrites dropped

Deslopping these texts mostly means deleting claims, because most of the slop
is significance asserted without a source. The rewrites keep every concrete
fact and drop:

- Vanderbilt: "a tragic reminder of the importance of", "one of the key
  ways", "another important aspect", "an ongoing process that requires
  ongoing effort", "a safer, more compassionate future for all". Every
  request the email makes of its readers survives, as a request.
- Douera: "a lively community", "a dynamic hub of activity and culture",
  "coastal charm", "captivates both residents and visitors alike", "stunning
  natural beauty". What is left is the census figure and the location.
- Sports Illustrated: "never-ending list", "perils of nature", "fitness
  guru", "thrilled", "the best of the best". The rewrite cannot remove the
  fabrication: neither author exists.

- Idescat: "a pivotal moment", "a significant shift" and "regional
  statistical independence" (puffery). The decentralisation context stays.
- Temple: the symbolic reading ("a counter-symbol", "a bridge across
  divides", "the spirit of unity", "a sense of connection and shared
  purpose"), which the original attributes to nobody. A version with a cited
  source could put one sentence of it back.
- Somali: "intricate and diverse fusion", "rich tapestry" (twice),
  "vibrant trade and bustling commerce", "cherished and fundamental
  elements". The typo "espicially" is gone with its sentence.
- Northern: "growing" (in "a visible, growing movement") and "broader" (in
  "a broader cultural shift"), unsupported trend claims. The rest is an
  argument rather than puffery, so every other claim survives, restated
  without the negative parallelisms ("isn't just X—it's Y").

The rewrites name actors the originals left implicit: "Catalonia's regional
government founded", "Somalis consider", "Editors have dismissed". Each actor is the one the
original's passive or nominalisation implies.

## What the rules missed, and what was added

Annotating the originals showed what the rules missed. Five of those gaps were closed in the first pass:

| escape | example | now |
|:--|:--|:--|
| not-X-dash-Y has no "but", so the academic not-X-but-Y rule cannot see it | "The issue here isn't just sourcing—it's framing." | `negDashes`: a negation, then a dash before a clause's subject (`House.lean`) |
| significance words counted only in sentences of six words or fewer | "marking a pivotal moment", "represented a significant shift" | `abstractSig`: a `significance` modifier on a `vague` head noun (`moment`, `shift`, `role`, `elements`, ...) |
| an inanimate subject of the second of two coordinated verbs | "They are considered a delicacy and serve as ... elements" | the inanimate-actor rule reads every active conjunct |
| copula avoidance ("serves as", "stands as") is never copular, so the inflation rule could not fire | "the temple stands as a counter-symbol" | `serve`, `stand`, `boast`, `underscore` and similar are `animate`, so an inanimate subject fails "no inanimate actors" |
| places doing what people do | "Douera enjoys close proximity", "Douera captivates both residents and visitors alike" | a `place` entity counts as inanimate, like `object` and `abstract` |

A second pass closed the escapes the first one listed:

| escape | example | now |
|:--|:--|:--|
| a contraction hides the copula or auxiliary | "That's not just a sourcing issue", "before they're neatly labelled" | contractions in class `fusedbe` count as "be" for the copular and passive rules |
| vague attribution | "is seen as a bridge across divides", "experts say" | **no vague attributions**: an agentless passive of a verb of reputation (`attribution`: seen as, regarded, considered, hailed, touted), or a `weasel` phrase, in a sentence that cites nothing |
| broader-trend claims | "part of a broader movement across Spain", "a visible, growing movement" | **no broader-trend claims**: a `scope` modifier on a `trend` noun |
| filler built from neutral words | "a multitude of", "a direct result of", "the importance of", "a sense of" | **no filler phrases** |
| manufactured enthusiasm | "is thrilled to bring her expertise", "fitness guru" | **no manufactured enthusiasm** (`hype`) |
| platitudes with the writer as subject | "We must continue to engage in conversations about how we can do better" | **few exhortations**: the authors or the reader as subject with must, should, need to or let us; at most one sentence in twenty |
| a significance noun as the subject | "Its significance extends beyond its nutritional value" | counted under abstract significance |
| a negation inside a quotation | "Dismissing these as "not notable" ... while ..." | `langlib academic` no longer counts it as a not-X-but-Y candidate |

The second pass also caught phrases the first rewrites had kept from their
originals ("a wider cultural shift", "a visible and growing movement" in the
Northern comment), and those rewrites were changed.

On Kiran's Sisyphus paper the new rules flag one sentence, the opening "is
widely considered prohibitively high", an uncited attribution; two
exhortations ("we should really prove its correctness") are within the limit.
On RustBelt they flag "it is considered a badge of honor" and "plays such a
fundamental role". The first versions of the rules also flagged cited or
technical passives ("has been acknowledged in several recent efforts
(Klein et al. 2009)", "is believed to satisfy phi", "deemed a safe
extension"), so the attribution class was narrowed to verbs of reputation
and cited sentences were exempted.

Still missed, as far as these eight texts show:

- Anything whose words are in no class: the rules are decided over declared
  word classes, so a new slop phrase passes until it is added to
  `base-lexicon.json`. Every phrase above was added after a text showed it.
- Claims that are false or unsupported but plainly worded ("Isaac Newton
  reportedly said ..." is fine; "Douera is coastal" would pass too). Truth is
  not a style property.
- Selection: what a text should leave out, and whether a paragraph needs to
  exist at all (the apple article's conclusion broke individual rules, but
  "this paragraph adds nothing" is not one of them).
- Tone: whether a condolence email sounds human. The Vanderbilt rewrite
  passes because its sentences are concrete, not because a rule checks warmth.

## Reproducing

```
python3 tools/house/certify.py docs/deslop/temple/original
python3 tools/house/certify.py docs/deslop/temple/rewrite
python3 tools/house/compare.py docs/deslop/temple/original docs/deslop/temple/rewrite
```
