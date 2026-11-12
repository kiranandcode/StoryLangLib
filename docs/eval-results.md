# Evaluation, 2026-11-12

Corpus: 20 passages (1,404 words): 2 each from Austen, Melville, Doyle, Twain,
Stoker, Dickinson, Shelley, Fitzgerald (Project Gutenberg), 4 from
kirancodes.me. Each model encodes each passage as a langlib document, given
the passage only (`raw`) or also its numbered tokens (`tokens`); `langlib
check` decides pass/fail and its report is fed back for up to 3 rounds.
Calls go through `claude -p` with tools and settings off; "cost" is the CLI's
API-equivalent figure.

Haiku and Fable were rerun after the bracket-balance hint was added to the
feedback; Sonnet and Opus numbers are from the first run (`eval/runs-v1/`).

## Findings

- Opus and Sonnet reach 100% within 2 rounds in both conditions; Opus is the
  fastest (~37 s/call) and cheapest.
- Fable's content is always faithful. Every Fable failure is the same JSON
  slip: on trees nested 26 to 41 deep it omits the final `]}` closing the
  sentence list and document. Appending the closers makes all of them pass
  with zero edits. With a feedback line naming the missing closers, raw
  reaches 100%; one passage (stoker-1, depth 40) still fails with tokens.
- Haiku tops out around 50%. Its failures: normalising typography (curly
  quotes and apostrophes to straight ones, `boat’s` to `boat's`), unbalanced
  brackets deep inside trees, malformed objects, inventing labels
  (`"kind": "agent"`, `"pron": "you"`). Feedback helps (35% to 55% raw), but
  giving it the token list hurts (45% to 20% first-round token match).
- The token list barely matters for the strong models (Opus 95% to 100% first
  round, Sonnet 85% to 95%).
- Generality: no model needed the escape hatches (FRAG under 1% of nodes, no
  X tags, `dep` under 0.3%). The schema covered verse, dialect, diary entries,
  letters and technical prose.
- Agreement: Opus and Fable agree on 98% of part-of-speech tags, 0.87
  labelled bracket F1 and 0.88 coreference-link F1. The others agree with
  each other at 0.96 to 0.97 POS and 0.75 to 0.81 bracket F1. POS is settled;
  phrase boundaries and coreference are where models differ.
- Jev pronoun spot-check (raw, final docs): agreement with the document's ref
  is Opus 132/135, Sonnet 110/112, Fable 159/162, Haiku 105/106. The
  disagreements are hard cases (dialect `'em`, a "him" with two candidates)
  where the model is often right.

## Flat format (2026-11-12, raw condition)

Same corpus and loop, but the tree is sent as two flat lists (`nodes`,
`words`), each item naming its parent with `in`; nesting depth is 3.

| model | first-round token match | pass r1 | pass ≤r2 | pass ≤r3 | secs/call |
|---|---|---|---|---|---|
| haiku | 15% (nested 45%) | 15% (35%) | 35% (45%) | 50% (55%) | 102 (86) |
| sonnet | 100% (85%) | 95% (80%) | 100% (100%) | 100% (100%) | 206 (116) |
| fable | 100% (95%) | 95% (90%) | 100% (95%) | 100% (100%) | 67 (61) |

- Flat removes the bracket failures: Fable passes every passage by round 2,
  including the depth-40 Stoker paragraph that nested never passed with tokens.
- Sonnet gets more accurate but slower (the ids cost output tokens).
- Haiku gets worse: it drops or alters more tokens (6.9 edits per first
  answer vs 3.2) and invents UD subtype roles (`aux:pass`, `nmod:poss`).
- Recommendation: flat for strong models; accept UD subtypes by mapping them
  to their base relation.

## Next

- Flat encoding (token table plus head and phrase ids) to remove the
  bracket-depth failure, compared against nested trees on the same corpus.
- A checker mode that reports the closers JSON is missing (now in the eval
  harness only).

## Faithfulness (token match + reference checks)

| model | cond | n | tokens ok r1 | pass r1 | pass ≤r2 | pass ≤r3 | mean edits r1 | mean ref issues r1 | mean secs/call | cost $ |
|---|---|---|---|---|---|---|---|---|---|---|
| haiku | raw | 20 | 45% | 35% | 45% | 55% | 3.154 | 0.45 | 85.62 | 3.61 |
| haiku | tokens | 20 | 20% | 15% | 40% | 45% | 2.1 | 0.05 | 84.494 | 3.91 |
| sonnet | raw | 20 | 85% | 80% | 100% | 100% | 0.158 | 0.1 | 115.679 | 3.56 |
| sonnet | tokens | 20 | 95% | 85% | 100% | 100% | 0 | 0.25 | 121.565 | 3.56 |
| opus | raw | 20 | 95% | 90% | 100% | 100% | 0 | 0.05 | 39.35 | 2.75 |
| opus | tokens | 20 | 100% | 95% | 100% | 100% | 0 | 0.05 | 35.671 | 2.43 |
| fable | raw | 20 | 95% | 90% | 95% | 100% | 0 | 0.05 | 61.039 | 7.19 |
| fable | tokens | 20 | 90% | 85% | 95% | 95% | 0 | 0.05 | 59.492 | 7.58 |

## Final pass rate by source (all models, both conditions)

| source | pass |
|---|---|
| austen | 13/16 |
| dickinson | 16/16 |
| doyle | 13/16 |
| fitzgerald | 14/16 |
| kiran | 30/32 |
| melville | 12/16 |
| shelley | 13/16 |
| stoker | 13/16 |
| twain | 15/16 |

## Tree agreement between models (final docs, raw+tokens pooled, passages where both match tokens)

| pair | n | UPOS | leaf role | brackets (labeled F1) | brackets (unlabeled F1) | mention spans F1 | coref links F1 |
|---|---|---|---|---|---|---|---|
| haiku~sonnet | 20 | 0.96 | 0.902 | 0.736 | 0.813 | 0.641 | 0.473 |
| haiku~opus | 20 | 0.954 | 0.881 | 0.755 | 0.809 | 0.655 | 0.578 |
| haiku~fable | 20 | 0.956 | 0.898 | 0.746 | 0.821 | 0.725 | 0.608 |
| sonnet~opus | 40 | 0.969 | 0.923 | 0.782 | 0.851 | 0.723 | 0.642 |
| sonnet~fable | 39 | 0.972 | 0.924 | 0.809 | 0.875 | 0.696 | 0.634 |
| opus~fable | 39 | 0.981 | 0.945 | 0.866 | 0.91 | 0.876 | 0.885 |

## Same model, raw vs tokens condition

| model | n | UPOS | brackets (labeled F1) | coref links F1 |
|---|---|---|---|---|
| haiku | 8 | 0.946 | 0.81 | 0.725 |
| sonnet | 20 | 0.975 | 0.815 | 0.625 |
| opus | 20 | 0.986 | 0.89 | 0.877 |
| fable | 19 | 0.985 | 0.919 | 0.914 |

## Escape hatches (share of nodes FRAG, leaves X, roles dep)

| model | FRAG nodes | X leaves | dep roles | categories used |
|---|---|---|---|---|
| haiku | 1.3% | 0.0% | 0.0% | ADJP ADVP COORD FRAG NP PP PRN S SBAR VP |
| sonnet | 0.5% | 0.0% | 0.3% | ADJP ADVP COORD FRAG NP PP PRN QUOTE S SBAR VP |
| opus | 0.3% | 0.0% | 0.0% | ADJP ADVP COORD FRAG INTJ NP PP PRN QUOTE S SBAR VP |
| fable | 0.4% | 0.0% | 0.0% | ADJP ADVP COORD FRAG NP PP PRN QUOTE S SBAR VP |
