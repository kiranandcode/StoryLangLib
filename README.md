# langlib

Lean 4 datatypes for English text — parts of speech, phrase structure, entity
references — that render back to the exact list of source tokens, plus a story
layer for checking that characters act in character.

The point is an anti-hallucination gate for LLM annotation: an LLM turns text
into a langlib document (JSON), and `langlib check` accepts it only if the
tree's leaves are exactly the tokens of the source text and every reference
resolves and agrees.

## Layers

| layer | what | file |
|---|---|---|
| tokens | deterministic tokenizer, `detokenize` | `LangLib/Token.lean` |
| syntax | constituency tree; leaves carry UD part of speech, lemma, features; edges carry UD relations | `LangLib/Basic.lean` |
| reference | entities declared once; words/NPs point at them; pronoun agreement; anaphora vs cataphora derived from position | `LangLib/Refs.lean` |
| topics | topics group entities; sentences link to a topic | `LangLib/Basic.lean` |
| render | `Tree.render : Tree → List String` (leaves in order) | `LangLib/Render.lean` |
| check | token diff (edit alignment), bad leaves, reference issues | `LangLib/Check.lean`, `LangLib/Diff.lean` |
| defeasible logic | `Strict`/`Def`/`NotDef` as mutually inductive relations; `coherent` (nothing is both provable and refuted); certificates checked by `decide` (`Cert.sound`) | `LangLib/Story/DL.lean` |
| scenes | state (places, objects, knowledge by observation, threats), events with hard preconditions, `Valid` story relation, character plausibility from personas (traits + ranked values); `validB_sound`; author-facing `explain` | `LangLib/Story/Scene.lean` |
| example | the gate scene: a valid story, a knowledge-leak plot hole, an out-of-character shout, a drunk shout, a gagged shout, each proved | `LangLib/Story/GateScene.lean` |

## CLI

```
lake build
.lake/build/bin/langlib tokenize examples/cata.txt
.lake/build/bin/langlib check examples/cata.txt examples/cata.json
.lake/build/bin/langlib render examples/cata.json
.lake/build/bin/langlib pretty examples/cata.json
```

`check` prints a JSON report and exits 0 when the document is faithful, 1 when
it is not, 2 when it does not parse. The JSON format is documented at the top
of `LangLib/Json.lean` and in `eval/prompt.md`.

## Evaluation

`eval/` has a 20-passage corpus (Project Gutenberg: Austen, Melville, Doyle,
Twain, Stoker, Dickinson, Shelley, Fitzgerald; plus 4 passages from
kirancodes.me), a runner that asks each model to encode each passage, checks
it, and feeds the checker report back for up to 3 rounds, and an analysis
script for pass rates and cross-model tree agreement.

```
cd eval
python3 build_corpus.py
python3 run_eval.py --models haiku,sonnet,opus,fable --conds raw,tokens --jobs 12
python3 analyze.py
```

Conditions: `raw` gives the model only the passage (it must transcribe every
token itself); `tokens` also gives the numbered token list.

## Literature

- `docs/lit-linguistic-encoding.md`: UD, GF, coreference, discourse, LLM parsing.
- `docs/lit-story-logic.md`: narrative planning, Ceptre/Versu, argumentation,
  defeasible logic, epistemic state, LLM story-coherence work, and the layered
  design the story layer follows.

## Name

There is already a Lean package called `langlib` (nielstron/langlib, formal
languages); rename before publishing.
