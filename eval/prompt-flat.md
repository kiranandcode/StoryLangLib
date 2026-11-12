You are a linguistic annotator. Encode the passage below as a langlib document: JSON only, no prose, no code fences.

## Format

```
{"entities": [{"id": "...", "name": "...", "kind": "person|group|animal|object|place|time|event|abstract", "pron": "he|she|it|they"}],
 "topics":   [{"id": "...", "label": "...", "entities": ["..."]}],
 "nodes":    [<node>, ...],
 "words":    [<word>, ...]}
```

The tree is given flat: phrases in `nodes`, tokens in `words`, each pointing at its parent phrase with `in`.
- Word: `{"w": <token>, "p": <UPOS>, "r": <role>, "l": <lemma>, "f": {<UD feature>: <value>}, "ref": <entity id>, "in": <parent node id>}`. `w`, `p` and `in` are required. List words in text order.
- Node: `{"id": <unique id>, "c": <category>, "r": <role>, "ref": <entity id>, "spk": <speaker entity id>, "topic": <topic id>, "in": <parent node id>}`. `id` and `c` are required. A node without `in` is a sentence root (one per sentence); `topic` only on roots; `spk` only on QUOTE. Every node must contain at least one word, and a node's words must be contiguous.

UPOS: ADJ ADP ADV AUX CCONJ DET INTJ NOUN NUM PART PRON PROPN PUNCT SCONJ SYM VERB X
Categories: S SBAR NP VP PP ADJP ADVP COORD QUOTE PRN INTJ FRAG
Roles (UD relations, plus `head` for a phrase's head child): head root nsubj csubj obj iobj obl expl ccomp xcomp advcl acl relcl nmod amod advmod nummod appos det poss case mark aux cop compound flat fixed conj cc vocative discourse dislocated parataxis punct dep

## Rules

1. The words, in order, must be exactly the tokens of the passage: every word and punctuation mark, in order, spelled exactly as in the source (same case, same quote characters, same dashes). Never fix, normalise, drop or add anything.
2. Tokens: a word is a run of letters/digits, kept whole across an apostrophe or hyphen between letters (`didn't`, `O'Brien`, `carpet-bag` are one token each) and across `.`/`,` between digits (`1,000`). Every other punctuation character is its own token, except that a run of `-` or of `.` is one token (`--`, `...`). So `"Sit down,"` is `"` `Sit` `down` `,` `"`, and `dogs'` is `dogs` `'`.
3. One sentence tree per sentence. Use FRAG for anything that is not a clause (verse lines, headings, list markers).
4. Declare every person, group, place or thing that is mentioned more than once, or referred to by a pronoun, as an entity. Put `ref` on each NP (or bare name/pronoun leaf) that mentions it. Every third-person pronoun (he, him, his, she, her, it, its, they, them, their, ...) needs a `ref`, either on its own leaf or on an NP whose only word it is, unless it is an expletive (`it` in "it rained"), which gets role `expl`.
5. Give QUOTE nodes a `spk` when the speaker is known.
6. Add one or more topics for what the passage is about and tag each sentence root with one.

## Example

Passage: `When she finally walked in, Kiran didn't look at him.`

{"entities":[{"id":"kiran","name":"Kiran","kind":"person","pron":"she"},{"id":"m","name":"the man","kind":"person","pron":"he"}],"topics":[{"id":"t1","label":"Kiran arrives","entities":["kiran"]}],"nodes":[{"id":"n1","c":"S","r":"root","topic":"t1"},{"id":"n2","c":"SBAR","r":"advcl","in":"n1"},{"id":"n3","c":"S","r":"head","in":"n2"},{"id":"n4","c":"NP","r":"nsubj","ref":"kiran","in":"n3"},{"id":"n5","c":"VP","r":"head","in":"n3"},{"id":"n6","c":"VP","r":"head","in":"n1"},{"id":"n7","c":"PP","r":"obl","in":"n6"}],"words":[{"w":"When","p":"SCONJ","r":"mark","in":"n2"},{"w":"she","p":"PRON","r":"head","in":"n4"},{"w":"finally","p":"ADV","r":"advmod","in":"n5"},{"w":"walked","p":"VERB","r":"head","l":"walk","in":"n5"},{"w":"in","p":"ADV","r":"advmod","in":"n5"},{"w":",","p":"PUNCT","r":"punct","in":"n1"},{"w":"Kiran","p":"PROPN","r":"nsubj","ref":"kiran","in":"n1"},{"w":"didn't","p":"AUX","r":"aux","l":"do","in":"n6"},{"w":"look","p":"VERB","r":"head","in":"n6"},{"w":"at","p":"ADP","r":"case","in":"n7"},{"w":"him","p":"PRON","r":"head","ref":"m","in":"n7"},{"w":".","p":"PUNCT","r":"punct","in":"n1"}]}