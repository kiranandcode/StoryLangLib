# The deslop loop

How to annotate a text, certify it against the house rules, rewrite it and
certify the rewrite. Everything model-shaped (annotating, deciding word
classes, rewriting) is done by an interactive agent or a person; the checks
are deterministic. Run commands from the repository root.

## Layout

```
<dir>/source.md                       where the text came from
<dir>/original/paragraphs/NN.txt      one paragraph per file, verbatim (typos included)
<dir>/original/paragraphs/NN.sx       its annotation
<dir>/original/lexicon.local.json     the text's own word classes
<dir>/original/headings.json          section headings, kept out of the paragraphs
<dir>/rewrite/...                     the same for the rewrite, with the same NN
```

Headings, displayed code and maths stay out of the paragraphs; inline maths
as ASCII. `deslop add FILE|- "Title"` makes this layout under
`stories/private-deslop/` and prints the directory.

## 1. Annotate

The format is `eval/prompt.md`, written in the bracket notation of
`tools/house/sx.py` (its docstring has the syntax); `sx.py NN.sx` writes
`NN.json`. Check the tokens first with `.lake/build/bin/langlib tokenize
NN.txt`, and the annotation with `langlib check NN.txt NN.json`.

What the rules read, so annotate it faithfully:

- Every verb gets `VerbForm` (`{Fin,Pres}`, `{Fin,Past}`, `{Inf}`, `{Part}`,
  `{Ger}`). A passive is `be` as `AUX.aux` and the participle as
  `VERB.head{Part}` in the same node; an agent is a `PP` with `by`.
- Subjects are `nsubj` (clausal ones `csubj`) with `ref` to an entity. Entity
  kinds matter: `object` and `abstract` subjects of `animate` verbs are
  inanimate actors. People and organisations are `person` or `group`.
- Put `ref` on every NP that mentions a tracked entity, and only those. Do not
  add a ref to link sentences that do not share a referent.
- Relative clauses are `relcl` (`acl` for reduced ones), coordination is
  `COORD` with `conj` and `cc`, copulas `AUX.cop`, and what follows a dash or
  colon is a sibling with its role (`appos`, or a clause role).
- Annotate the text as written, the way a UD treebank would, before drafting
  any rewrite. When two analyses are defensible, take the one that lets a
  rule fire.

## 2. Word classes and certification

```
python3 tools/house/certify.py <dir>/original [--paper]
```

`tools/house/base-lexicon.json` supplies the closed classes (AI vocabulary,
intensifiers, throat-clearing, inflation, American spellings, connectives,
vague nouns). The report's audit lists the words the text has not decided;
give each an entry in `lexicon.local.json`: `{"cls": ["animate"]}` for a verb
only a person does, `{"cls": ["nominal"]}` for a noun with a verb behind it,
`{"cls": ["us"]}` for an American spelling, otherwise `{"reg": "neutral"}`.
Never drop a base class to make a rule pass; the report prints every override.
`--paper` adds the academic styles, which also need a register (`formal`,
`informal`, `technical`, `neutral`) for every content word.

## 3. Rewrite

Write `<dir>/rewrite/paragraphs/NN.txt` with the same NN.

- Keep every concrete fact, number, name and step of the argument, and the
  text's person and register.
- Drop significance asserted without a source and list what you dropped in
  `rewrite/notes.json` (`{"NN": {"dropped": why, "dropped_claims": [...]}}`).
  Add no facts. An actor you name must be the one the original implies.
- Fix every rule the report flags, then annotate the rewrite with the same
  conventions and certify it until the report says CERTIFIED. Use
  `contrasts.json` (`{"P:I": "what was put forward, where"}`) only for a
  not-X-but-Y that denies something the text itself put forward.

Then `python3 tools/house/compare.py <dir>/original <dir>/rewrite` prints the
before, the after, the rule table and the flagged sentences.

## 4. Arguments (optional)

`argument.json` holds `lore` and `terms` (a one-sentence gloss and a kind for
every claim: fact, evaluation, summary, definition, saying, promise);
`paragraphs/NN.argument.json` holds World/Argument moves (claim, cite,
example, infer with premises, hedge, promise, deny, define; `uses` names
earlier terms). `docs/deslop/apples` is the worked example. `langlib argument`
reads them; the deslop UI's sceptical-reader view and the Studio's Rules tab
show them.

## Worker mode

The deslop UI (`deslop`, http://localhost:8790) queues annotate, rewrite and
certify requests in the Studio's request log. Any interactive agent session
in this repository with the `studio` MCP server (`.mcp.json`) can serve them:

1. `await_request {"kind": "deslop"}`; call it again on timeout. The request
   gives `doc_dir`, `target` (annotate, rewrite or certify), `para` (NN, or
   empty for the whole document) and a note in `text`.
2. `reply` with status `working`.
3. Do steps 1–2 (annotate), 3 (rewrite) or 2 (certify) for that paragraph.
4. `reply` done with what changed and what was dropped. The server re-runs
   `certify.py` and refuses `done` while the paragraph is flagged.

Never run a headless model (`claude -p`) or call a model with an API key from
scripts; the model work is the interactive session's.
