# Linguistic encodings for langlib: a literature and tooling review

Scope: what existing annotation schemes, grammar formalisms and proof-assistant projects offer a Lean 4 library that (a) types English sentences and discourse, (b) is filled in by an LLM emitting JSON, and (c) is checked by `render(tree) == tokenize(text)`. Each section ends with a recommendation. The last section puts them together into one design.

---

## 1. Universal Dependencies: the tag inventory to adopt

[Universal Dependencies](https://universaldependencies.org/) (UD) is the de facto cross-lingual standard. It has four parts, and we should take all of them:

- **UPOS** has 17 closed tags: `ADJ ADP ADV AUX CCONJ DET INTJ NOUN NUM PART PRON PROPN PUNCT SCONJ SYM VERB X`. The set is small, stable, and LLMs have seen a lot of it.
- **Features** are attribute=value pairs such as `Number=Plur`, `Tense=Past`, `VerbForm=Part`, `PronType=Prs`, `Person=3`, `Poss=Yes` and `Reflex=Yes`. English uses a small subset of them.
- **Deprels** are 37 universal relations (`nsubj obj iobj obl advcl acl amod nmod det case mark cop aux conj cc parataxis vocative discourse dislocated reparandum flat fixed compound appos punct root …`) plus language subtypes after a colon (`nsubj:pass`, `obl:tmod`, `nmod:poss`, `acl:relcl`, `compound:prt`).
- **[CoNLL-U](https://universaldependencies.org/format.html)** is a 10-column tab format (ID FORM LEMMA UPOS XPOS FEATS HEAD DEPREL DEPS MISC). Two of its details matter a lot for us:
  - **Multiword tokens (MWTs).** A range line `1-2 don't` is followed by syntactic words `1 do` and `2 n't`. The surface token and the syntactic words are kept apart, so rendering uses the surface form and syntax uses the words. [UD English guidance](https://universaldependencies.org/en/) uses MWTs for `n't`, `'ll`, `'s`, `'re` and so on. [EWT added MWTs for clitics and contractions in v2.7/2.8](https://github.com/UniversalDependencies/UD_English-EWT) (see [issue #5](https://github.com/UniversalDependencies/UD_English-EWT/issues/5) and [docs #641](https://github.com/UniversalDependencies/docs/issues/641) on informal contractions).
  - **`SpaceAfter=No` in MISC.** This one flag is what lets UD rebuild the original text. CoNLL-U also allows `# text = …` sentence comments, and the [CorefUD](https://ufal.mff.cuni.cz/~popel/corefud-1.0/corefud-1.0-format.pdf) work shows that MISC can carry whole extra annotation layers.

The reference treebanks for our genre are [UD_English-EWT](https://github.com/UniversalDependencies/UD_English-EWT) (web text, about 250k words) and [GUM](https://gucorpling.org/gum/). GUM includes fiction, conversation and Reddit, and adds coreference, RST and bridging layers on the same tokens. That makes GUM the closest existing analogue to langlib as a whole.

**Recommendation.** Adopt UPOS and the universal deprels exactly, as Lean inductives. Represent subtypes as a typed field over a closed English set (`pass`, `tmod`, `poss`, `relcl`, `prt`, `npmod`, `agent`, …) with an `other : String` escape. Type the roughly dozen features English actually uses and keep the rest in a string map. Keep PTB `XPOS` as an optional string; it adds detail (VBD vs VBN) that we can derive from features anyway. Adopt the MWT split between token and word as a **core structural concept**, because it is exactly the boundary between "what renders" and "what syntax sees".

---

## 2. Constituency vs dependency vs GF vs CCG

**Penn Treebank constituency.** Phrase-structure trees (`(S (NP …) (VP …))`) are a natural fit for an inductive type, and rendering is just reading the leaves. The drawbacks are real, though. The PTB label set is English-specific and tied to a particular theory: empty elements, traces and function tags. Fragments and dialogue end up under `FRAG`/`X`/`INTJ` catch-alls. LLMs are also measurably worse at it: [Bai et al., "Constituency Parsing using LLMs"](https://arxiv.org/pdf/2310.19462) report that LLMs hallucinate content and produce unmatched brackets, especially on sentences over 40 tokens or with special tokens. Unsupervised GPT-4 with prompting tops out around 77 F1 in [related cross-domain work](https://aclanthology.org/2023.emnlp-main.508.pdf), well below supervised parsers at about 95.

**Dependency (UD).** The structure is flat: one head per word. It handles fragments gracefully, since a fragment is just a tree whose root is a noun or interjection. Dialogue has dedicated relations (`vocative`, `discourse`, `parataxis`, `reparandum`, `dislocated`). The CoNLL-U-style tabular format is also what LLMs produce best. [Matsuda, Ma & Asahara (SyntaxFest 2025)](https://arxiv.org/abs/2506.09983) show that step-by-step prompting (UPOS first, then head and deprel) with a simple tabular output reaches state-of-the-art UD accuracy across 17 languages "without hallucination". The main cost is that English UD trees are nearly always projective but not guaranteed to be. Extraposition and some quotation patterns break projectivity, so a tree type that forces in-order traversal will reject legitimate analyses.

**Grammatical Framework (GF).** GF ([Ranta](https://www.grammaticalframework.org/)) is conceptually *the* model for "a typed tree that pretty-prints to words". An abstract syntax is a typed signature (`fun PredVP : NP -> VP -> Cl`), and each concrete syntax is a compositional linearization to strings. The Resource Grammar Library (RGL) covers English morphology and syntax. GF trees can be [converted to UD (gf2ud)](https://aclanthology.org/W17-0247.pdf), and the [inverse ud2gf](https://aclanthology.org/2016.lilt-13.4/) also exists. Ranta's [Abstract Syntax as Interlingua](https://direct.mit.edu/coli/article/46/2/425/93370/Abstract-Syntax-as-Interlingua-Scaling-Up-the) explains how they scaled GF to robust pipelines precisely by routing through UD, because RGL grammars do not cover open-domain text. [GFLean](https://arxiv.org/pdf/2404.01234) bridges GF and Lean 4, but for controlled math language. The lesson: GF's *architecture* (typed abstract tree plus a separate, provably total linearization) is right. GF's *coverage* is not good enough for literary text, where unbalanced quotes, interrupted speech, typos and archaic forms would need constant fallbacks.

**CCG and categorial grammar.** CCGbank-style derivations give a tight syntax-semantics link, and Lambek and categorial types map neatly onto Lean types (see §5). They are, however, the most brittle option for messy text: every word needs exactly the right category, and a single wrong category breaks the derivation. LLM accuracy here is not well studied. Treat CCG as a possible later *semantic* view, not as the ingestion format.

**Recommendation.** Use **UD dependencies as the ingestion and storage format**, and borrow **GF's discipline** for rendering: render is a total function from the token layer, not from the syntax layer, so it can be proven correct once. Store syntax as a head-pointer table over word ids, with decidable well-formedness (one root, acyclic, every word has a head). Then offer a *derived* ordered-tree view (left dependents, head, right dependents) together with a lemma that, for projective trees, the in-order traversal equals the word sequence. Do not make projectivity part of the type.

---

## 3. Reference and coreference

**Entity-mention clusters.** OntoNotes, [CorefUD 1.x](https://aclanthology.org/2022.lrec-1.520.pdf) and [LitBank](https://github.com/dbamman/litbank) all use the same basic shape: mentions are token spans, and each mention points to an entity or cluster id. CorefUD stores this in MISC as bracketed `Entity=(e8-place-1)` annotations giving cluster id, entity type and head index, and it allows discontinuous mentions ([format spec](https://ufal.mff.cuni.cz/~popel/corefud-1.0/corefud-1.0-format.pdf)). LitBank is the most relevant for fiction ([Bamman et al.](https://arxiv.org/pdf/1912.01140)). It annotates **singletons**, separates **generic from specific** mentions, and handles **near-identity** and **revelation of identity** (the stranger who turns out to be the father). It also has a **quotation layer** that links each quote to speaker and addressee entities using the same ids as coreference. Speaker attribution is its own research thread ([PDNC](https://www.researchgate.net/publication/359917786_The_Project_Dialogism_Novel_Corpus_A_Dataset_for_Quotation_Attribution_in_Literary_Texts), [Vishnubhotla et al. 2023](https://arxiv.org/pdf/2307.03734)).

**Anaphora vs cataphora.** None of these schemes stores direction. A cluster is an unordered set of mentions, so whether a pronoun is anaphoric or cataphoric (*"When **she** arrived, **Mary** …"*) is *derived* from token order and from which mention is most informative. [Sequence Box Notation (SBN)](https://semanticsarchive.net/Archive/jQzMzJlY/compact.pdf) in the Parallel Meaning Bank does use **signed relative indices** (`-1`, `+2`) that point backwards or forwards to concepts. That works for linearized seq2seq output, but it is fragile under edits and hard for an LLM to count.

**Bridging.** Bridging is a separate, non-identity relation between mentions: *the house … **the door***. [ARRAU](https://www.researchgate.net/publication/220745830_Anaphoric_Annotation_in_the_ARRAU_Corpus) labels bridging pairs with semantic relations such as part-whole, set-member and attribute. [ISNotes/BASHI](https://arxiv.org/pdf/2506.07297) treat bridging as an information-status category. [GUMBridge](https://arxiv.org/html/2512.07134) (2025) is a recent multi-genre taxonomy. Agreement on bridging is low across the board.

**DRT / Parallel Meaning Bank.** [PMB DRSs](https://pmb.let.rug.nl/drs.php) give full scoped meaning (boxes, discourse referents, presupposition, negation) with WordNet senses and VerbNet roles. They are excellent as a *target* for story logic, but too heavy as an LLM output format. [Neural DRS parsing](https://direct.mit.edu/coli/article/51/1/235/124789/Neural-Semantic-Parsing-with-Extremely-Rich) needs dedicated models.

**AMR and UMR.** AMR is sentence-level, not anchored to tokens, and has no tense or coreference across sentences. Not anchoring to tokens is a dealbreaker for a round-trip check. LLMs are also poor at it: [GPT-4o reaches a maximum Smatch of about 60 few-shot](https://aclanthology.org/2025.jlcl-2.4/), and ["You Are An Expert Linguistic Annotator"](https://arxiv.org/pdf/2310.17793) needed manual repairs just to get scorable output. [UMR](https://github.com/umr4nlp/umr-guidelines/blob/master/guidelines.md) ([UMR 2.0 data](https://lindat.mff.cuni.cz/repository/items/version/285)) adds a **document-level graph**: coreference (`same-entity`, `subset-of`), **temporal dependencies** (events anchored to each other or to the document creation time with `before`/`after`/`overlap`/`contained`), and **modal dependencies** (who asserts what, and with what certainty). Its document-level design is the best existing template for our later story logic. Its sentence graphs are not.

**LLM coreference performance.** In the [CRAC 2025 shared task](https://arxiv.org/pdf/2509.17796) the best LLM system scored 62.96 against 75.84 for the traditional CorPipe system. Long-range context and ambiguous mentions are the known weak points ([IdentifyMe](https://aclanthology.org/2025.naacl-short.64.pdf), [BookCoref](https://aclanthology.org/2025.acl-long.1197.pdf)).

**Recommendation.** Use **LitBank/CorefUD-style clusters over token spans**:

- `Mention = {id, span : TokenSpan (contiguous, with an optional list for discontinuous ones), entity : EntityId, kind : Name | Nominal | Pronoun | Zero?, specificity : Specific | Generic}`.
- `Entity = {id, etype : PER|LOC|ORG|FAC|GPE|VEH|OBJ|TIME|EVENT|ABSTRACT, canonicalName?, topics : List TopicId}`.

Do **not** store anaphora or cataphora as a type. Compute it, and prove that the computation is total. Model bridging as a separate typed relation, `Bridge {anaphor : MentionId, anchor : MentionId, rel : PartWhole | SetMember | Attribute | Role | Other String}`, and keep it optional and low-confidence. Model quotes as LitBank does: `Quote {span, speaker? : EntityId, addressees : List EntityId}`.

---

## 4. Discourse structure

- **[RST](https://www.sfu.ca/rst/)** builds full trees over clause-like units (EDUs) with nucleus/satellite relations. GUM has RST in the [eRST](https://gucorpling.org/gum/) variant. Full RST trees are expensive, have low inter-annotator agreement at the higher levels, and force one global tree even where a narrative is not tree-shaped.
- **[PDTB-3](https://catalog.ldc.upenn.edu/docs/LDC2019T05/PDTB3-Annotation-Manual.pdf)** is shallow and anchored to the lexicon. Each relation is a connective (explicit tokens, or an implicit connective inserted by the annotator) with an Arg1 span, an Arg2 span, and a sense from a 3-level hierarchy: the top level is Temporal, Contingency, Comparison and Expansion, and Level 3 now encodes only directionality. No global tree is required. [Discourse Annotation in the PDTB: The Next Generation](https://aclanthology.org/W18-4710.pdf).
- **QUD (Questions Under Discussion)** treats each sentence as answering an implicit question anchored in earlier context. It is attractive for "topics", but LLM QUD parsing still violates the framework's constraints ([QUDeval](https://aclanthology.org/2023.emnlp-main.325/); [survey](https://arxiv.org/pdf/2502.15573)).
- **Information structure** (topic/focus, given/new) is mostly derivable from coreference (first mention means new) plus syntax (preposed or dislocated means topic). ISNotes shows that information status can be annotated as a mention attribute.

**Recommendation.** Make the discourse layer **PDTB-style**: `DRel {connective? : TokenSpan, arg1 arg2 : Span, sense : PdtbSense}`, with the sense hierarchy as an inductive type down to Level 2. Represent "topics" as a separate set of `Topic {id, label : String, members : List (EntityId ⊕ SpanId)}`, and keep QUDs as optional string-labelled nodes that point to an answer span. Skip RST until a concrete consumer needs it. Add `infoStatus : New | Old | Mediated` to mentions only if scene graphs need it. Most of it can be computed.

---

## 5. Formalizations in proof assistants

- **Lean 4.**
  - [linglib](https://github.com/hawkrobe/linglib) ([fork](https://github.com/patrl/linglib)) aims to be "mathlib for linguistics" across semantics, syntax and pragmatics. Its own README says it is mostly AI-written and needs review. It is useful for interop on semantic types, but it is not a corpus encoding.
  - [lean-nl-semantics](https://github.com/YOUSEFSAADELDIN/lean-nl-semantics) implements Modern Type Theory semantics (common nouns as types, à la Chatzikyriakidis and Luo) and mechanizes FraCaS, with a bridge to linglib.
  - Gordon's [Natural Language Specifications in Proof Assistants](https://arxiv.org/pdf/2205.07811) and [Trustworthy Formal NL Specifications](https://arxiv.org/html/2310.03885) implement an extensible categorial fragment of English *inside Lean*, with grammatical types as an inductive type and typeclass-driven interpretation.
  - [GFLean](https://arxiv.org/pdf/2404.01234) uses GF for autoformalization.
  - **Name clash:** [nielstron/langlib](https://github.com/nielstron/langlib) is already a Lean 4 package called `langlib` (formal language theory). Rename ours or namespace it carefully before publishing to Reservoir.
- **Coq.** Anoun and Castéran's Lambek calculus formalization (later [ported to HOL4](https://arxiv.org/abs/1705.07318)). The [GF + Coq FraCaS system](https://aclanthology.org/W17-6801.pdf) by Chatzikyriakidis and Luo maps GF trees to Coq propositions.
- **Agda.** [Dependently-typed Montague semantics in Agda-flat](https://www.semanticscholar.org/paper/Dependently-Typed-Montague-Semantics-in-the-Proof-Zwanziger/e719782ea8424fc52bee6385c1ef80adb0759a12). Kokke's [type-logical grammars in Agda](https://www.researchgate.net/publication/319478183_Formalising_Type-Logical_Grammars_in_Agda). A [nonassociative Lambek calculus in Agda](https://link.springer.com/chapter/10.1007/978-3-032-06085-3_23) (2025). Bekki's Dependent Type Semantics (DTS), which handles anaphora with dependent sums.

**Takeaway.** Every existing formalization targets *semantic theory* over hand-built fragments. None of them encodes *corpus annotation* of real text with a verified round trip. That gap is langlib's niche. DTS and DRT are the right future targets for anaphora semantics, since they resolve pronouns through context.

---

## 6. LLM parsing accuracy and failure modes

The findings so far:

- **Dependency parsing.** Naive prompting gives structurally invalid output. Tabular step-by-step prompting reaches UDPipe-level results, and fine-tuning reaches state of the art ([Matsuda et al. 2025](https://arxiv.org/abs/2506.09983); [LLM dependency parsing with symbolic rules](https://aclanthology.org/2025.xllm-1.17.pdf)).
- **Constituency parsing.** Hallucinated words, unmatched brackets, and degradation past about 40 tokens ([Bai et al.](https://arxiv.org/pdf/2310.19462)).
- **AMR.** Poor, and often ill-formed (see §3).
- **Coreference.** About 63 vs 76 CoNLL F1 against specialized systems, and weak on long range.

The failure modes that matter for our round-trip check:

1. **Silent normalization.** The model "fixes" the text: curly quotes become straight, `—` becomes `--`, `…` becomes `...`, `colour` becomes `color`, `gonna` becomes `going to`, typos and archaic spellings get corrected, `n't` turns into `not`.
2. **Dropping tokens.** The model skips repeated words, closing punctuation and quote marks, or stutters (`I—I don't`).
3. **Hallucinating tokens.** The model adds implied subjects, copulas or punctuation, especially in fragments.
4. **Index drift.** Head and token indices go off by one after an MWT, or after about 40 tokens.
5. **Re-segmentation.** The model merges or splits sentences, especially multi-sentence quotes.
6. **Omitted optional fields.** Under [strict structured-output modes](https://futureagi.com/blog/evaluating-llm-structured-output-modes-2026/), optional fields get dropped.

**Implication.** `render == tokenize` catches failures 1, 2, 3 and 5. It does **not** catch failure 4, a well-formed string with wrong structure. It is also too blunt as a diagnostic, because a mismatch tells the LLM nothing about *where* it went wrong. See the design below.

---

## 7. Tokenization conventions

- **PTB (classic).**
  - Splits clitics: `do n't`, `I 'm`, `John 's`.
  - Rewrites quotes to `` `` `` and `''` and brackets to `-LRB-`/`-RRB-`.
  - Keeps hyphenated words whole.
  - Splits `gonna` into `gon na` and `cannot` into `can not`.
  - The rewriting of quotes and brackets is **lossy**. Never adopt it.
- **OntoNotes/newer PTB and UD English (EWT, GUM).**
  - Clitics are split as syntactic words, with the surface MWT preserved since v2.7/2.8.
  - **Hyphens are split off as their own `PUNCT` token** (`long - term`) in EWT and GUM, and `SpaceAfter=No` marks that there is no whitespace around them.
  - Quotes keep their original characters.
  - Em-dashes and ellipses are their own `PUNCT` tokens.
  - URLs, emoticons and similar stay whole.
  - Possessive `'s` is a separate word (`PART`, `case`).
  - See [Where are we still split on tokenization?](https://aclanthology.org/2024.findings-eacl.9.pdf) for remaining disagreements between corpora.
- **Fiction-specific cases.** `'Tis`, `o'er`, `ma'am`, `'em`, dropped-g `goin'` (is the apostrophe part of the word?), `Mr.`/`Mrs.` (abbreviation periods stay attached), spaced vs unspaced em-dashes, `?!`, `—"` clusters, single quotes doubling as apostrophes (`'I can't,' he said`), and nested quotes.

**Recommendation.**

- Langlib owns a **deterministic tokenizer written in Lean**, defined as a function `String → Array Token` with byte offsets. It follows UD-EWT conventions with no character rewriting, and records whitespace as `spaceAfter : String` (the actual whitespace, not a Bool), so that newlines and paragraph breaks round-trip too.
- MWTs are a token-level split into words (`don't` becomes `do` + `n't`; `cannot` becomes `can` + `not`; `gonna` becomes `gon` + `na`). Tokenization stays fixed and the MWT split is chosen by syntax.
- Unicode NFC is applied once, at ingestion. Anything else is a faithfulness error.

---

## Recommended encoding for langlib

### Core principle: the LLM annotates; it does not transcribe

Tokenize in Lean **first**. Then give the LLM a numbered token table and have it return structure **over token ids**. Each leaf also repeats its `form`, as a checksum. Faithfulness then splits into three decidable checks, each with a precise error message:

1. **Coverage.** Every token id appears exactly once, in order: `words.map tokenOf = tokens`.
2. **Echo.** For every leaf, `form == tokens[id].surface`, which catches index drift (failure 4).
3. **Render.** `render doc = originalText`. This holds by construction once checks 1 and 2 pass, and should be a *theorem*, not just a test.

If the model is required to emit free text instead, keep `render(tree) == tokenize(text)` but diff the two at the token level and send the first divergent index back in the retry prompt.

### Layers

Each layer refers only to ids from the layers below it. All layers are flat, id-indexed arrays, both in JSON and in Lean. Do not use nested JSON trees: nesting is exactly where LLMs mismatch brackets.

```
Layer 0  Text      : original String (NFC), paragraph boundaries
Layer 1  Tokens    : Array {id, surface, start, stop, spaceAfter : String}
         Words     : Array {id, tokenId, form, isMwtPart}      -- don't → do, n't
         Sentences : Array {id, wordRange}                      -- typed partition proof
Layer 2  Syntax    : per word {upos : UPOS, lemma : String, feats : Feats,
                               head : Option WordId, deprel : Deprel}
Layer 3  Reference : Entities, Mentions (word spans), Bridges, Quotes(speaker, addressees)
Layer 4  Discourse : DRels (PDTB), Topics, optional QUDs
Layer 5  (later)   : Events + UMR-style temporal/modal doc graph; scene graph
```

### Typed vs stringly

| Typed (inductives / structures + invariants) | Stringly (with an `other` escape) |
|---|---|
| UPOS (17), universal deprels (37), English deprel subtypes | lemma, XPOS, rare features |
| Core features: Number, Person, Tense, Mood, VerbForm, PronType, Case, Degree, Poss, Reflex, Gender (pronouns) | entity `canonicalName`, topic labels, QUD text |
| Ids (`TokenId`, `WordId`, `EntityId`, …) as distinct structures, never bare `Nat` | lexical senses (WordNet / PropBank) if added |
| Span = `{start stop : WordId, h : start ≤ stop}`; mention kind; entity type | bridging `Other` relations |
| PDTB senses to Level 2; Quote structure | free-form notes / confidence |
| Well-formedness as decidable `Prop`s: single root per sentence, acyclic heads, spans in bounds, token coverage | |

Put invariants in `Decidable` predicates checked by a `validate : Doc → Except Error ValidDoc` function, not in dependent types inside the JSON-facing structures. Lean's `FromJson` derivation works on plain structures. The validated `ValidDoc` subtype then carries the proofs that downstream code (rendering, scene graphs) relies on.

### Pitfalls

- **Do not make projectivity, sentence-internal coreference, or "antecedent precedes pronoun" part of the types.** Fiction breaks all three: cataphora, extraposition, and dialogue that spans sentences.
- **Sentence segmentation in dialogue.** `"Stop," she said. "Now."` UD makes `said` the root, with the quote as `ccomp` or `parataxis`. Multi-sentence quotes cross sentence boundaries, so `Quote` must be a document-level span over words, not a syntax node.
- **MWT indexing.** Head indices refer to *words*, but the LLM sees *tokens*. Give the LLM the word table after the MWT split (`do`, `n't`) with the surface token shown alongside. Otherwise index drift is guaranteed.
- **Whitespace.** `spaceAfter : Bool` loses double spaces, tabs and newlines. Store the actual string.
- **Quote characters.** Typographic `'` is both an apostrophe and a closing single quote. The tokenizer needs a rule for this (an apostrophe between letters is word-internal). LLMs will disagree with it, and the echo check will surface that.
- **Long inputs.** Chunk at paragraph level, about 40 to 60 words per call for syntax. Do coreference in a separate pass over the whole chapter, with the entity table carried forward between passes, since LLM coreference degrades with distance.
- **Over-ambitious semantics.** AMR/DRS output from LLMs is unreliable. Derive semantics *from* the validated UD and reference layers in Lean (the ud2gf / UD→DRS route, cf. [ud-boxer](https://github.com/WPoelman/ud-boxer)) instead of asking the LLM for it directly.
- **Packaging.** Rename to avoid the existing [`langlib`](https://github.com/nielstron/langlib) Lean package, and consider a bridge to [linglib](https://github.com/hawkrobe/linglib) for semantic types.
