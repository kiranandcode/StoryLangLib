<h1 align="center">StoryLangLib: Checking Stories in Lean</h1>

Idea: let an LLM write the prose, and let Lean check that the text says what
the model claims it says and that the story it tells has no plot holes.

StoryLangLib is a Lean 4 library in two halves. The first half encodes
English text as typed trees (Universal Dependencies parts of speech, phrase
structure, entity references) whose leaves must render back to exactly the
tokens of the source, so an LLM's annotation of a passage can be checked
rather than trusted. The second half reads events off those trees into a
modular story world (places, minds, relationships, a magic system, whatever
the story needs) where validity is decidable: who knows what, who could be
where, whether an action is in character, whether there was consent, and
whether the timeline the text describes is consistent.

<p align="center"><img width="95%" src="viz/out/8b-bridge-compact.png" alt="text to tree to events to scene facts to a defeasible derivation" /></p>

A passage, its checked annotation, the events read off it, the scene facts
they produce, and the derivation that Kiran's shout is in character. Every
dashed line is a step the code performs.

## Example

An LLM encodes a passage as a langlib document; `langlib check` accepts it
only if its leaves are the source's tokens and its references resolve:

```
$ langlib check examples/cata.txt bad.json
 "edits":
 ["token 2 \"finally\" is missing (near: When she finally walked in ,)",
  "token 10 \"him\" was written as \"her\" (near: Kiran didn't look at him . \" Sit)"],
 "refIssues":
 ["pronoun \"her\" (token 9) refers to \"theo\", whose pronouns are he"],
```

Story worlds are assembled from modules, and stories about them are theorems:

```lean
inductive E | space (x : SpaceEv Ch Pl Ob) | mind (x : MindEv Ch Fact) | social (x : SocialEv Ch)
  deriving DecidableEq, Repr, StoryEvent   -- Inject, Domain, Observable, Purpose, by dispatch

def told : List E :=
  [ so (.confide theo kiran), so (.flirt theo kiran), so (.flirt kiran theo),
    sp (.take mara letter),                                 -- meanwhile, in the office
    so (.ask theo kiran .kiss), so (.agree kiran theo .kiss),
    so (.agree theo kiran .kiss), so (.act kiran theo .kiss),
    sp (.drop theo letter), sp (.move theo roof) ]      -- flashback

theorem story_valid : story.Valid start := by decide +kernel
theorem theo_false_belief :
    falseBelief ends theo (fact (.objAt letter office)) = true := by decide +kernel
theorem kiss_needs_consent : ¬ Valid start noConsent := by decide +kernel
```

When a step fails, the checker says why, in terms a writer (or the model) can
act on:

```
out of character (shy people hold back); to justify it, first establish:
attraction draws them on or the confident make the first move
```

From text to theorem: `examples/office.txt` was annotated by Opus, accepted by
`langlib check`, read by the space and relationship lexicons into the office
story (flashback "an hour earlier", a "meanwhile"), timed by the solver, and
proved valid (`LangLib/World/Examples/OfficeText.lean`).

## Studio

StoryLangLib Studio is a local app for writing a story with an LLM where every
paragraph is checked against the story's model, and the reader can see that
model (`docs/ui-spec.md`; design notes in `docs/ui-reading.md` and
`docs/ui-visualisation.md`).

```
studio/run.sh                     # the Electron app, plus http://localhost:5177 in any browser
studio/run.sh --browser           # no Electron window
```

In development the window loads the Vite dev server, so the renderer hot
reloads; `studio/web/electron/dev.cjs` restarts the main process when
`electron/*.cjs` changes. Closing the window, Cmd+Q or a TERM to `run.sh`
stops the API and Vite, and the API's shutdown kills every Lean and langlib
process group it started.

The left panel is the prose (chill: just the text; overview: entity mentions,
quotes, events, time words and warnings layered on without reflowing it). The
right panel threads the logic paragraph by paragraph: a storyline of where
everyone is, then for each paragraph its events and verdicts, belief changes
with their explanations, bonds and consent, goals, claims, plan realisation,
time, and whether its Lean theorems are proved. Both follow the files under
`stories/<name>/` as they change.

A story is data: `story.json` (cast with personas, places, objects, facts,
lore, plans, opening state, beats, outline) and `paragraphs/NN.{txt,json,events.json,plan.json}`.
The Lean side is the judge:

```
langlib story <dir>                    per-paragraph report (JSON) the Studio renders
langlib story-lean <dir> <namespace>   the story as a Lean file of theorems (Proofs.lean)
```

`LangLib/Studio` builds one world from a `Spec` with the same modules as the
examples, so the CLI's verdicts and the `decide +kernel` proofs in
`Proofs.lean` run the same definitions; `Refine.lean` adds refinement between
layers (`Refines abs fine coarse := fine.filterMap abs = coarse`, with
`Refines.trans`) and a beat layer with STRIPS-style preconditions.
The writing itself happens in an interactive Claude session (or subagents
Kiran can watch), never a headless model call. That session writes the prose,
the annotation and the event reading, and drives `studio/workflows.py`, a
checking CLI that makes no model calls:

```
python3 studio/workflows.py brief           stories/roof 3   what the writer needs for paragraph 3
python3 studio/workflows.py tokens          stories/roof 3   the leaves the annotation must have
python3 studio/workflows.py extract         stories/roof 3   event language, world and rules for its reading
python3 studio/workflows.py paragraph-check stories/roof 3   annotation, events, claims, plan: exit 1 with the why
python3 studio/workflows.py plan-check      stories/roof     beats and paragraph plans (top-down)
python3 studio/workflows.py refine-check    stories/roof     the paragraphs refine the beat story (so far)
python3 studio/workflows.py prove           stories/roof     Proofs.lean regenerated and checked (via the Studio if running)
```

Kiran asks for changes from the Studio itself: **Request** in the top bar
(or `r`, or ✎ in a paragraph's margin; selected prose is quoted) files a
change to the story or to the tool in `studio/requests.jsonl`. An agent
listens through the repo's MCP server `studio` (`studio/studio_mcp.py`,
registered in `.mcp.json`): `await_request` blocks until a request arrives,
sending a progress ping every 15 s so the call outlives the client's tool
timeout; the agent does the work, then `reply` marks it working, done or
declined, and the Requests tab shows the reply. The server calls no model;
it hands Kiran's words to whichever interactive session is listening.

`--log incremental` appends each verdict to `runs/incremental.jsonl` for the
Studio's run panel; `summary` and `compare` total them. Every child the Studio
or the CLI starts (langlib, lake, lean) runs in its own process group under
`nice -n 10` with a timeout and is killed on cancellation, reload and
shutdown; one Lean job runs at a time across both (`studio/procs.py`).

## Building

The project is a plain Lake package:

```
lake build
```

This checks every theorem in the examples. The command-line tool ends up in
`.lake/build/bin/langlib`:

```
langlib tokenize <text>             print tokens
langlib check <text> <doc.json>     check an encoding against its text
langlib render <doc.json>           print the text a document renders to
langlib pretty <doc.json>           print bracketed trees
```

## Evaluation

`eval/` asks models to encode 20 passages (Austen, Melville, Doyle, Twain,
Stoker, Dickinson, Shelley, Fitzgerald, and four from kirancodes.me), feeding
the checker's report back for up to three rounds:

```
cd eval
python3 build_corpus.py
python3 run_eval.py --models haiku,sonnet,opus,fable --jobs 12
python3 analyze.py
```

| model  | right first time | right within 3 tries |
|:-------|:-----------------|:---------------------|
| Opus   | 90%              | 100%                 |
| Fable  | 90% (95% flat)   | 100%                 |
| Sonnet | 80% (95% flat)   | 100%                 |
| Haiku  | 35%              | 55%                  |

Full results, including tree agreement between models and a reference check
with TypeSafe's Jev, are in `docs/eval-results.md`.

## Project structure
```
.
|-- LangLib
|   |-- Basic.lean, Token.lean, Render.lean, Json.lean, Diff.lean, Refs.lean, Check.lean
|   |-- Story
|   |   |-- DL.lean
|   |   |-- Bridge.lean
|   |   `-- Scene.lean, GateScene.lean, GateText.lean
|   `-- World
|       |-- Time.lean, Domain.lean, Persona.lean
|       |-- Space.lean, Mind.lean, Social.lean, Magic.lean
|       |-- Lexicon.lean
|       `-- Examples        Office, OfficeText, Gossip, Mage, Date
|-- Main.lean
|-- examples
|-- eval
|-- viz
`-- docs
```

| Path                  | Description                                                                 |
|-----------------------|-----------------------------------------------------------------------------|
| LangLib/Basic.lean    | Words, phrases, entities, topics: the typed encoding of a text              |
| LangLib/Token.lean    | The tokenizer both the source and every leaf are cut by                     |
| LangLib/Check.lean    | The faithfulness check: token diff, bad leaves, reference issues            |
| LangLib/Refs.lean     | Mentions, pronoun agreement, anaphora and cataphora                         |
| LangLib/Story/DL.lean | Defeasible logic as inductive relations, coherence, checked certificates    |
| LangLib/Story/Bridge  | Clauses (verb, subject, object, obliques) read off a checked document       |
| LangLib/Story/Scene*  | The first, single-file scene model (the gate scene), kept as a worked case  |
| LangLib/World/Time    | Allen interval relations, durations, an untrusted solver, timelines as consistency certificates |
| LangLib/World/Domain  | Composable story semantics: `Domain`, `Valid`, three-valued `ok3` and `Plausible` under listed assumptions, stories told out of order |
| LangLib/World/Persona | Traits, ranked values, and in-character checks via defeasible logic         |
| LangLib/World/Space   | Places, objects, possession, what each event lets witnesses see             |
| LangLib/World/Mind    | Evidence bases (seen, sensed, inferred, told, rumour, ...), trust- and persona-dependent upgrades (hard, radical, conservative, note), views as the greedy consistent prefix (consistent by theorem), lore, factive `realise` |
| LangLib/World/Social  | Trust, attraction, affection, tension; consent as a hard precondition       |
| LangLib/World/Magic   | An example story-specific module: spells and mana                           |
| LangLib/World/Dialogue | Questions under discussion, answers, hints (implicature), sarcasm read by rapport, promises (kept/broken), requests |
| LangLib/World/Goals   | Goals, plans, `Purpose` of each action; `motives` explains every action or flags it unmotivated; `planWorks` |
| LangLib/World/Derive  | `deriving StoryEvent` / `deriving StoryFact`: one `Inject` per constructor and composite instances by dispatch (no overlapping instances, small instance terms) |
| LangLib/World/Lexicon | Verb lexicons per module (incl. evidential and dialogue verbs); adverbials ("meanwhile", "an hour earlier") to time constraints |
| eval                  | Corpus, model runner, analysis, Jev reference check                         |
| viz                   | Scripts for the figures in `viz/out`                                        |
| docs                  | Literature reviews (linguistic encoding, story logic) and results           |

## Requirements

| Package        | Version  | Notes                                       |
|:---------------|:---------|:--------------------------------------------|
| Lean           | 4.35.0   | via `lean-toolchain`; no Mathlib needed     |
| Python         | ≥ 3.10   | only for `eval` and `viz`                   |
| claude CLI     |          | `eval/run_eval.py` calls models through it  |
| graphviz       |          | `viz` figures                               |
| matplotlib     |          | `viz` figures                               |
| JEV_API_KEY    |          | optional, `eval/jev_coref.py`               |

## Status

Work in progress. Open next: lexicon coverage beyond the example verbs,
character rules for more actions, and a loop that sends checker failures back
to the writing model.
