# StoryLangLib Studio: spec

A local app for writing stories with an LLM where every paragraph is checked
against the story's formal model (langlib), and the reader can see that model.

## UI

Two panels.

**Left: the text.** Optimised for long-form reading.
- Serif body font, comfortable measure (research the reading-typography
  literature: line length, leading, font size, contrast, paragraph spacing,
  hyphenation, justification vs ragged right; cite what you follow in
  `docs/ui-reading.md`).
- Dark mode and light mode, togglable, remembered; calm palette, no visual noise.
- "Chill" mode: just the prose.
- "Overview" toggle: the same prose with annotations layered on, drawn from the
  langlib document of each paragraph: parts of speech (subtle), entity
  mentions (colour per character, forward/backward references), quotes and
  speakers, events read off each clause, time words, beliefs changed, warnings
  (unmotivated actions, assumptions, out-of-character moves, knowledge leaks).
  Annotations must not wreck the reading layout: use underlines, margin marks,
  hover cards, not inline clutter.

**Right: the logic, threaded per paragraph.** Scrolls in sync with the left.
For each paragraph: the events it asserts, the scene state that changed, who
believes what (and why: `explain`), relationships and consent, goals/plans
advanced, time (Allen relations, the solved timeline), and the verdict
(valid / plausible under assumptions / failing, with `why`). Research how to
visualise this well (narrative visualisation: storyline charts (Tanahashi &
Ma), XKCD-style movie narrative charts, story curves; belief/epistemic state
diagrams; argument maps and proof trees; timelines); write
`docs/ui-visualisation.md`, then pick a design. The thread between paragraphs
should make state change over the story visible (e.g. a storyline per
character, belief deltas per paragraph).

Live reload for development; the app also updates live when the story files on
disk change (the agent writes, the UI follows).

## Workflows

All three end in the same artefacts per paragraph: text, checked langlib
document, extracted events/constraints, the world state after it, and a
verdict with Lean proofs where they apply.

1. **Top-down (refinement).** The agent writes the plot as beats (a coarse
   story over a beat vocabulary), checks it; breaks each beat into paragraph
   plans (events), checks them; then writes each paragraph's prose and checks
   the prose realises its plan (re-extract and compare). Between consecutive
   layers, prove refinement: the finer story, abstracted to the coarser
   vocabulary, is the coarser story, and validity is preserved. Add the
   refinement relation to Lean (e.g. `Refines (abs : Fine → Option Coarse)
   fine coarse := fine.filterMap abs = coarse` plus validity of both).
2. **Incremental.** The agent writes paragraph by paragraph; after each one it
   annotates, extracts, extends the story, and checks it against the model so
   far; the model only grows (later paragraphs refine earlier facts:
   unknowns become known, consistent with the assumptions made).
3. **Post hoc.** The agent writes the whole story, then goes paragraph by
   paragraph: parts-of-speech tree, then scene events, then higher-level facts
   (beliefs, relationships, goals), then the implications between layers.

Compare the three on the candidate story: failures caught, rewrites needed,
time, model calls.

## Candidate story (for building and testing)

Adult, consensual, self-insert: Kiran (the user) and Theo, plus Mara.
Seed: Kiran works late in a lab; Theo, a visiting engineer, keeps finding
excuses to stay; a message meant for Kiran is read by Mara first (a false
belief and some gossip); the tension resolves on the roof, with consent
negotiated explicitly. Beats, personas (traits, ranked values, trust and
attraction) and the module set (space, minds, relationships with consent,
dialogue, goals) are the agent's to propose; keep the story file under
`stories/<name>/` (beats, paragraphs, langlib JSON, Lean world file).
How explicit the prose gets is the user's call; the structure (beats, events,
consent) does not depend on it.

## Architecture (suggested, not binding)

- Backend: Python (FastAPI or similar, with reload) calling the `langlib` CLI
  and `lake env lean` for checks and proofs; add CLI subcommands to Main.lean
  as needed (e.g. `langlib story <dir>` emitting per-paragraph JSON: events,
  states, beliefs, verdicts). The Lean side stays the source of truth.
- Frontend: Vite + TypeScript (React or Svelte), hot module reload; file
  watching pushes updates (SSE or websocket).
- Story store: plain files under `stories/`, git-friendly.
- Model calls: none from the app or its scripts. The writer is an interactive
  Claude session (or subagents/termlings Kiran can see) that drives the
  checking CLI `studio/workflows.py`; the checker does not care which model
  wrote the prose.

## Done when

The app runs with one command, shows the candidate story in both panels with
dark mode and overview, updates live as files change, and workflow 2 runs end
to end on at least a few paragraphs with checks visible in the right panel.
Then workflows 1 and 3.
