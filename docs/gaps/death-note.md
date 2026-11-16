# Gaps: a Death Note arc (Light against L)

Work in progress. What exists, what the checker caught, and what is open.

## Done

* `LangLib/World/DeathNote.lean`: the note as a power system whose
  preconditions are knowledge. Faces seen and names heard per character; a
  write is an act (alive, holds a page, has heard that name for that person)
  whose effect is decided when written and frozen with its reason (`Refusal`):
  no face, a fake name (naming the homonym, who is unaffected), already dead,
  already written. Cause within 40 s, details within 6 min 40 s, actions within
  23 days, a cause impossible for the victim or one that would kill another is
  refused (heart attack instead), an action the victim could not do or that
  would kill another is refused. Pages, touching, seeing the shinigami, the eye
  deal (half the remaining life). `takeChecks` lists the checks for views.
* `LangLib/World/Mystery.lean`: fair play for any story with minds. `clue`,
  `conclude` (allowed only if derivable by the story's `Deduction` rules from
  what the detective holds now), `suspect` (a credence, needs a lead),
  `reveal` (the reader must be able to derive it from what the page showed).
  `valid_fair`: a valid story is fair play (for any event type with
  `MysteryEvents`).
* `LangLib/World/Examples/DeathNoteArc.lean`: the arc as 36 paragraphs of
  moves (`p01`..`p36`, from the first killings to the To-Oh ceremony), the note
  half by a proved projection (`run_proj`, `valid_proj`), `arc_valid` (whole
  arc, minds included, about 7 s of kernel time: no checkpoints needed), and the
  counterfactuals: writing "L", "Hideki Ryuga" (the idol's name: neither dies),
  "Ryuzaki" (never heard), no face yet after L's broadcast, the FBI plan without
  the badge, Naomi without her ID, a stand-in shown as "L" (the trap needs a real
  name), `writing_cannot_test_a_name`, old age for Naomi, the bus driven off the
  road, a train crash, Raye drawing L, the two windows, Ryuk unseen by Soichiro,
  the eye deal (would end it; only the owner).

## What the checker caught while building

* An action refused for harming others left the victim to die when the cause's
  window closed, so the refusal surfaced as "is dead" on the next act; `act` now
  reports the refusal itself (`Refusal.refused`).
* The arc first had Naomi meet Light the same second Raye died (no time passed
  between paragraphs 22 and 26).

## Open (next steps)

1. Minds theorems (`DeathNoteMinds.lean`): `MysteryEvents` instance for `E` and
   `fairB start arc = true` from `valid_fair`; per-inference derivations (which
   rule, at which move) for L, Naomi and Light; credences (`needsName` 80,
   `kira light` 5); false beliefs (Light: the man on air is L; Raye: the pages
   are ordinary, he will live; Naomi: Light helps L); dramatic irony (the reader
   holds `kira light`, Soichiro the opposite); Light's plant (not a student)
   fails and shows the leak; counterfactual conclusions (region without the
   Kanto-only clue, student before the hours, Light is Kira: "suspect still
   needs noOtherSuspect"; the unfair reveal). All were checked by `#eval`, not
   yet stated.
2. `#guard_msgs` pins for each counterfactual's reason (the messages are in
   this session's notes: see the `firstFailure` output in the commit message).
3. L's briefing (paragraph 7) as an `Argument` (Coherent).
4. Power export (`studio/power-schema.md`): a generator over `arc` emitting
   moves with checks (the act's checks, plus the write's `takeChecks` as an
   outcome), clocks per entry (40 s, 6:40 windows from `Entry`), knowledge
   (faces, names), credences over time, counterfactuals; one line in the
   `langlib power` registry in Main.lean.
5. The story: `stories/death-note/` (story.json, beats, plans, then prose and
   annotation paragraph by paragraph with `studio/workflows.py`), each
   `events.json` listing its moves under `"deathnote"`, tied by `#guard`.

## Gaps in the model

* Groups as one character (the FBI agents, each group of criminals): one write
  stands for many names.
* Indirect killing is allowed: Raye, controlled, writes the agents' names; the
  "kills another" rule looks only at the direct harm of a cause or an action.
* "No way to test a name" is proved for the act of writing only
  (`writing_cannot_test_a_name`); the eye deal is the one way the module offers.
* Regions are lists of places; a broadcast reaches whoever is at one of them.
