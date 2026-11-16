# Abstraction round 1: kernel time of a story's proofs

## Context

`langlib story-lean` writes a story's verdicts as theorems proved by
`decide +kernel`. Two changes already landed (not abstractions in the
skill's sense; they removed waste):

* the Studio world is first-order data (`W s` tables, not `upd` chains);
* checkpoints (`Snap.lean`): each paragraph is proved from a literal state
  `c(k-1)`, chained to the story's start by `Valid.chain`/`run_chain`.

roof (9 paragraphs) went from 61 s to 37 s. On a 43-paragraph chapter the file
still runs past the 600 s budget (a full run was reaped for memory at ~30 CPU
minutes): one event step from a checkpoint costs tens of seconds of kernel
time. The census below is per theorem kind, one late paragraph, each theorem
checked alone (`abstractions/census.py`).

## 1. Census

Paragraph 33 of the 43-paragraph chapter (2 events), each theorem alone, seconds
inside the Lean lock (`census.py`; an earlier run timed wall clock and so
included waiting behind other agents' jobs: discarded).

| theorem | what it forces | s (lore) | s (no lore) |
|---|---|---|---|
| baseline (header + literals) | nothing | 5.2 | 5.0 |
| `p33_here` (`Valid c32 chunk33`) | each event's `ok` only | 5.4 | 5.5 |
| `p33_step` (`run c32 chunk33 = c33`) | the whole final state | 45.3 | 6.0 |

`setting`, `perceived` and `complete` also force final states and cost the same
as `step` in the (wall-clock) run. langlib-1a's census of sweet-girl (no lore),
in-lock: about 2 s of kernel time per event; unfoldings dominated by
`Bool.rec`, `List.rec`, `List.any`, `clash`, `stale`, `insertBy`: the
consistency scans inside `view`, run at every witnessed learn (the liar check in
`learnWith` builds the witness's view).

**Finding.** With lore, a view costs about forty times as much: `view`'s lore
branch rebuilds `viewAt w c t` (a full admit and closure) for every distinct
story time in the base, to find conclusions settled earlier. String interning
(L1, landed by langlib-1a as `511f973`) did not change the step time.

## 2. Laws

Stated over the existing terms (`LangLib/World/Mind.lean`, `Studio/World.lean`):

* **L1, explanation is inert.** `Held.reasons` (strings) never affects `ok`,
  `step`, `view` or any verdict; only `learnWith`'s liar check reads it, through
  `Held`'s derived equality. For all states `w, w'` that differ only in
  `reasons`: same `ok3`, and `step` keeps them differing only in `reasons`.
* **L2, nested beliefs are inert for views.** `view w c` depends only on the
  first-order, non-noted items of `beliefs w c` (`adoptable`); nested
  `.bel` items (most of a base: each witness learns that every other witness
  saw it) only feed `viewOf`.
* **L3, a view changes only where its base does (frame).** `view (next w e) c =
  view w c` unless `e` adds an adoptable item to `c`'s base. Views are therefore
  a function of the base that can be carried in the state and reused across
  queries, and written into the checkpoint literal.
* **L4, a consistent addition extends the view.** If an appended item's literal
  clashes with nothing in `view w c` and makes nothing stale, the new view is
  the old one plus that literal (as sets; `contains` is all callers use).

* **L5, the past is frozen (time monotonicity).** Items enter a base stamped
  `about := Clock.now w`, and the clock only grows; so for `t < now`,
  `viewAt w c t` never changes again. Hence the conclusions settled at past
  times can be accumulated (each learn adds at most the heads in the view at
  the newest time) instead of recomputed from the whole history at every
  view. Known theory: incremental (materialised) view maintenance in
  databases; semi-naive evaluation in Datalog; append-only temporal tables.
* **L6, conclusions only come from rule heads.** `settled ⊆` heads of lore
  rules that are permanent, not already believed, and still supported; if no
  rule head qualifies, `settled = []` and the view is the plain admit, whatever
  the history (exact, cheap to decide).

## Measured falsifier

Same paragraph, the story's lore deleted (scratch copy): `p33_step` 45.3 s →
6.0 s. The lore branch of `view` is the cost; L5/L6 target it.

## 3. What was tried (the meet: rules over the existing terms, no new datatype)

Measured on paragraph 33, seconds inside the Lean lock, baseline about 5 s.

| change | `p33_step` | the paragraph's forcing checks |
|---|---|---|
| checkpoints + data world (incumbent) | 45.3 | ~4 × 45 (step, setting, perceived, complete) |
| L1, reasons as codes (langlib-1a, `511f973`) | 45.3 → no change | — |
| L6, settled only when a rule head qualifies (`243adaf`) | 30.7 | ~4 × 30 |
| per-paragraph bundle: the checks as one conjunction | — | 35.3 together |

* L1 is still worth having (it removed strings from states) but was not the cost.
* L6 is exact (`settledAt_guard`, `view_eq_viewSpec` re-proved) and saved a third
  of a step: the witness with no qualifying rule head (Robin) no longer builds
  per-time views; the one with two (Remy) still does.
* Bundling a paragraph's checks into one declaration lets the kernel run the
  paragraph's events once (whnf is shared within a declaration, never across):
  about 3× on the forcing checks. A check whose native verdict is false stays a
  theorem of its own, so a failure still names itself.

## 4. Next: L5 (needs a decision)

What remains in a step is the per-time views for characters with a qualifying
rule head. L5 removes them: since the past is frozen, carry each character's
settled conclusions as a table in the state, extended at each learn by the heads
in the view at the newest time, and written into the checkpoint literal. It
changes `HasMinds` (shared with the Fight world and its generated snapshots), so
it goes to Kiran with these numbers first.

## L5 adopted: the past is frozen, so conclusions are recorded, not recomputed

`HasMinds.settled`/`setSettled` (default: no record) hold each character's
permanent rule conclusions; perception appends the new ones at the end of each
event whose base changed (compared by content: a revision can keep the count),
and `view` reads the record instead of rebuilding every past view. The record
lives in `HasMinds` because `view` already takes it: as a separate class it was
resolved to its no-record default where `view` is defined, so the Studio's
record would never have been read. `view_eq_viewSpec` is proved for worlds
without a record; with one, equality is checked on the corpus.

Checked: every story's `langlib story` report is byte-identical with the
Studio's record on and off (hxh, roof, roof-posthoc, roof-topdown,
roof-pratchett, both AO3 chapters).

| story | report, record off | record on | proofs |
|---|---|---|---|
| boyremoval (lore) | 67.9 s | 17.9 s | 349/349 in 208.5 s (did not finish before) |
| sweet-girl (no lore: the plain path) | 6.2 s | 6.5 s | 831/831 in 347 s (334 s before; unaffected) |
| roof | 0.12 s | 0.18 s | 94/94 in 8.3 s |
| hxh | 1.0 s | 1.0 s | 66/66 in 5.4 s |
