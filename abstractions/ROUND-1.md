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
