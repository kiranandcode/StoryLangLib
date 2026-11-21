# Abstraction round 2: a verified fast engine for the reasoning logics

Goal (Kiran, 2026-11-20): make a story's proofs fast, not only its report.
Revised design (same day): no untrusted solver plus checker. Each fast
algorithm is a Lean function proved equal to its specification, and the
generated proofs run the fast function inside the kernel (`decide +kernel`).
Compiled speed may come from `@[csimp]` lemmas (proved equalities), never from a
bare `@[implemented_by]` and never from `native_decide`.

All timings are CPU (user) seconds of one `lake env lean` or `langlib` process,
inside the shared Lean lock (`studio/procs.py`), on a loaded machine (load
average 20–35 from other agents). Wall time is not comparable.

## 1. Census

### 1.1 What the checker and the proofs compute

Every judgement, by algorithm class (survey of `LangLib/World`, `Story/DL`,
`Studio/Complete`, `Studio/Load`):

| class | judgements | how computed today |
|---|---|---|
| state machine over a run | `Valid`/`validB`, `Plausible`, `ok3` of every module (space, minds, social, dialogue, goals, consent, care, ties, affect, identity, conviction, Nen, Death Note, Mystery's `fairB`), `run`, `atStep`, `Was`/`Throughout`, `Timed.stateAt` | structural recursion over the event list; one `next` per event |
| linear base revision + monotone closure | `Mind.view`, `viewAt`, `viewOf`, `viewAsOf`, `admit`, `closure`, `stale`, `lits` | greedy consistent prefix (`admit`, O(n²) clash checks, O(n³) with lore), insertion sort, closure by `|rules|+1` naive passes |
| Datalog-like closure | `Mind.closure`, `Mystery.deriveFrom`, `DL.strictClosure`, `Rules.subRules`/`reached` | naive passes with fuel; `subRules` unmemoised (exponential on shared DAGs) |
| defeasible logic with priorities | `DL.certify` + `Cert.check`, `Persona.inCharacter`/`motivated`, `Social.socialOk3` (flirt, agree) | untrusted `certify` then `check`, both run by the kernel (`inCharacter := check (certify T) && …`) |
| argumentation | `Rules.grounded`, `labels`, `scepticLabels` | `|nodes|+1` Jacobi rounds, O(N²·A) |
| difference constraints | `Time.solve` (`@[implemented_by solveFast]`, no theorem), `Timeline.Satisfies` | the solver runs only at generation time; the kernel checks the timeline literal |
| plain lookups | settings, perception, completeness (`completeOk`), claims | list scans; `completeOk` also replays prefixes for counterfactual causes |

The kernel never runs the STP solver or `argumentGraph`; it runs views, closure,
the event steps, DL certificates (social events), the setting, perception and
completeness checks.

### 1.2 Where the time goes

Baseline: HEAD `31d6d61`, every story's `Proofs.lean` regenerated (identical to
the committed ones) and checked alone.

| story | theorems | report (s) | kernel file (s) | max RSS |
|---|---|---|---|---|
| private-ao3-sweet-girl | 831 | 14.4 | 581 | 2.3 GB |
| private-ao3-boyremoval | 349 | 36.8 | 356 | 5.0 GB |
| private-fixpoint | 273 | 0.8 | 333 | 1.3 GB |
| essay-bloomfilters | 469 | 3.2 | 80 | 1.0 GB |
| essay-end-of-pl | 197 | 3.7 | 84 | 1.3 GB |
| private-roof-ran | 149 | 2.7 | 50 | 1.4 GB |
| private-fixpoint-v1c01…v2c10 (10 chapters) | 121–127 each | 0.3 each | 16–31 each | 0.8–1.0 GB |
| roof / roof-pratchett | 94 / 94 | 0.5 / 0.6 | 24 / 20 | 0.7–0.8 GB |
| hxh-chrollo-hisoka | 66 | 0.3 | 17 | 0.8 GB |

The file time splits three ways (sweet-girl, profiled with `Elab.async false`):

1. **Elaborating the checkpoint literals.** Each `cNN : W spec` is a 90–200 KB
   structure-instance term. Writing the same 95 literals with anonymous
   constructors (`⟨…⟩`, no field names) took sweet-girl from 581 s to 277 s and
   boyremoval from 356 s to 248 s, with every theorem still proved. What
   remains is 56 s of elaboration (still mostly checkpoints) and 134 s of
   kernel time.
2. **Kernel: views.** One paragraph (sweet-girl p69, 7 events), timed per
   prefix:
   - a goal event costs nothing;
   - a `drop` or `take` costs about 4 s;
   - a `tell` or `notice` costs 0.5–1.5 s;
   - one `view` of a 150-item base costs about 2 s.
   A space event makes every witness learn what it showed, and each learn
   rebuilds the learner's view for the liar check. So the per-event cost is
   (witnesses × facts) views.
3. **Kernel: what a view costs.** In a 58-literal view, `admitPlain`'s
   pairwise clash checks are about 0.8 s and `lits` (staleness, insertion sort)
   about 0.4 s. The kernel manages roughly 300 K reductions per second:
   - a `foldl` step costs about 70 µs;
   - one `clash` pair costs about 0.25 ms (`Supersedes` walks `spec.atoms` with
     `List.get?`);
   - with each literal's supersession class computed once, a pair costs about
     0.15 ms.

Kernel encoding, measured on 3000-element lists (`List.all`, `foldl`, nested
`all`):

| encoding | `all` | sum | nested 60×60 |
|---|---|---|---|
| core functions, `==` | 0.34 s | 0.32 s | 0.18 s |
| `List.rec` directly, `Nat.beq` | 0.16 s | 0.11 s | 0.07 s |

Structural recursion compiles through `brecOn` (`List.any._f` is in every
kernel profile), and `==` on `Nat` goes through `instBEqOfDecidableEq`,
`Nat.decEq` and `decide`. Writing the hot loops with recursors directly and
`Nat.beq` is 2–3× by itself.

Kernel unfold profile of p69 (`diagnostics`): `Bool.rec` 225 K, `List.rec`
170 K, `List.casesOn` 120 K, `and` 115 K, `decide` 73 K, `or` 66 K, `List.any`
64 K: boolean scans over lists, in clash and staleness checks.

Split by check kind (each check of every paragraph proved alone, so each
includes its own run of the paragraph's events; anonymous-constructor
checkpoints, first fast view):

| story | run + `pNN_step` | perception | completeness | `Valid` | setting |
|---|---|---|---|---|---|
| sweet-girl | 77 s | 53 s | 35 s | 30 s | 30 s |
| boyremoval | 218 s | 211 s | 206 s | 151 s | 61 s |
| private-fixpoint | 27 s | 1 s | – | 15 s | – |

In boyremoval the events themselves dominate: with lore, every view runs
`admit`, which takes `consistent (closure (kept ++ [l]))` for every literal
(cubic), and every event runs `recordSettled`, which builds each changed
character's view again.

## 2. Laws

Stated over the existing terms. Each became one proved equation, used
everywhere (§4).

* **L7, a clash needs a shared bit.** Two literals clash only if they share a
  fact (with opposite signs), or are both positive with facts of one
  supersession class. Keep, for a set of literals, three bit masks: the codes of
  its positive literals, the codes of its negative ones, and the classes of its
  positive ones. A literal whose bits are clear clashes with nothing in the set.
  So `admitPlain`'s scan of everything kept is needed only when a bit is set,
  which in a story is almost only for the literals the view then drops.
  (`Masks.no_clash`; false positives cost a scan, never a wrong answer.)
* **L8, the lore's closure is its least fixpoint.**
  - `closure` runs `|rules| + 1` passes. A pass that changes the list adds a
    rule head that was missing, so a pass with no change comes first, and the
    result is closed under the rules (`closure_closed`).
  - So `x ∈ closure ls ↔ Derivable ls x` (`mem_closure`): the closure depends
    only on what `ls` contains.
  - So `admit`'s test at literal `l`, `consistent (closure (kept ++ [l]))`, equals
    `consistent (closure (C ++ [l]))` for any `C` with the members of
    `closure kept`. That list is `C ++ N`, and only `N` (what `l` adds) needs
    checking (`consistent_append`).

  Known theory: semi-naive evaluation, where only new facts need joining (Bancilhon
  and Ramakrishnan 1986). Each admitted literal is an insertion into a
  materialised view, as in DRed and counting (Gupta, Mumick and Subrahmanian
  1993), with no deletions: the greedy prefix only adds.
* **L9, only later, fluent, adopted information outdates.** `stale` needs only
  the candidates that are fluent and adopted, compared by time before clash
  (`staleK_eq`), and the L7 masks of those candidates.
* **L10, a checkpoint is data, not syntax.** Elaborating 95 literal states of
  100 KB is half of sweet-girl's file. The kernel needs the term, not the
  elaborator's view of it: build the `Expr` from the value (`checkpoint%`,
  `ToExpr`). Nothing is trusted, because `pNN_step` proves the value is the
  state the events reach.
* **L11, equal states need no proofs to compare.** `decide (run c chunk = c')`
  with the derived `DecidableEq` reduces a `dite` and an `Eq.rec` per field. A
  derived `BEq` with `LawfulBEq` decides the same equation by booleans
  (`decEqW`).
* **L12, the kernel reduces recursors, not equation compilers.** Core's
  `List.all`, `foldl`, `filter` go through `brecOn` (`List.any._f` is in every
  profile). The same functions written with `List.rec` are 2–3× faster in the
  kernel. `@[csimp]` equations send compiled code back to core's versions.

## 3. Design: one engine, verified refinement

Kiran's revision rules out an untrusted solver plus certificate checker. Each
fast algorithm is a Lean function proved equal to its specification, and the
proofs run the fast function in the kernel:

* `view` keeps its name, type and meaning. Its body now runs `litsK`, `admitK`,
  `admitL` and `closureK`, and `view_eq_viewDef` proves it equal to the old
  body (`viewDef`). All existing theorems about `view` (`view_eq_viewSpec`,
  `view_eq_viewSpec_of_rec`, `view_run_start`, `view_consistent`) are re-proved
  through it.
* Every statement in a generated `Proofs.lean` is unchanged, because the fast
  functions are what the statements' definitions already call. Only literals
  are written differently.
* Compiled code uses the same functions: the `K` loops are `@[csimp]`-equal to
  core's. So `langlib story` got faster too, and stays byte-identical by the
  same theorems.
* The fact keys live in `Supersedes` itself (`code`, `cls`, `cls_sup`,
  `codeInj`, `code_inj`), with defaults that are always right (one class, no
  injectivity). A separate class would be resolved to its default where `view`
  is defined, the trap ROUND-1 hit with `settled`. Worlds that give no keys are
  exactly as correct, only slower.

Candidates from the brief, and what measurement decided:

| candidate | decision |
|---|---|
| semi-naive Datalog, incremental views | adopted for `admit` with lore (L8: one closure pass per literal, early exit, masks). Per-event view maintenance (DRed across events) not built, see §6 |
| defeasible logic certificates | not on the measured path: DL runs only for flirt/agree events, and no DL constant appears in any kernel profile above the noise |
| grounded labelling, linear | not on any story's proof path (`Rules.lean` serves the argument view); design in §6 |
| STP, incremental | the kernel never runs the solver, it checks the timeline literal (`story_valid` ≈ 1.4 s) |
| precondition runs, state per checkpoint | already the incumbent (`Snap.lean`). Its cost was in writing the states (L10) and comparing them (L11) |

### Where verification costs speed, and what was done

* **Exactness on every input, not just reachable states.**
  - The masks only prefilter. A set bit still scans, so a coarse key cannot
    give a wrong view.
  - Making the check scan-free needed two laws: an injective code (`npair` and
    `Fact.code_inj`, proved), and classes that contain only facts able to
    supersede each other (`Fact.cls_sup`).
  - With `codeInj`, `containsK` answers membership from the bits alone. That
    needs a second invariant, `Masks.Sound` (every set bit is a member).
* **`before` is not a total order.** Two items with equal stamps that are both
  conservative are "before" neither way. So insertion sort cannot be replaced by
  merge sort with an equality proof. It stays, with a cheaper comparator
  (`beforeK_eq`).
* **No sortedness assumption.** Studio bases are in time order, but `lits` is
  defined on all lists. A suffix-by-time mask, which would remove most `stale`
  scans, needs that invariant carried into the proof. It was not built (§6).
* **Fuel stays.** `closure`'s `|rules| + 1` passes are the definition.
  `closureGoK` stops at the first pass with no change, which is provably the
  same list (`closure_go_fixed`).
* **`rfl` is slower than `decide`.** A kernel-only `rfl` for `pNN_step` saves
  about 1.4 s of kernel time on the largest paragraph, but inside the bundle the
  elaborator adds more than it saves. `decide` with the `BEq` instance stayed.

## 4. Built (all proved, no `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`)

`LangLib/World/Kernel.lean`:

* `K.all`, `any`, `filter`, `filterMap`, `foldl`, `append`, `insertBy`, `sortBy`,
  defined by recursors;
* `K.*_eq`: `@[csimp]` equal to core's (and to `Domain.insertBy`/`sortBy`).

`LangLib/World/Space.lean`: `Supersedes.code`, `cls`, `cls_sup`, `codeInj`,
`code_inj`, with defaults.

`LangLib/World/Mind.lean`:

* masks:
  - `Masks.no_clash`, `Masks.maybe_of_clash`, `Masks.has_add`, `Masks.ok_add`,
    `bitOf_addBit`;
  - `containsK_eq` (exact membership, scan-free under `codeInj`);
* `admitK_eq : admitK ls = admitPlain ls`;
* `beforeK_eq`, `staleK_eq`, `litsK_eq : litsK hs = lits hs`;
* `closure_closed`, `mem_closure`, `Derivable.mono`, `consistent_congr`,
  `consistent_append`, `admit_nil_of_inconsistent`;
* `closureK_eq : closureK ls = closure ls` (masks, early exit);
* `admitL_eq : admitL ls = admit ls`;
* `recordedHeadsK_eq`, `liar_test`, `view_eq_viewDef : view w c = viewDef w c`;
* the L5 theorems re-proved on top: `view_eq_viewSpec`, `view_eq_viewSpec_of_rec`,
  `view_consistent`, `recordOne_frame`, `recordOne_done`, `rec_run`.

`LangLib/Studio/World.lean`:

* `npair_inj`;
* `Fact.code_inj`: injective fact codes;
* `Fact.cls_sup`: classes;
* the Studio's `Supersedes` with `codeInj := true`.

`LangLib/Studio/Emit.lean`:

* derived `ToJson`/`FromJson`/`ToExpr` for the state;
* `checkpoint% r#"…"#`, which builds the checkpoint's term, with raw numerals;
* derived `BEq`/`ReflBEq`/`LawfulBEq` for the state's types, and `decEqW`.

`LangLib/Studio/Load.lean`:

* `story-lean` writes checkpoints with `checkpoint%`;
* other literals as anonymous constructors (`anonStructs`), and checkpoints as
  `noncomputable` (no compilation).

## 5. Measured, before and after

Before is main at `8bfe6d9`; after is the same with this round (`2ced319`).

Each story's files are regenerated by each build's own `langlib story-lean` and
checked by its own `lake env lean`. Before and after run back to back, story by
story, in the shared lock (CPU seconds, so other agents' load cancels out). The
reports are compared byte for byte.

| story | theorems | report before → after (s) | same | proofs before → after (s) | × | max RSS before → after (MB) | errors |
|---|---|---|---|---|---|---|---|
| essay-bloomfilters | 469 | 2.05 → 1.22 | same | 69 → 28 | 2.4 | 1052 → 1376 | 0 / 0 |
| essay-end-of-pl | 197 | 2.22 → 0.70 | same | 66 → 19 | 3.4 | 1462 → 1635 | 0 / 0 |
| hxh-chrollo-hisoka | 66 | 0.17 → 0.19 | same | 12 → 6 | 1.9 | 808 → 1438 | 0 / 0 |
| private-ao3-boyremoval | 349 | 23.33 → 6.73 | same | 352 → 89 | 3.9 | 4913 → 3239 | 0 / 0 |
| private-ao3-sweet-girl | 831 | 9.02 → 6.64 | same | 597 → 112 | 5.3 | 2194 → 2101 | 0 / 0 |
| private-fixpoint-v1c01 | 127 | 0.13 → 0.15 | same | 16 → 8 | 1.9 | 868 → 1631 | 0 / 0 |
| private-fixpoint-v1c02 | 121 | 0.11 → 0.13 | same | 15 → 11 | 1.3 | 901 → 1460 | 0 / 0 |
| private-fixpoint-v1c03 | 122 | 0.20 → 0.21 | same | 15 → 7 | 2.0 | 928 → 1625 | 0 / 0 |
| private-fixpoint-v1c04 | 123 | 0.13 → 0.14 | same | 15 → 10 | 1.6 | 947 → 1632 | 0 / 0 |
| private-fixpoint-v1c05 | 122 | 0.16 → 0.16 | same | 14 → 8 | 1.8 | 916 → 1626 | 0 / 0 |
| private-fixpoint-v2c06 | 123 | 0.19 → 0.20 | same | 15 → 9 | 1.7 | 928 → 1621 | 0 / 0 |
| private-fixpoint-v2c07 | 122 | 0.15 → 0.19 | same | 11 → 9 | 1.2 | 901 → 1625 | 0 / 0 |
| private-fixpoint-v2c08 | 122 | 0.19 → 0.19 | same | 13 → 7 | 1.7 | 915 → 1626 | 0 / 0 |
| private-fixpoint-v2c09 | 124 | 0.19 → 0.19 | same | 20 → 10 | 1.9 | 1019 → 1640 | 0 / 0 |
| private-fixpoint-v2c10 | 124 | 0.20 → 0.20 | same | 22 → 16 | 1.4 | 986 → 1603 | 0 / 0 |
| private-fixpoint | 273 | 0.67 → 0.53 | same | 293 → 45 | 6.4 | 1864 → 2041 | 0 / 0 |
| private-roof-ran | 149 | 1.81 → 1.22 | same | 40 → 22 | 1.9 | 1405 → 1784 | 0 / 0 |
| roof-pratchett | 94 | 0.27 → 0.24 | same | 12 → 9 | 1.3 | 859 → 1566 | 0 / 0 |
| roof | 94 | 0.24 → 0.24 | same | 10 → 8 | 1.2 | 860 → 1540 | 0 / 0 |
| **all stories** | | | | **1607 → 436** | **3.7** | | |

| example file (`lake env lean`) | before → after (s) | errors |
|---|---|---|
| FightSnaps | 6.14 → 5.75 | 0 / 0 |
| FightSnapsGen | 0.68 → 0.65 | 0 / 0 |
| FightMinds | 4.16 → 3.65 | 0 / 0 |
| Fight | 5.90 → 5.73 | 0 / 0 |
| DeathNoteArc | 13.32 → 14.30 | 0 / 0 |


* Every report is byte-identical, every theorem proves (0 errors), and no
  statement changed.
* The three stories the brief names:
  - sweet-girl, 597 → 112 s (5.3×);
  - boyremoval, 352 → 89 s (3.9×; it also peaks at 3.2 GB instead of 4.9);
  - private-fixpoint, 293 → 45 s (6.4×).
* All stories together: 1607 → 436 s.
* The target, an order of magnitude on the big stories, is not reached: 4–6×.
  §6 lists where the rest is.
* The fixpoint chapters and roof-sized stories gain less (1.2–2×). Their files
  are small, so fixed costs dominate: importing, the spec, the `#guard`s.
* Memory on small stories goes up by about 0.7 GB. `checkpoint%` runs in the IR
  interpreter (LangLib is not precompiled) and holds its JSON and terms. Small
  files are the ones where that shows.
* Examples compiled with `lake build`: the Nen fight (`FightSnaps`, `Fight`,
  `FightMinds`) is unchanged within noise, and Death Note is 13.3 → 14.3 s.
  These worlds give no fact keys, so they take the defaults, which are correct
  but only as fast as before, plus the masks' overhead. Giving
  `NenFact`/`DeathNote` facts a `code` and `cls` is the cheap next step.
* `langlib story` gets faster through the same `@[csimp]` functions: boyremoval
  23.3 → 6.7 s (36.8 s at `31d6d61` in §1), sweet-girl 9.0 → 6.6 s.


## 6. Not done, and next

* **Views per event (the largest remaining cost).** Each perceptual learn
  rebuilds the learner's view for the liar check, and with masks a view is now
  mostly linear. The next law is L3/L4 of ROUND-1 as an equation: the view after
  appending one item is the old view adjusted where the new item's bits meet
  it. That is incremental view maintenance across events (DRed). It needs the
  time order of a base (every item about a time ≤ now) as a proved invariant,
  which `RecOk` nearly is.
* **`stale` scans.** About half of the fluent items still hit a set bit, because
  the masks ignore time. A suffix-by-time mask (candidates strictly later than
  the item) would make the test exact for the Studio's facts, again under the
  time-order invariant.
* **Sharing the run across a paragraph's checks.** `perceptFrom`, `sceneOf` and
  `completeOk` (`stateAt`, `afterItem`, the counterfactual causes) each replay
  prefixes of the paragraph from `cPrev`. Separately they cost 4–5× the bundle,
  so the kernel's caches recover much of it, not all. The law is that every
  check reads states from one trace. Each check would need a version over the
  trace, proved equal to the current one.
* **Grounded labelling** (`Rules.lean`, owned by the agent writing the argument
  view, so not edited here):
  - `grounded` runs `|nodes| + 1` simultaneous rounds;
  - the same early exit as `closureGoK` (stop at a round that changes nothing)
    is exact, by the same argument as `closure_go_fixed`;
  - the linear algorithm (decrement a count of unrefuted attackers, a queue of
    nodes all of whose attackers are out; Modgil and Caminada 2009, Nofal et al.
    2014) is also a fixpoint of `labRound`, so its proof is the uniqueness of
    the least fixpoint, as in L8.
* **Defeasible logic.** `inCharacter` runs `certify` and then `Cert.check` in
  the kernel. `certify` only adds literals whose condition holds, so
  `(certify T).check T = true` is provable (with a fuel-adequacy argument like
  `closure_closed`), and the kernel could skip the check. Not measured as a cost
  in any story (§3).
* **STP.** `Time.solve` is `@[implemented_by solveFast]` with no theorem between
  them. Kiran's rule is `@[csimp]` with a proof. The kernel never runs it, so it
  costs no proof time. Proving `solveFast = solve`, or making `solve` the warm
  start itself, is the residue.
* **The Studio's report on a keystroke.** `langlib story` now takes about 7 s on
  the two AO3 chapters and under 2.1 s elsewhere (byte-identical). A keystroke
  changes one paragraph, so the next step is to keep each checkpoint state
  between reports and rebuild from the edited paragraph on.
