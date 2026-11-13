# Visualising a story's logic paragraph by paragraph: a short review for the Studio

*Status: design note, November 2026. Scope: the right panel of StoryLangLib Studio. For each paragraph the checker produces the events it asserts, the scene state after it, who believes what and why, bonds and consent, goals and plans, a timeline, and a verdict. The question is how to show that next to prose, threaded so that change across the story is visible, without turning a reading tool into a dashboard. The chosen design is in Section 7.*

## 1. Storyline charts

**Origins.** Randall Munroe's *Movie Narrative Charts* (xkcd #657, 2009) draw each character as a line running left to right through time; lines that run together are characters in the same scene; bands group lines by location. The chart makes three things legible at a glance: who is with whom, when groups split and merge, and where each character is.

**Layout algorithms.** Ogawa & Ma ("Software evolution storylines", *SOFTVIS* 2010) first automated the form. Tanahashi & Ma ("Design considerations for optimizing storyline visualizations", *IEEE TVCG* 18(12), 2012, InfoVis) cast layout as optimisation: minimise line crossings, wiggles (vertical movement) and white space, subject to lines in a session being adjacent, and solved it with a genetic algorithm. Liu, Wu, Wei, Liu & Liu ("StoryFlow: Tracking the evolution of stories", *IEEE TVCG* 2013) made it fast and hierarchical (location tree, then sessions), with an ordering step (barycentric crossing reduction), an alignment step and a compaction step, and interactive edits. Tang et al. ("iStoryline", *TVCG* 2019) and Tang, Wu et al. ("PlotThread", *TVCG* 2020) add authoring: the user edits the chart and an optimiser respects the edits. Gronemann et al. ("Crossing minimization in storyline visualization", *GD* 2016) give exact ILP crossing minimisation for small instances, which is the Studio's size (three to six characters).

**What it gives the Studio.** The space module's state is exactly a storyline: per step, a location per character. The minds module adds what Munroe's charts cannot show: whether a character *knows* where another is, and false beliefs about location.

## 2. Story curves: telling order versus story order

Kim, Bach, Im, Schriber, Gross & Pfister ("Visualizing nonlinear narratives with story curves", *IEEE TVCG* 24(1), 2018) plot each event at (position in the text, position in story time). A linear narrative is the diagonal; flashbacks jump below it, flash-forwards above, "meanwhile" sections are horizontal runs. This is the Studio's syuzhet/fabula split (`Story.told` versus `Timed.chrono` with the solved `Timeline`). Bach et al. ("Telling stories about dynamic networks with graph comics", *CHI* 2016) and the comics-based timelines of Bach, Riche et al. argue for small multiples (one panel per step) over animation, because readers compare states better side by side than across time (Tversky, Morrison & Bétrancourt, "Animation: can it facilitate?", *IJHCS* 2002, a review finding little benefit from animation over static sequences).

## 3. Timelines and interval relations

Allen's relations (Allen, "Maintaining knowledge about temporal intervals", *CACM* 1983) are best shown as bars on a shared axis, not as relation names; the relation is visible in the bar geometry. LifeLines (Plaisant et al., *CHI* 1996) established the lane-per-entity bar layout; Brehmer, Lee, Bach, Riche & Munzner ("Timelines revisited: a design space and considerations for expressive storytelling", *IEEE TVCG* 2017) classify timelines by representation (linear, radial, spiral, grid), scale (chronological, relative, logarithmic, sequential) and layout (unified, faceted, segmented), and recommend linear + sequential or relative scale for event sequences whose absolute times are unknown, which is our case (the solver produces minimum relative endpoints).

## 4. Belief and epistemic state

There is no dominant visual idiom for epistemic state. Relevant precedents:

- **Kripke models / epistemic diagrams** in dynamic epistemic logic (van Ditmarsch, van der Hoek & Kooi, *Dynamic Epistemic Logic*, 2007): worlds as nodes, indistinguishability as labelled edges; the update is drawn as a model before and after. Precise but unreadable beyond a handful of worlds and agents; the Studio's minds are belief bases, not possible-worlds models, so this does not map directly.
- **Belief matrices.** Theory-of-mind benchmarks and narrative-planning papers (Shirvani, Ware & Farrell, *AIIDE* 2017; Sabre, Ware & Siler 2021) present "who believes what" as a table: agents × propositions, cells true/false/unknown, with false beliefs marked. Readers decode tables well when the cell vocabulary is tiny (Bertin, *Semiology of Graphics*, 1967; Cleveland & McGill, "Graphical perception", *JASA* 1984, on position/colour channels).
- **Provenance graphs.** Talk of the Town (Ryan et al., 2015) displays a character's knowledge with its source chain (saw, heard from X). The W3C PROV model and provenance visualisers (e.g. Prov Viewer) show derivations as DAGs. For the Studio the source of each belief (`Evid`: seen, told by, rumour, inferred), its strength reasons and its attitude (hard, radical, conservative, note) are already computed by `explain`; the natural display is a short justification list, expandable.
- **Delta displays.** Diff views (unified diffs; Tufte's "small multiples" and "the smallest effective difference", *Envisioning Information*, 1990) show only what changed. For a story with dozens of propositions, showing the full matrix every paragraph is noise; showing the cells that changed, with a compact running matrix available on demand, follows the smallest-effective-difference principle.

## 5. Argument maps and proof trees

Argument maps (Toulmin, *The Uses of Argument*, 1958; the Araucaria and Rationale tools; Reed, Walton & Macagno, "Argument diagramming in logic, law and artificial intelligence", *KER* 2007) render claims, grounds and rebuttals as boxes with support and attack arrows. Defeasible logic proofs fit this exactly: the rule that concludes, the rules against it, which defeated which by superiority. Proof-tree displays in proof assistants (Gentzen-style trees in Proof General / Alectryon by Pit-Claudel, *SLE* 2020) show that interleaving the source with the proof state, revealed on demand, keeps proofs readable next to text; Alectryon's lesson is that the proof state should be adjacent to the line that produced it and collapsed by default. The Studio's verdicts and `why` strings ("out of character (shy people hold back); to justify it, first establish: attraction draws them on ...") are already argument-map-shaped: conclusion, blocker, possible repairs.

## 6. Two-column reading interfaces

Margin-aligned commentary is old (glossed manuscripts, the Talmud page); modern instances are Tufte-style sidenotes (Tufte CSS), Genius annotations, literate-programming tools (Docco and Pycco's two-column prose/code), Observable's side panels, and Alectryon again. Docco's alignment rule (each comment block beside the code it explains, both scrolling together) is the one the spec asks for. When the right column is taller than its paragraph (common here), two options exist: pad the left (breaks reading) or let the right side scroll independently and *sync on focus* (the paragraph at the reading line selects its card). Overleaf's synctex-style scroll sync and Typora's outline both use the second.

## 7. Design chosen

**Layout.** The right panel is a column of *paragraph cards*, one per paragraph, in order. Scrolling is synced by focus: the paragraph nearest the reading line (40% down the viewport) is the *current* paragraph; its card scrolls into view on the right and is highlighted, and clicking a card scrolls the prose to its paragraph. The card column and the prose never pad each other.

**The thread: a storyline spine.** Down the left edge of the card column runs a vertical storyline chart (Munroe / Tanahashi & Ma, rotated so story time flows downward with the text). Columns are places; each character is a coloured line; a character's line sits in the column of their location after each paragraph, so lines converge when characters share a scene and split when they part. A hollow marker on a line means the location was assumed rather than stated (`PartialLoc`); a small eye marks a paragraph where the character witnessed something. The spine is drawn with crossing-minimised place order (exhaustive search over place orders, cheap for four or five places). Each card's top edge is aligned with its paragraph's row of the spine, so the spine reads as the story's state over time, and each card as its detail.

**Each card**, top to bottom, collapsed to what changed:
1. *Verdict badge*: valid (green check), plausible under N assumptions (amber, lists them), failing (red, the first failure's `why`), plus "proved" when the Lean kernel proof for the paragraph has been checked.
2. *Events*: one line per event in a compact notation (`Theo → roof`, `Mara takes note`, `Mara tells Kiran: Theo likes Mara`), each with its status: ok, assumed (amber dot), out of character / blocked (red); unmotivated actions flagged (`motives`); each event links to the verb token in the prose when the event was read off the text.
3. *Scene delta*: who moved, who holds what.
4. *Beliefs*: belief deltas only: new or changed beliefs per character as chips (`Mara ✓ note for Mara` with a red "false" flag when it is a false belief), each expandable to `explain` (sources, strength reasons, attitude, outranked by what).
5. *Bonds and consent*: changes in trust/attraction/affection/tension per directed pair as `+1`/`−1` chips; consent given or withdrawn as explicit rows (`Kiran agrees: kiss with Theo`); intimate acts show the consent they rest on.
6. *Goals and plans*: goals adopted, plan steps advanced, promises kept or open.
7. *Time*: a mini interval chart (Brehmer et al.'s linear relative timeline) of the paragraph's events on the solved timeline, with flashback/meanwhile labels, and a tiny story curve (Kim et al.) in the card header when the paragraph is told out of order.

**Whole-story views** (header toggle): a belief matrix (characters × facts, at the current paragraph, false beliefs outlined), bond sparklines per pair across paragraphs, the story curve, and, for the top-down workflow, the beat layer with refinement status per beat.

**Why this design.** The storyline spine carries what changes most (place, company) as position, the strongest perceptual channel (Cleveland & McGill); belief and bond changes are rare and discrete, so they are listed as deltas (Tufte) instead of drawn; proofs and explanations stay collapsed until asked for (Alectryon); and nothing on the right requires the prose to move.

## References (selected)

- Allen, J. F. (1983). Maintaining knowledge about temporal intervals. *CACM* 26(11).
- Bach, B. et al. (2016). Telling stories about dynamic networks with graph comics. *CHI*.
- Brehmer, M., Lee, B., Bach, B., Riche, N. H. & Munzner, T. (2017). Timelines revisited. *IEEE TVCG* 23(9).
- Cleveland, W. S. & McGill, R. (1984). Graphical perception. *JASA* 79(387).
- Kim, N. W. et al. (2018). Visualizing nonlinear narratives with story curves. *IEEE TVCG* 24(1).
- Liu, S. et al. (2013). StoryFlow: Tracking the evolution of stories. *IEEE TVCG* 19(12).
- Munroe, R. (2009). Movie Narrative Charts. xkcd #657.
- Ogawa, M. & Ma, K.-L. (2010). Software evolution storylines. *SOFTVIS*.
- Pit-Claudel, C. (2020). Untangling mechanized proofs (Alectryon). *SLE*.
- Plaisant, C. et al. (1996). LifeLines: visualizing personal histories. *CHI*.
- Reed, C., Walton, D. & Macagno, F. (2007). Argument diagramming in logic, law and artificial intelligence. *Knowledge Engineering Review* 22(1).
- Tanahashi, Y. & Ma, K.-L. (2012). Design considerations for optimizing storyline visualizations. *IEEE TVCG* 18(12).
- Tang, T. et al. (2019). iStoryline: effective convergence to hand-drawn storylines. *IEEE TVCG* 25(1).
- Tufte, E. R. (1990). *Envisioning Information*. Graphics Press.
- Tversky, B., Morrison, J. B. & Bétrancourt, M. (2002). Animation: can it facilitate? *IJHCS* 57(4).
- van Ditmarsch, H., van der Hoek, W. & Kooi, B. (2007). *Dynamic Epistemic Logic*. Springer.
- Ware, S. G. & Siler, C. (2021). The Sabre narrative planner. *AAMAS*.
