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

## 8. Arguments, minds and the rest of the world (November 2026)

The logic now gives more than the cards show: a paper's argument with its grounded labelling (`langlib argument`, `Studio/PaperArg.lean`), the story's argument graph (`Complete.lean`), each character's beliefs with their sources and strengths, nested beliefs, ties, affect, care, identity knowledge, the refined consent reading, and the style verdicts. What has been *shown* to work for drawing these is reviewed, study by study, in `docs/ui-visualisation-evidence.md`; the choices below cite it by section (E§n) and carry its strength labels.

**The forms in the literature.** Toulmin (1958) draws one argument as claim, data, warrant, backing, qualifier and rebuttal. Wigmore's charts (1913) draw a whole legal case as a graph of evidence for and against each probandum, with symbols for kinds of evidence and their force. Dung's abstract frameworks (*AIJ* 77(2), 1995, doi:10.1016/0004-3702(94)00041-X) reduce arguments to nodes and attacks; Caminada's labellings (*JELIA* 2006, doi:10.1007/11853886_11) give each argument IN, OUT or UNDEC, and the grounded labelling is the least one. AIF (Chesñevar et al., *KER* 21(4), 2006, doi:10.1017/S0269888906001044) separates information nodes from rule-application and conflict nodes, which Araucaria and OVA (Reed & Rowe 2004; Janier, Lawrence & Reed 2014) draw top-down as box-and-arrow trees; Rationale (van Gelder) draws the same with colour for support and objection. In epistemic logic, Kripke models draw worlds as nodes and each agent's indistinguishability as labelled edges, and DEL event models (Baltag, Moss & Solecki 1998) draw an update as a second such graph; Hintikka's World (Schwarzentruber 2018) animates them for teaching. None of these forms has been tested for readability with users beyond the teaching setting (E§1.3, E§8).

**What the evidence supports, and what we built.**

1. *Argument graphs are small, layered trees, one claim at a time* (E§2, E§3: strong for crossings and straight paths). A paper's graph has 150 nodes (RustBelt); node-link beats a matrix only for small graphs and path tasks (Ghoniem et al. 2005; Okoe et al. 2018). So the Argument tab lists the claims grouped by how the reader ends up holding them (accepted, on the authors' word only, unsupported, denied), and each opens into its own tree drawn top-down: the claim, then what supports and attacks it, then what supports and attacks those. A tree has no crossings and straight vertical chains (Purchase 1997; Ware et al. 2002). Shared premises are repeated, marked "also under …", instead of drawn as a DAG. Nodes are HTML boxes, so their text wraps; edges are drawn under them from measured positions.
2. *Edges are tapered, wide at the source; attack is dashed and red as well as tapered* (E§3: moderate, Holten & van Wijk 2009). No arrowheads on top of the taper (redundant cues gave no gain).
3. *Labels are words first, hue second* (E§10: moderate). Every node carries IN, OUT or UNDEC as text and as hue; UNDEC is lighter rather than a third saturated hue (MacEachren et al. 2012). A node that is IN although attacked says why on the node ("reinstated: its attacker is out, defeated by …"), because readers only partly restore reinstated arguments (Rahwan et al. 2010). Grounded semantics, which lay judgements match about as well as any (Cramer & Guillaume 2018).
4. *Belief: a table for "now", lanes for "when"* (E§5: strong). The Minds tab opens on a characters × propositions table at the current paragraph; below it, one lane per character on the paragraph axis, a bar for each belief from the paragraph it was gained to the one it was lost (LifeLines; Alonso et al. 1998). Static, never animated (E§6: strong).
5. *A false belief shows belief and fact in one cell* (E§8: no evidence for the display; the ground is the Sally-Anne error of substituting reality for belief). The cell reads "thinks: … / actually: …", outlined with a mark (≠) used nowhere else. In the lanes the false stretch of a bar is hatched. Dramatic irony is listed per paragraph: the character's false belief, and whether the reader has been shown the truth (a fact node of the argument graph at or before the paragraph) or only the world holds it.
6. *Strength by lightness, provenance on demand* (E§7: weak for the channel; moderate for filtering, Huang et al. 2009). Outright beliefs are solid, conservative ones lighter, noted ones faint; clicking a cell lists that belief's sources only: seen, told by whom (with the believer's trust in them), inferred, with each reason's weight.
7. *Nested beliefs as chip paths with a "through their eyes" switch* (E§8: none; to be tested first). "Mara → Kiran → the note is for Mara", marked wrong when the modelled belief is not Kiran's. The switch redraws the table as one character believes the others believe. No Kripke diagrams: untested and they grow with every agent and proposition.
8. *Ties, affect and bonds as sparklines on a shared scale, ≥ 24 px tall, stacked* (E§6: strong for multiples, moderate for the size, Heer et al. 2009; Javed et al. 2010), with the current paragraph marked.
9. *Consent as lanes with text* (E§5, E§10: moderate). Each scene (from an offer or first grant to a close or stop) has a lane per pair and act: a bar from grant to withdrawal or the scene's end, check-in ticks, limits written on the bar, a withdrawal end cap with the word "withdrawn", assumed acts written out with their reason. Consent state is never colour alone.
10. *Identity knowledge as a who-knows-what table* (knower × person: names, pronouns, private facts), with harms (misgendering, deadnaming, outing) listed as text.
11. *Style verdicts as rule lists*, failing rules first, each with its measured ratio; no chart, since every question is a lookup (Vessey 1991, E§10).
12. *At about 700 px* everything stacks; tables keep to the propositions someone holds; lanes stay horizontal and compress; trees stay top-down and use the panel's height (E§11: moderate).
13. *Adjacent and linked* (E§9, E§10: strong, spatial contiguity d ≈ 0.6–0.7, Ginns 2006). Every new node carries a `data-target`, so right-click inspects it, and the tabs follow the reading line; nothing repeats the prose.

Three of these rest on no evidence and are the first to test with users: the nested-belief chips, the false-belief cell, and whether IN/OUT/UNDEC labels read better than a sentence.

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
