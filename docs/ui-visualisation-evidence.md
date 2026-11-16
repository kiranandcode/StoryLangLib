# What the evidence says about the Studio's visualisations

*Status: literature review, November 2026. A companion to `docs/ui-visualisation.md`. That note describes the forms the Studio borrows (storylines, story curves, timelines, belief matrices, argument maps, two-column reading) and picks a design. This note asks a narrower question: for each form, what has been **measured**, on whom, and what held up? Throughout, "shown to work" means a controlled comparison with a reported effect. "Exists / is popular" means a tool paper, a design space, expert interviews, Likert ratings, or advocacy.*

**How the figures were checked.** I checked each DOI against its Crossref record (title, venue, year). I took sample sizes and effect sizes from the paper's full text or abstract where I could read it. Figures I could only take from a secondary source carry "(secondary)". Figures I could not confirm say so. None are filled in from memory. The local PLDB/plwiki corpus covers PL venues and had nothing relevant, so every source below came from the open web.

## 0. Summary of evidential status

| Pattern | Status | Best evidence |
|---|---|---|
| Argument mapping for teaching critical thinking | Shown to work, but confounded with intensive instruction | Cullen et al. 2018 (controlled, d ≈ 0.7); Álvarez Ortiz 2007 (meta, uncontrolled gains) |
| Reading an argument map instead of text | Mixed: helps recall, not comprehension | Dwyer et al. 2010 (n = 400) |
| Showing an AF graph alongside text | Weakly shown: helps compliance with semantics principles; one null result on interpretation | Vesic et al. 2022/Teovanović et al. 2026; Mardah et al. 2023 |
| Grounded labelling as a model of lay judgement | Roughly matches (~75–83%), tied with CF2 | Cramer & Guillaume 2019; Guillaume et al. 2022 |
| Toulmin, Wigmore, AIF, OVA, Araucaria, Carneades, bipolar AFs | Exist; no controlled evaluation of the visual form found | — |
| Matrix vs node-link | Shown, and task-dependent | Ghoniem et al. 2005; Okoe et al. 2019 |
| Fewer crossings, straight paths, wide crossing angles, tapered edges | Shown | Purchase 1997; Ware et al. 2002; Huang et al. 2008; Holten & van Wijk 2009 |
| Edge bundling | Hurts path tracing | McGee & Dingliana 2012 |
| Storyline layouts (Tanahashi & Ma, StoryFlow, iStoryline, PlotThread) | Exist; evaluated only by metrics, experts and Likert ratings | Di Bartolomeo et al. 2026 survey |
| Story curves | Learnable (~80% correct, n = 13); no comparison condition | Kim et al. 2018 |
| Narrative-vis genres, visualization rhetoric | Descriptive corpus analyses | Segel & Heer 2010; Hullman & Diakopoulos 2011 |
| Lane timelines vs tables | Shown: ~2× faster on interval questions, equal on exact lookups | Alonso et al. 1998 |
| Small multiples vs animation | Shown: small multiples are more accurate and faster for analysis | Robertson et al. 2008; Archambault et al. 2011; Farrugia & Quigley 2011 |
| Small charts (~24 px) | Shown to remain readable | Heer et al. 2009 |
| Sparklines in text | Exist; no controlled performance study found | Goffin et al. 2014, 2017 (design space, qualitative) |
| Uncertainty: quantile dotplots, HOPs, gradients over error bars | Shown, for numeric uncertainty | Kay et al. 2016; Fernandes et al. 2018; Hullman et al. 2015; Correll & Gleicher 2014 |
| Kripke models, DEL event models, nested-belief diagrams | Exist; no user study found | — |
| Spatial contiguity (no split attention) | Shown repeatedly | Ginns 2006 (d = 0.72); Schroeder & Cenkci 2018 (g = 0.63) |
| Marginal vs pop-up glosses | Small studies, mostly L2 reading | Abraham 2008 meta; gloss-position studies |

## 1. Argument maps and argumentation frameworks

### 1.1 Argument mapping as pedagogy

**Twardy (2004).** "Argument maps improve critical thinking." *Teaching Philosophy* 27(2):95–116. doi:10.5840/teachphil200427213.
- Setting: a first-year Monash critical-thinking class of about 135 students taught with Reason!Able, measured pre and post on the California Critical Thinking Skills Test (CCTST).
- Result: a gain of about **0.72 SD**. van Gelder's courses averaged about 0.8. Twardy cites about 0.34 SD for a whole first year of university.
- Twardy's own caveat: the design has no control group. The comparisons are across classes that differ in lecturer, size and aptitude.

**van Gelder, Bissett & Cumming (2004).** "Cultivating expertise in informal reasoning." *Canadian Journal of Experimental Psychology* 58(2):142–152. doi:10.1037/h0085794.
- Design: a 12-week course of deliberate practice with Reason!Able.
- Result: CCTST gains of about 0.8 SD (secondary, via Davies 2011). Practice hours correlated with gain at r ≈ .31 (secondary, unconfirmed). Per-study n is unconfirmed.
- No control arm, so practice and mapping cannot be separated.

**Álvarez Ortiz (2007).** *Does philosophy improve critical thinking skills?* MA thesis, University of Melbourne. https://www.reasoninglab.com/wp-content/uploads/2017/05/Alvarez-Final_Version.pdf
- Method: a meta-analysis of within-group pre/post gains, normalised to one semester.

| Group | k | Gain per semester (SD) | 95% CI |
|---|---|---|---|
| Philosophy CT course, no argument mapping | 16 | 0.34 | [0.21, 0.48] |
| Philosophy CT course, some argument mapping | 10 | 0.68 | [0.51, 0.86] |
| Philosophy CT course, lots of argument-mapping practice | 7 | 0.78 | [0.67, 0.89] |
| Non-philosophy students, no CT instruction | 55 | 0.12 | — |

- Caveats: the "lots of practice" studies come largely from van Gelder's group, and all the gains are uncontrolled.

**Harrell (2011).** "Argument diagramming and critical thinking in introductory philosophy." *Higher Education Research & Development* 30(3):371–385. doi:10.1080/07294360.2010.502559.
- Design: a quasi-experiment with 269 students; one group was taught diagramming, the other was not.
- Result: **low-achieving students gained significantly; high achievers showed no difference.**
- Harrell (2008, *Teaching Philosophy* 31(4):351–374, doi:10.5840/teachphil200831437) reports that pencil-and-paper diagramming also works. I could not obtain its n or effect sizes.

**Cullen, Fan, van der Brugge & Elga (2018).** "Improving analytical reasoning and argument understanding: a quasi-experimental field study of argument visualization." *npj Science of Learning* 3:21. doi:10.1038/s41539-018-0038-5. This is the strongest controlled study.
- Participants: Princeton first-years; 105 in the seminar and 56 waitlist controls; students self-selected into the seminar.
- Results: LSAT Logical Reasoning favoured the seminar group, **d = 0.71 [0.37, 1.04]**. Blind-scored essays also favoured it, **d = 0.87 [0.26, 1.48]**.
- The authors' caveat: the study cannot separate visualisation from about 5.5 hours a week of intensive, feedback-rich instruction.

**Dwyer, Hogan & Stewart (2010).** *Thinking Skills and Creativity* 5(1):16–22. doi:10.1016/j.tsc.2009.05.001. This is the cleanest test of *reading* a map, which is the Studio's use.
- Participants: 400 undergraduates studied a 30- or 50-item argument as a colour map, a black-and-white map, or text.
- Recall: maps beat text, but the effect was small (η² = .041). Colour and black-and-white maps did not differ.
- **Comprehension: no effect (η² = .002).**
- Dwyer et al. (2012, *Metacognition and Learning* 7(3):219–244, doi:10.1007/s11409-012-9092-1, n = 74) found an 8-week mapping e-course improved Halpern Critical Thinking Assessment scores over a no-instruction control. Effect sizes were not reported in the abstract.

**Syntheses.**
- Davies (2011, *Higher Education* 62(3):279–301, doi:10.1007/s10734-010-9387-6) is conceptual. It separates mind maps, concept maps and argument maps and presents no new data.
- Lin, Chang, Lin & Ryoo (2026, *Technology, Knowledge and Learning* 31:641–668, doi:10.1007/s10758-026-09981-8) pool k = 20 effects (N = 1,455). A search snippet gives g ≈ 1.59, falling to ≈ 0.87 after publication-bias correction. I have not checked this against the paper.
- Nesbit & Liu (2025, *Higher Education Quarterly*, doi:10.1111/hequ.70063) is a systematic review of 124 studies, with no pooled effect.

**What held up.** Courses that make students build maps raise critical-thinking scores, by roughly 0.7 SD where controlled. That effect cannot be separated from the teaching. Merely *reading* a map instead of text helps recall a little and does not help comprehension. Weaker reasoners benefit most.

### 1.2 The forms themselves

The following formalisms and tools exist and are widely used. I found **no controlled evaluation of their visual form**:
- Toulmin's layout.
- Wigmore charts: Wigmore 1913, developed by Anderson, Schum & Twining. The literature is pedagogy and commentary.
- Dung frameworks with Caminada's IN/OUT/UNDEC labellings: Caminada 2006, JELIA, LNCS 4160:111–123, doi:10.1007/11853886_11.
- Bipolar frameworks: Cayrol & Lagasquie-Schiex 2005, ECSQARU, LNCS 3571:378–389, doi:10.1007/11518655_33.
- AIF: Chesñevar et al. 2006, *KER* 21(4):293–316, doi:10.1017/S0269888906001044.
- Araucaria: Reed & Rowe 2004, *IJAIT* 13(4):961–979, doi:10.1142/S0218213004001922. Rowe et al. (2006, *Teaching Philosophy* 29(2), doi:10.5840/teachphil200629217) surveyed 22 students' satisfaction, with no performance measure.
- OVA+: Janier, Lawrence & Reed 2014, COMMA, doi:10.3233/978-1-61499-436-7-463.
- Carneades.

I found no evaluated system called "ArgVis".

### 1.3 How people judge frameworks, and whether the graph helps

**Rahwan et al. (2010).** *Cognitive Science* 34(8):1483–1502. doi:10.1111/j.1551-6709.2010.01123.x.
- Design: members of the public rated confidence in a conclusion; the arguments were in prose, with no diagrams.
- Results (Study 1, n = 20): confidence was 5.9 at baseline, **4.0 when the argument was defeated, and 5.2 when it was reinstated.** Reinstatement was real (η²p = .34) but **incomplete**, with a residue that no standard semantics predicts. Floating reinstatement (Study 2, n = 47) behaved the same.

**Cramer & Guillaume (2019).** JELIA, LNCS 11468:102–115. doi:10.1007/978-3-030-19570-0_7.
- Participants: 61 undergraduates, who saw both the prose and the attack graph.
- Agreement with their judgements: grounded 75.0% and CF2 75.5%. Among the 49 coherent participants, both were about 82–83%. Preferred semantics fitted worse (Cramer & Guillaume 2018, COMMA, doi:10.3233/978-1-61499-906-5-413).
- Guillaume et al. (2022, *PLOS ONE*, doi:10.1371/journal.pone.0273225, n = 130) had participants draw the attack graphs themselves. Attacks were identified correctly over 80% of the time after discussion.

**Graph versus text.** As far as I found, this is the only direct manipulation: Vesic, Yun & Teovanović (2022), "Graphical representation enhances human compliance with principles for graded argumentation semantics," AAMAS 2022, pp. 1319–1327. Crossref lists the DOI as 10.65109/itwn6917.
- Its extended version is Teovanović, Vesic & Yun (2026), *Artificial Intelligence* 351, doi:10.1016/j.artint.2025.104457. Showing the graph increased compliance with principles such as independence and void precedence. The gain was largest for people high in cognitive reflection. Asking people to draw the graph helped when none was given.
- I could not confirm the n or the percentages.
- Against it, Mardah et al. (2023, arXiv:2303.03235, n = 25) found graphs improved user experience and lowered NASA-TLX workload, but **interpretation and decision outcomes were the same as with text**.

## 2. Node-link versus matrix

**Ghoniem, Fekete & Castagliola.** InfoVis 2004, doi:10.1109/INFVIS.2004.1. Journal version: *Information Visualization* 4(2):114–135, 2005, doi:10.1057/palgrave.ivs.9500092.
- Participants: 36 computer-science postgraduates and researchers.
- Graphs: random graphs of 20, 50 and 100 nodes at densities 0.2–0.6.
- Tasks: seven, from counting nodes to finding a path.
- Results: above about 20 nodes, matrices won most tasks. For example, finding the most connected node in large graphs was 57% correct with a matrix against 25% with node-link. **Path finding favoured node-link on small graphs (99% vs 70%)**; the advantage faded on large or dense graphs.
- Caveat: the graphs were random and meaningless.

**Keller, Eckert & Clarkson (2006).** *Information Visualization* 5(1):62–76. doi:10.1057/palgrave.ivs.9500116.
- Data: real engineering networks of up to 50 nodes.
- Results (secondary descriptions): node-link was better for small, sparse graphs and for path tasks; matrices were better for complex ones. n is unconfirmed.

**Okoe, Jianu & Kobourov (2019).** "Node-link or adjacency matrices: old question, new insights." *IEEE TVCG* 25(10):2940–2952. doi:10.1109/TVCG.2018.2865940. It is an expanded version of a GD 2017 paper.
- Participants: 864 crowd workers.
- Data: two real scale-free networks of about 250–330 nodes; 14 tasks.
- Results: **node-link won most connectivity and path tasks and one memorability task; matrices won common-neighbour tasks and some cluster tasks.**
- The authors limit their claims to these datasets and interactions.

**What held up.** The question has no single answer. Path and connectivity tasks favour node-link, especially for small graphs. Lookup tasks and dense graphs favour matrices: "is X adjacent to Y", "who has the most links", "common neighbours". This is Vessey's cognitive fit (1991, *Decision Sciences* 22(2):219–240, doi:10.1111/j.1540-5915.1991.tb00344.x): graphs suit spatial tasks and tables suit symbolic lookup. Vessey re-analysed earlier studies rather than running a new experiment. Speier (2006, *IJHCS* 64(11):1115–1131, doi:10.1016/j.ijhcs.2006.06.007) adds that people felt *more confident* with tables even where graphs performed better.

## 3. Graph aesthetics and readability

**Crossings.** Purchase (1997), "Which aesthetic has the greatest effect on human understanding?", GD 1997, LNCS 1353:248–261, doi:10.1007/3-540-63938-1_67.
- The abstract calls crossing reduction "by far the most important" of five aesthetics. Bends and symmetry had lesser effects, and minimum angle and orthogonality had none. n is unconfirmed.
- Purchase, Cohen & James (1997, *ACM JEA* 2, doi:10.1145/264216.264222) agree on crossings and bends. A secondary survey reports symmetry as non-significant there.
- Purchase (2000, *Interacting with Computers* 13(2):147–162, doi:10.1016/S0953-5438(00)00032-1) found crossings mattered most, but eight layout algorithms produced similar performance.
- Purchase (2002, *JVLC* 13(5):501–516, doi:10.1006/jvlc.2002.0232) defines metrics; it is not an experiment.
- Caveat: a later UML class-diagram study by Purchase et al. reportedly did not reproduce the aesthetic effects. Informal feedback there favoured grouping semantically related classes (secondary; DOI unverified).

**Paths.** Ware, Purchase, Colpoys & McGill (2002), *Information Visualization* 1(2):103–110, doi:10.1057/palgrave.ivs.9500013.
- Task: tracing the shortest path in 42-node spring layouts.
- Results: response time was predicted by path length, then by **path continuity (straightness)**, then by crossings *on the path*. Total crossings predicted poorly.
- Partial non-replication: Yoghourdjian et al. (2020, arXiv:2008.07944, n = 22) used larger graphs, and global measures predicted better there.

**Crossing angles.** Huang, Hong & Eades (2008), "Effects of crossing angles," PacificVis, doi:10.1109/PACIFICVIS.2008.4475457. Path-tracing time fell as the crossing angle grew, levelling off near 90°. n is unconfirmed.

**Cognitive load.** Huang, Eades & Hong (2009), *Information Visualization* 8(3):139–152, doi:10.1057/ivs.2009.10.
- Participants: 30 students read sociograms. One version showed all relations colour-coded; the other was filtered to the relation the task needed.
- Results: **accuracy was the same** (0.84 vs 0.88, n.s.). **Self-rated mental effort was far higher unfiltered** (η² = .78).
- Lesson: accuracy alone hides the cost of clutter.

**Edge direction.** Holten & van Wijk (2009), "A user study on visualizing directed edges in graphs," CHI, doi:10.1145/1518701.1519054.
- Results: **tapered edges (wide at the source, narrow at the target) beat standard arrowheads** and colour gradients. Combining cues gave no extra gain. Arrowheads cluttered where edges converged. n is unconfirmed.
- Replication: Holten, Isenberg, van Wijk & Fekete (2011, PacificVis, doi:10.1109/PACIFICVIS.2011.5742390, n = 25). Tapered edges were fastest, and the only significant pairwise time difference was tapered versus glyphs. Accuracy was high for all (93–97%).

**Edge bundling.** McGee & Dingliana (2012), AVI, doi:10.1145/2254556.2254670. Bundling **hurt path-tracing accuracy and time**. It sped up cluster-level questions but did not make them more accurate. n is unconfirmed.

**Layered layouts.** Sugiyama, Tagawa & Toda (1981), *IEEE SMC* 11(2):109–125, doi:10.1109/TSMC.1981.4308636. I found no controlled test of layered layouts against alternatives for general directed graphs.
- The nearest evidence is for trees: Burch et al. (2011, *IEEE TVCG* 17(12):2440–2448, doi:10.1109/TVCG.2011.193, n = 38). Traditional top-down and orthogonal trees beat radial ones on a least-common-ancestor task.
- So a layered layout is *supported indirectly*: it is a crossing-minimising, direction-consistent layout, and those are the properties the studies above measure.

## 4. Storylines and narrative visualisation

Every storyline-layout paper is evaluated by metrics or by experts. None compares reader comprehension against a baseline:
- **Tanahashi & Ma (2012)**, TVCG 18(12):2679–2688, doi:10.1109/TVCG.2012.212. Layout metrics only (crossings, wiggles, white space).
- **StoryFlow** (Liu et al. 2013, TVCG 19(12):2436–2445, doi:10.1109/TVCG.2013.196). Interviews with 3 experts and performance benchmarks.
- **iStoryline** (Tang et al. 2019, TVCG 25(1):769–778, doi:10.1109/TVCG.2018.2864899):
  - 74 students hand-drew storylines.
  - 25 students mapped hand-drawn features to narrative meaning and rated layouts.
  - 12 users rated the interactions (Likert means 3.75–4.75).
  - 3 experts compared it with StoryFlow.
  - The abstract calls the evaluation qualitative.
- **PlotThread** (Tang et al. 2021, TVCG 27(2):294–303, doi:10.1109/TVCG.2020.3030467). Use cases and 3 expert interviews.
- Di Bartolomeo et al.'s storyline survey (2026, *Computer Graphics Forum* 45(3), doi:10.1111/cgf.70499) confirms the pattern. Crossings are the usual quality metric, and the link between design choices and reader tasks is an open problem.

Story curves (Kim et al. 2018, TVCG 24(1):595–604, doi:10.1109/TVCG.2017.2744118) is the exception, with a reader study:
- Participants: 13, mostly graduate students, after about 17 minutes of training.
- Result: they answered 16/20 pattern questions correctly (SD 3.4).
- Caveat: there was no comparison condition. The study shows the form is learnable, not that it beats an alternative.

The genre and rhetoric papers are **descriptive corpus analyses, not tests**:
- Segel & Heer (2010), TVCG 16(6):1139–1148, doi:10.1109/TVCG.2010.179: 58 examples, 7 genres.
- Hullman & Diakopoulos (2011), "Visualization rhetoric: framing effects in narrative visualization," TVCG 17(12):2231–2240, doi:10.1109/TVCG.2011.255: 51 examples.

Hullman et al. (2013, TVCG 19(12):2406–2415, doi:10.1109/TVCG.2013.119) did run two studies. Sequences with parallel structure gave memory and rating benefits. n is unconfirmed.

## 5. Timelines

**Alonso, Rose, Plaisant & Norman (1998).** *Behaviour & Information Technology* 17(5):249–262. doi:10.1080/014492998119328. This is the controlled test of LifeLines (Plaisant et al. 1996, CHI, doi:10.1145/238386.238493).
- Design: 36 participants, between subjects, static displays, 31 questions.
- Questions predicted to favour LifeLines (interval comparisons, lookups across rows or columns): **LifeLines was about 2× faster** (107 s vs 211 s, t(34) = 4.79, p < .0001).
- Questions predicted to favour the table (exact dates, codes, overlaps): **no difference** (101 s vs 101 s).
- The one significant win for the table was a lookup that needed a colour code decoded. Recall was better with LifeLines.

**Brehmer et al. (2017).** TVCG 23(9):2151–2164. doi:10.1109/TVCG.2016.2614803. A design space drawn from 263 timelines, with no user study.

**Di Bartolomeo et al. (2020).** "Evaluating the effect of timeline shape on visualization task performance," CHI, doi:10.1145/3313831.3376237.
- Design: 192 crowd workers.
- Results: shape (horizontal line, vertical line, circle, spiral) affected **time but not accuracy**. Horizontal lines were preferred as easiest to read, and spirals were slowest.

## 6. Small multiples, animation and sparklines

**Robertson et al. (2008).** "Effectiveness of animation in trend visualization," TVCG 14(6):1325–1332, doi:10.1109/TVCG.2008.125.
- Design: 36 participants. Small multiples were **more accurate** than animation.
- For analysis, animation was **slowest** (83 s vs 46 s for small multiples). For presentation it was fastest.
- People enjoyed animation more despite making more errors with it.

**Archambault, Purchase & Pinaud (2011).** TVCG 17(4):539–552. doi:10.1109/TVCG.2010.78.
- In dynamic graphs, small multiples were faster than animation on all five tasks.
- Animation made fewer errors only on questions about what appeared in the same time step.
- Preserving the mental map made little difference (a null result). n is unconfirmed.

**Farrugia & Quigley (2011).** *Information Visualization* 10(1):47–64. doi:10.1057/ivs.2010.10. Static small multiples were generally more effective, especially for time, and were preferred.

**Javed, McDonnel & Elmqvist (2010).** TVCG 16(6):927–934. doi:10.1109/TVCG.2010.162.
- Design: 16 participants, 3,456 trials.
- Results: technique did not affect correctness. Split-space charts (small multiples) were **faster for comparisons spanning much of the chart**; a shared-space line chart was faster for local comparisons.

**Heer, Kong & Agrawala (2009).** "Sizing the horizon," CHI, doi:10.1145/1518701.1518897.
- Participants: 18, 30 and 8 in three studies.
- Results: line charts stayed accurate down to about **24 px** tall. One-band mirrored horizon charts matched line charts twice their height. Below 24 px, two bands helped; four or more bands hurt.

**Sparklines.** Tufte's sparklines (*Beautiful Evidence*, 2006) are a design argument. Goffin et al. 2014 (TVCG 20(12):2291–2300, doi:10.1109/TVCG.2014.2346435) is a placement design space with no participants; one search snippet claims 120 participants, which the full text does not support. Goffin et al. 2017 (TVCG 23(10):2275–2287, doi:10.1109/TVCG.2016.2618797) is a qualitative study with designers. **I found no controlled study of how well people read sparklines.** The nearest evidence for small charts is Heer et al. 2009.

## 7. Uncertainty and graded belief

**Hullman, Qiao, Correll, Kale & Kay (2019).** "In pursuit of error," TVCG 25(1):903–913, doi:10.1109/TVCG.2018.2864889. A survey of 86 uncertainty-visualisation user studies. Most measure accuracy or satisfaction, not decision quality, and they define "uncertainty" inconsistently.

**Hypothetical outcome plots (HOPs).**
- Hullman, Resnick & Adar (2015), *PLOS ONE* 10(11):e0142444, doi:10.1371/journal.pone.0142444. With 288 participants, animated HOPs beat error bars and violin plots on judgements that involve two or three variables. They lost on some single-variable mean estimates.
- Kale et al. (2019), TVCG 25(1):892–902, doi:10.1109/TVCG.2018.2864909. HOPs let untrained viewers detect trends at lower levels of evidence.

**Quantile dotplots.**
- Kay, Kola, Hullman & Munson (2016), CHI, doi:10.1145/2858036.2858558. With 541 analysed participants, 20-dot plots gave about 1.15× lower variance in probability estimates than density plots.
- Fernandes et al. (2018), CHI, doi:10.1145/3173574.3173718. In a preregistered study with 408 participants, dotplots and CDFs led to better payoffs than text and than no uncertainty display.

**Correll & Gleicher (2014).** "Error bars considered harmful," TVCG 20(12):2142–2151, doi:10.1109/TVCG.2014.2346298.
- Design: 240 participants across the reported experiments.
- Results: bar charts produced a within-the-bar bias. Gradient and violin plots removed it and raised confidence.

**MacEachren et al. (2012).** "Visual semiotics & uncertainty visualization: an empirical study," TVCG 18(12):2496–2505, doi:10.1109/TVCG.2012.279.
- Results (secondary; the abstract does not list them): **fuzziness, location, value (lightness), arrangement, size and transparency** were rated intuitive for uncertainty. Hue, orientation and shape were rated less intuitive. n is unconfirmed.

**Padilla et al. (2018).** *Cognitive Research: Principles and Implications* 3, doi:10.1186/s41235-018-0120-9. A review that frames visual decision-making as dual-process, with no new data.

**What transfers.** All of this concerns *numeric* uncertainty. The Studio's belief strengths are ordinal (hard, radical, conservative, note). What carries over is the channel choice (MacEachren) and the warning against encodings with a hard edge, such as error bars, for graded quantities (Correll & Gleicher). The dotplot and HOP results do not transfer directly.

## 8. Epistemic diagrams and theory of mind

These exist; **none has been evaluated**:
- Kripke models and DEL event models: van Ditmarsch, van der Hoek & Kooi 2007, *Dynamic Epistemic Logic*, Springer Synthese Library 337, doi:10.1007/978-1-4020-5839-4. Baltag, Moss & Solecki 1998, TARK, http://tark.org/proceedings/tark_jul22_98/p43-baltag.pdf.
- DEMO, van Eijck's Haskell model checker (2007), which draws models.
- Hintikka's World: Schwarzentruber 2018, IJCAI demo, https://www.ijcai.org/proceedings/2018/862; Charrier et al. 2019, https://www.ijcai.org/proceedings/2019/0934.pdf. It shows each agent's possible worlds as comic panels, opened by clicking that agent.
- Talk of the Town: Ryan et al. 2015, EXAG workshop at AIIDE. I could not read the paper; I believe it has no user study.
- Teaching tools for logic.

I found no study comparing Kripke diagrams with any other way of showing nested belief, and no evaluated display of dramatic irony.

The one robust empirical anchor is about *people*, not displays. In the Sally-Anne task (Baron-Cohen, Leslie & Frith 1985, *Cognition* 21:37–46, https://docs.autismresearchcentre.com/papers/1985_BC_etal_ASChildTheoryOfMind.pdf), children who failed answered with where the marble *really* was (16/16 failures). The characteristic error in reasoning about false belief is substituting reality for the belief. A display can either invite that error or guard against it.

## 9. Annotation and marginalia

- **Marshall (1997).** "Annotation: from paper books to the digital library," ACM DL, doi:10.1145/263690.263806. An observational study of used textbooks, reportedly about 150 books (secondary). Annotations were varied and mostly readable by others, and some students sought out already-marked copies.
- **O'Hara & Sellen (1997).** "A comparison of reading paper and on-line documents," CHI, https://www.microsoft.com/en-us/research/wp-content/uploads/2016/08/reading-paper-and-online-97-.pdf. Ten participants summarised an article, five on paper and five on screen, analysed qualitatively. Paper let readers annotate while reading and lay pages out spatially. Annotation and window management on screen interrupted reading.
- **Abraham (2008).** *CALL* 21(3):199–226, doi:10.1080/09588220802090246. A meta-analysis of 11 studies of computer glosses in L2 reading. It reports a medium effect on comprehension (exact d unconfirmed) and large effects on incidental vocabulary (d ≈ 1.4 immediate; secondary).
- **Gloss position** (small L2 studies).
  - Marefat, Rezaee & Naserieh (2016, *JITE: Research* 15:479–501, n = 39) found in-text glosses gave lower load and better comprehension than marginal ones.
  - A 2016 *CALL* study (ERIC EJ1087607; authors unverified) found pop-up glosses scored **lowest** on all four of its tests.
  - I found **no study comparing footnotes, sidenotes and pop-ups for general reading.**
- **Dunlosky et al. (2013).** *PSPI* 14(1):4–58, doi:10.1177/1529100612453266. Rates highlighting as a study technique of **low utility**. This concerns learners highlighting for themselves, not a system highlighting for them.

## 10. Cognitive load and perception

**Split attention.**
- Chandler & Sweller (1991), *Cognition and Instruction* 8(4):293–332, doi:10.1207/s1532690xci0804_2. Six experiments: text and diagram integrated beat text and diagram kept apart, and non-essential text hurt even when integrated.
- Ginns (2006), *Learning and Instruction* 16(6):511–525, doi:10.1016/j.learninstruc.2006.10.001. Meta-analysis: **spatial contiguity d = 0.72 (k = 37)** and **temporal contiguity d = 0.78 (k = 13)**, larger for complex material.
- Schroeder & Cenkci (2018), *Educational Psychology Review* 30(3):679–701, doi:10.1007/s10648-018-9435-9: **g = 0.63** over 58 comparisons (n = 2,426).
- Mayer & Fiorella (2014), *Cambridge Handbook of Multimedia Learning* 2nd ed., doi:10.1017/CBO9781139547369.015. Median d: spatial contiguity 1.10 (22/22 tests), coherence 0.86, redundancy 0.86, signalling 0.41 (24/28). Most of these are short Mayer-lab lessons.
- Kalyuga, Chandler & Sweller (1999), *Applied Cognitive Psychology* 13(4):351–371. Colour-linking text to the diagram parts it names reduced split attention.

**Redundancy, with a caveat.** Adesope & Nesbit (2012), *Journal of Educational Psychology* 104(1):250–263, doi:10.1037/a0026147, pooled 57 studies. The overall effect was g = 0.15 in *favour* of redundant verbal material. "Redundancy hurts" holds for adding non-essential material. It does not hold for every duplicate.

**Channels.**
- Cleveland & McGill (1984), *JASA* 79(387):531–554, doi:10.1080/01621459.1984.10478080. Participants: 51 analysed. Accuracy ranks as position, then length, then angle, then area, then shading.
- Heer & Bostock (2010), CHI, doi:10.1145/1753326.1753357, replicated the ranking with crowd workers, 50 per chart.
- Munzner (2014), *Visualization Analysis and Design*, doi:10.1201/b17511, synthesises the literature. For categorical identity the channels are spatial region, then hue, motion and shape.

**Categorical colour.**
- Healey (1996), IEEE Visualization, doi:10.1109/VISUAL.1996.568118. With 38 observers, up to **7** carefully chosen colours supported fast, accurate search. Beyond that, some targets slowed.
- Haroz & Whitney (2012), TVCG 18(12):2402–2410, doi:10.1109/TVCG.2012.233. Finding an oddball degraded sharply as the number of categories grew in random layouts, and grouping removed most of the cost.

## 11. What the evidence supports for the Studio

Each recommendation carries a strength label:
- **Strong:** replicated controlled results.
- **Moderate:** one good study, or consistent indirect evidence.
- **Weak:** extrapolated from adjacent domains.
- **None:** design judgement; it needs a Studio user test.

**Argument graphs.**
- *Layout.* Lay out the defeasible-logic argument graph top-down and layered, with the conclusion at the top and supports and attacks below it.
  - Minimise crossings first. Keep each argument chain straight. Where crossings are unavoidable, make them near-perpendicular.
  - Do not bundle edges.
  - The Studio's graphs are small (under 20 nodes), which is where node-link beat matrices on path tasks (Ghoniem; Okoe).
  - Strength: strong for crossings, straight paths and angles (Purchase; Ware; Huang 2008); moderate against bundling (McGee & Dingliana); weak for "layered", which rests on trees (Burch 2011).
- *Edges.* Show direction by tapering, wide at the attacker or supporter. Distinguish attack from support with a second channel: solid against dashed, or a line-end mark. Do not layer several redundant direction cues; combining them gave no gain.
  - Strength: moderate (Holten & van Wijk 2009; Holten et al. 2011).
- *Labelling colours.* Show IN/OUT/UNDEC in three hues, well within Healey's limit of 7. Always pair each hue with a shape or text badge for colour-blind readers.
  - Draw UNDEC with a lightness or texture change rather than a third saturated hue. The MacEachren variables (fuzziness, transparency, value) read as "uncertain".
  - Use grounded semantics as the default: lay judgements match it at about 75–83%, as well as any other semantics (Cramer & Guillaume).
  - Rahwan et al. show readers only partly restore confidence in a reinstated argument. When an argument is IN *because* its attacker is OUT, say so on the node ("reinstated: X is defeated by Y") rather than leaving the reader to recompute it.
  - Strength: moderate for the semantics; weak for the colour choice.
- *Expectations.* Showing the graph next to the prose should help readers apply the semantics (Vesic et al.). It should not be expected to raise comprehension of the story itself: Dwyer et al. found map reading had no effect on comprehension, and Mardah et al. found no effect on interpretation.
  - Keep the graph collapsed by default and opened on a verdict, which the existing note already does.
  - Strength: moderate.

**Belief per character over time.**
- *The question decides the form.*
  - "What does each character believe now?" is a symbolic lookup, so use a characters × propositions table.
  - "When did Mara start believing p, and for how long?" is an interval question, so use one lane per character on a shared horizontal sequential axis, with a bar per belief interval. LifeLines-style lanes were about 2× faster on interval questions and equal on exact lookups. Horizontal lines are the shape readers find easiest to read.
  - Do not draw beliefs as a node-link graph; nothing in the evidence supports it for lookup.
  - Strength: strong for table versus lanes (Vessey; Alonso et al.; Di Bartolomeo 2020).
- *Change across paragraphs.* Show static small multiples or lanes, not animated transitions. Animation was less accurate and slower for analysis.
  - Strength: strong (Robertson; Archambault; Farrugia & Quigley).

**Nested beliefs ("A thinks B knows p").**
- There is no evidence for any display. Do not draw Kripke models. Nobody has tested them, and they grow with every agent and proposition.
- Render a nested belief as a short path of chips, A → B → p, inside A's row of the belief table. Add a per-character "through their eyes" toggle that re-renders the table as A models it. This borrows Hintikka's World's click-an-agent idea, which is also untested.
- Strength: none. This is the first thing to put in front of users.

**Evidence and trust provenance.**
- Show each belief's justification as a list next to its cell (seen, told by X, inferred), filtered to the selected belief. Unfiltered multi-relation views gave the same accuracy at far higher effort (Huang et al. 2009).
- Encode strength or attitude with lightness or transparency, possibly with fuzziness. Do not use hue, and do not use a hard-edged interval. Ordinal strengths should read as a gradient (MacEachren 2012; Correll & Gleicher 2014).
- Strength: moderate for filtering; weak for the channel, which comes from numeric and map uncertainty.

**False belief and dramatic irony.**
- Show the belief and the fact side by side in the same cell ("Mara: note is for Mara | actually: for Kiran"). Flag the mismatch with a channel used nowhere else in the panel, such as an outline or a mismatch glyph, plus text.
- This works against the error Sally-Anne exposes, substituting reality for the belief. The reader never has to hold the true state in mind to see the false one.
- In the per-character lanes, a false belief interval can be overlaid on the fact's interval. Mismatching bars are then visible geometrically, as in the LifeLines interval results.
- Strength: none for the display itself. The ground for it, that people confuse belief with reality, is strong but comes from developmental psychology.

**Bonds and affect over time.**
- Use word-sized line sparklines, one per directed pair, at least about 24 px tall, all on a shared y-scale, stacked as small multiples. Use split space (multiples) rather than one shared chart once there are more than 3–4 pairs and the questions span the whole story. A shared chart is fine for "what changed at this paragraph".
- Never animate.
- Strength: strong for small multiples over animation; moderate for the 24 px floor (Heer 2009); moderate for split versus shared (Javed 2010). Sparklines in running prose have no controlled evidence.

**Consent scenes.**
- Draw each consent scope as a lane on the scene's sequential axis:
  - a bar from given to withdrawn;
  - tick marks for check-ins;
  - limits as text labels on the bar;
  - withdrawal as a hard end cap plus the word "withdrawn".
- Exact state ("is X consented at paragraph 12?") must be readable as text. Tables matched graphics on exact lookups, and the one table win in Alonso et al. was a lookup needing a colour decoded. This is a case where misreading has real cost, so **never encode consent state by colour alone.**
- Strength: moderate (Alonso et al.; Healey; Vessey). Treating consent as safety-critical is a design judgement.

**Narrow layout (~700 px).**
- At this width the right panel is roughly 300–350 px.
  - Stack vertically.
  - Run time horizontally only within a card, using relative or sequential scales.
  - Keep matrices to about 6 characters × the propositions that changed.
  - Keep argument graphs top-down so depth uses the panel's height.
  - Sparklines at 24 px fit about ten pairs in a card.
- Below that height, switch to a two-band horizon chart or to text deltas.
- Collapse by default: clutter costs effort even where accuracy holds (Huang 2009).
- Strength: moderate. The sizes come from Heer 2009 and the collapse rule from Huang 2009; the rest is layout judgement.

**Annotation next to prose.**
- Keep the logic adjacent to the paragraph it explains and linked to it. Use hover-synced highlighting between the prose token and its card row, colour-linked as in Kalyuga et al. 1999. Do not put the logic on a separate page or tab.
  - Strength: strong. Spatial contiguity d ≈ 0.6–0.7 across two meta-analyses (Ginns 2006; Schroeder & Cenkci 2018). Signalling d ≈ 0.4 (Mayer & Fiorella).
- Do not repeat the prose in the panel. Show only what the logic adds, such as status, why, and deltas; non-essential duplicated text has hurt since Chandler & Sweller.
  - Strength: moderate, given Adesope & Nesbit's caveat.
- Prefer marginal cards to pop-ups for anything the reader must compare. Pop-ups hide the text they gloss and did worst in one gloss study. Hover cards are acceptable for one-off definitions.
  - Strength: weak (small L2 gloss studies; Abraham 2008; O'Hara & Sellen 1997 on annotation interrupting on-screen reading).
- Keep system highlighting in the prose sparse, marking only the token tied to the focused card.
  - Strength: weak (Dunlosky et al. concerns learner highlighting; Haroz & Whitney on oddball search with many categories).

**What to test first.** Nested-belief chips, the false-belief cell, and IN/OUT/UNDEC readability against prose-only explanations. These are the three places where the Studio's design rests on no evidence at all. Each can be tested in a small within-subjects study with comprehension questions as the outcome measure.
