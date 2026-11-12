# Logics for coherent long-form LLM stories: a literature review for `langlib`

*Status: research note, November 2026. Scope: the machinery that keeps a long, LLM-written story consistent. That covers who is where, who knows what, whether a character acts in character, and whether the timeline and causes hold together. The prose style and the content of the stories are out of scope.*

The proposed architecture has an LLM that proposes prose and events, a typed Lean layer that represents what the text asserts, and a checker that rejects or flags plot holes. Three lines of work bear on this. Narrative planning has spent 25 years formalising "a story is a causally coherent, character-motivated plan". Logic-based interactive narrative has built working story systems on linear logic, exclusion logic, and ASP. Recent LLM work measures how badly unconstrained models break consistency over long texts. Argumentation theory and non-monotonic logic answer the "timid people don't shout, unless..." question more directly than fuzzy logic does.

---

## 1. Narrative planning: stories as plans with motivated actors

**Classical roots.** Planning-based story generation started with TALE-SPIN (Meehan, 1977), in which characters plan to reach goals and the story is the trace. Later systems treat the story as a STRIPS/PDDL plan: actions have preconditions and effects over a world state. Causal coherence comes for free, because every action's preconditions are established by earlier steps or by the initial state. The shortcoming is that a plan only reaches the *author's* goal. Characters do things for no reason of their own.

**IPOCL (Riedl & Young).** [Narrative Planning: Balancing Plot and Character (JAIR 2010)](https://www.jair.org/index.php/jair/article/view/10669) extends partial-order causal-link planning with *intention frames*. Every character action must belong to a frame that explains which goal of *that character* it serves, and goals are adopted only through *motivating* steps (for example, the king orders the knight to rescue the princess). This is the first formal notion of "acting in character". An action is justified when a chain of causal links runs from a motivating event, through the character's adopted intention, to the action. The idea worth taking is that **motivation is a checkable structural property of the event graph** and does not need a vibes judgement.

**CPOCL and Glaive (Ware & Young).** CPOCL ([Ware & Young, AIIDE 2011](https://ojs.aaai.org/index.php/AIIDE/article/view/12432)) adds *conflict*: plans a character intends that fail or are thwarted. Glaive ([Ware & Young, AIIDE 2014](https://ojs.aaai.org/index.php/AIIDE/article/view/12715)) is a fast state-space planner for the same intentional and conflict semantics.

**Sabre (Ware & Siler).** [The Sabre Narrative Planner: Multi-Agent Coordination with Intentions and Beliefs (AAMAS 2021)](https://www.ifaamas.org/Proceedings/aamas2021/pdfs/p1698.pdf) is the current reference formalism. Characters have **arbitrarily nested, possibly wrong beliefs**, actions have belief-update effects, and every action must be *explained*. An action is explained when, in the acting character's own (possibly wrong) belief state, it belongs to a plan that achieves one of that character's goals. Beliefs are tracked without uncertainty: a character believes p or believes ¬p, never "0.7 p". This is the closest existing formal spec of "no plot holes" covering motivation and knowledge together. It descends from [Shirvani, Ware & Farrell's possible-worlds belief model for state-space narrative planning (AIIDE 2017)](https://ojs.aaai.org/index.php/AIIDE/article/view/12960). [Siler & Ware (AIIDE 2025)](https://ojs.aaai.org/index.php/AIIDE/article/view/36817) re-encode Sabre's formalism in ASP. It does not beat the specialised planner on speed, but it is far more compact and modular, which matters to someone who has written a clingo story engine.

**LLMs meet narrative planning.** [Senanayake & Ware (FDG 2025)](https://doi.org/10.1145/3723498.3723815) use LLMs as heuristics for a narrative planner. They are comparable to classical heuristics but not yet reliable. [Wang & Kreminski, "Can LLMs Generate Good Stories?" (IEEE CoG 2025)](https://arxiv.org/abs/2506.10161) benchmark LLMs against narrative-planning criteria. GPT-4-class models produce *causally sound* stories at small scale, while **character intentionality and dramatic conflict remain hard** and degrade with scale. That result is the empirical case for a symbolic intentionality checker.

**Takeaway for langlib.** Take Sabre's definition of an *explained action* (an action consistent with the actor's beliefs and serving one of the actor's goals) as the spec for motivation. Do not adopt a planner as the generator: the LLM proposes, and the formalism checks.

## 2. Logic-based interactive narrative

**Ceptre (Chris Martens).** [Ceptre: A Language for Modeling Generative Interactive Systems (AIIDE 2015)](https://ojs.aaai.org/index.php/AIIDE/article/view/12735) and Martens' thesis *Programming Interactive Worlds with Linear Logic* (CMU 2015) model a story world as a multiset of linear resources rewritten by rules, with *stages* for phase structure. Linear logic fits object continuity well: `has(kiran, key) ⊸ has(guard, key)` *consumes* the old fact, so a key cannot be in two pockets at once. Martens also shows that proofs/traces carry a causal structure (a partial order of rule applications), which is exactly the story's causal graph. An earlier, related line is Bosser, Cavazza & Champagnat's *Linear Logic for Non-Linear Storytelling* (ECAI 2010).

**Versu, Praxis, and exclusion logic (Evans & Short).** [Versu: A Simulationist Storytelling System (IEEE TCIAIG 2014)](https://ieeexplore.ieee.org/document/6656883) drives autonomous characters through *social practices* (a dinner party, a courtship) written in Praxis. Its logic is [exclusion logic (Evans, DEON 2010)](https://link.springer.com/chapter/10.1007/978-3-642-14183-6_13). State is a tree of facts in which `!` marks a slot that holds exactly one value: `kiran.location!garden` automatically excludes `kiran.location!hall`. That is the cheapest available way to get functional fluents (location, mood, relationship status) without frame axioms. In Versu, characters choose actions by *utility over their desires*. The social practice proposes the options and the character's personality weights them. That split between *available* and *preferred* actions is the right one for plausibility.

**Comme il Faut / Prom Week.** [McCoy et al., Prom Week (FDG 2013)](https://dl.acm.org/doi/10.1145/2509136.2509155) and *Social Story Worlds With Comme il Faut* (IEEE TCIAIG 2014) model "social physics". Characters have traits and statuses, and *influence rules* add or subtract weights toward social intents such as befriend, date, or embarrass. "Timid characters are unlikely to initiate a confrontation" is exactly a CiF microtheory rule with a negative weight. The rules are numerous, small, authored, and **additive**. The system shows that a large library of weighted defeasible rules can be authored and debugged in practice, and it also shows the cost: tuning weights is opaque.

**Talk of the Town (Ryan et al.).** [Toward Characters Who Observe, Tell, Misremember, and Lie (AIIDE EXAG 2015)](https://users.soe.ucsc.edu/~jor/publications/ryanToward.pdf) gives each NPC a *mental model* of other characters that is built by observation and gossip, decays, and can be corrupted. It is the best working example of a per-character knowledge base with *provenance*: how a character learned a fact, and from whom. That is what lets you check "how does she know that?"

**Story sifting.** Kreminski's Felt and Winnow (Kreminski, Dickinson & Mateas, *Winnow: A Domain-Specific Language for Incremental Story Sifting*, AIIDE 2021) query a story trace for patterns such as "betrayal after favour". This is the dual of checking. Once events are typed, a Datalog-style query layer gives "find all scenes where X was in Y's debt" for free.

**Event calculus and situation calculus.** The situation calculus (McCarthy & Hayes 1969; Reiter, *Knowledge in Action*, 2001) and the event calculus (Kowalski & Sergot 1986; Shanahan 1999; Mueller, *Commonsense Reasoning*, 2006/2014) solve the frame problem with circumscription or negation-as-failure. Mueller's [Understanding script-based stories using commonsense reasoning (Cognitive Systems Research, 2004)](https://doi.org/10.1016/j.cogsys.2004.06.002) fills gaps in restaurant stories with an event-calculus reasoner. Its lesson is that a story's *unstated* facts are where most of the inference work lies. The user's earlier OCaml/Clingo renderer sits here: event calculus as an ASP program with inertia via default negation. Section 8 explains what that approach got right and why the new setting is different.

**Story grammars.** Propp's *Morphology of the Folktale* (1928) gives 31 functions in a fixed partial order. Lakoff's *Structural Complexity in Fairy Tales* (1964/1972) rewrites Propp as a grammar. Rumelhart (1975) and Thorndyke (1977) wrote story grammars, and Black & Wilensky (1979) criticised them, arguing that grammars capture form and miss coherence, which comes from goals and causality. That critique still holds. A beat sheet or Propp sequence is a good *outline constraint* but not a consistency checker.

**Drama managers.** These systems steer an interactive story toward authorial goals. Examples are Weyhrauch's search-based drama management (1997), Façade's beat sequencer (Mateas & Stern 2005), and Riedl's Automated Story Director (2008), which repairs plans when players deviate. In langlib's setting the LLM plays the "player" whose deviations must be accommodated or rejected, and the *mediation* idea (detect that a proposed event breaks a causal link that a later plot point needs) applies directly.

## 3. Argumentation and non-monotonic reasoning: the plausibility core

The request `plausible(character(kiran, personality=timid), action(subject=kiran, op=shouts))` is a textbook default with exceptions. This is the strongest fit in the review.

**Default logic and non-monotonic reasoning.** [Reiter's default logic (AIJ 1980)](https://doi.org/10.1016/0004-3702(80)90014-4) writes `timid(x) : ¬shouts(x) / ¬shouts(x)`. If x is timid and it is consistent to assume x doesn't shout, conclude that. ASP's default negation (`not`) is the operational version. The user's clingo work already used this for inertia.

**Dung's abstract argumentation.** [Dung (AIJ 1995)](https://doi.org/10.1016/0004-3702(94)00041-X) abstracts away from rules. There is a set of arguments and an attack relation, and the semantics (grounded, preferred, stable) pick out acceptable sets. Its key result is that logic programming, default logic, and n-person games are all instances of this framework. **Grounded semantics** is unique, polynomial, and skeptical, which makes it the natural checker semantics.

**ASPIC+.** [Modgil & Prakken, The ASPIC+ framework for structured argumentation: a tutorial (Argument & Computation, 2014)](https://doi.org/10.1080/19462166.2013.869766) puts structure back. It has strict rules (→) and defeasible rules (⇒), arguments are trees of rule applications, and there are three kinds of attack: *undermining* a premise, *rebutting* a defeasible conclusion, and *undercutting* a defeasible rule's applicability. Undercutting is the key piece for stories. "Kiran is drunk" does not argue that Kiran shouts. It argues that *the timidity rule doesn't apply right now*. Preferences over rules (last-link, weakest-link) decide rebuttals.

**Defeasible logic.** Nute's defeasible logic, in the [Antoniou, Billington, Governatori & Maher formulation (ACM TOCL 2001)](https://doi.org/10.1145/371316.371517), has strict rules, defeasible rules, *defeaters* (rules that only block and never conclude), and a superiority relation. Its proof theory is a set of **inductive tagged-literal conditions** (+Δ, −Δ, +∂, −∂). Conclusions are computable in **linear time** (Maher 2001). Of everything in this review it maps most directly onto Lean: +∂p is literally an inductive predicate, a derivation is a proof term, and the checker is a decidable procedure with a soundness proof. Governatori's [SPINdle](https://github.com/gvdgdo/SPINdle) is a reference implementation.

**Value-based argumentation (Bench-Capon).** [Persuasion in Practical Argument Using Value-based Argumentation Frameworks (J. Logic & Computation, 2003)](https://doi.org/10.1093/logcom/13.3.429) attaches a *value* to each argument (safety, loyalty, pride, honesty), and each *audience* ranks values. An attack succeeds against an audience only if the attacked argument's value is not preferred. **This is a model of character.** A character's personality is a value ordering. Kiran-timid ranks `safety > self-assertion`, but `protect(friend) > safety`. "Would Kiran shout at the guard?" then becomes a question about the audience-specific grounded extension: the argument "shouting protects Mara" (value: loyalty) defeats "shouting is risky" (value: safety) *for this audience*. The same story then supports different verdicts for different characters with no numbers anywhere. Atkinson & Bench-Capon's practical-reasoning scheme AS1 ("in circumstance R, doing A achieves G, which promotes value V") is a ready-made template for *why a character acted*.

**Belief revision.** [AGM (Alchourrón, Gärdenfors & Makinson, JSL 1985)](https://doi.org/10.2307/2274239) gives postulates for revising a belief set by new information. It matters in two places: a *character's* beliefs when told something contradicting them, and the *story bible* when a retcon is accepted. For the checker, simple prioritized base revision is enough (newer and more reliable sources win).

## 4. Graded plausibility: fuzzy, probabilistic, weighted

**Fuzzy logic** (Zadeh 1965; t-norm logics such as Łukasiewicz and Gödel; Hájek, *Metamathematics of Fuzzy Logic*, 1998) assigns degrees of truth. It is the wrong tool for plausibility. Fuzziness models *vagueness* ("how tall is tall"), not *likelihood under exceptions*. Truth-functional combination of degrees also gives poor results: min(0.3 timid-shouts, 0.9 provoked) says nothing about the interaction. Fuzzy predicates *are* fine for genuinely graded traits ("somewhat timid"), but they can be discretised into an ordinal scale and fed to the defeasible layer as rule strength.

**Probabilistic logic programming.** [ProbLog (De Raedt, Kimmig & Toivonen, IJCAI 2007)](https://www.ijcai.org/Proceedings/07/Papers/396.pdf) attaches probabilities to facts and rules under the distribution semantics. [Markov Logic Networks (Richardson & Domingos, MLJ 2006)](https://doi.org/10.1007/s10994-006-5833-1) attach weights to first-order formulas. LP^MLN ([Lee & Wang, KR 2016](https://www.aaai.org/ocs/index.php/KR/KR16/paper/view/12844)) brings MLN-style weights into ASP, and Probabilistic Soft Logic ([Bach et al., JMLR 2017](https://jmlr.org/papers/v18/15-631.html)) is fuzzy-plus-weights with convex inference. All of them work, but they demand numbers nobody can justify ("P(timid person shouts | provoked) = 0.35"). Inference is #P-hard in general, and the answers are hard to explain to the author.

**Weighted ASP / weak constraints.** Clingo's `:~` weak constraints with priority levels give *lexicographic* soft preferences. This is the pragmatic middle ground: "prefer stories where no character acts against their top value (level 3); then minimise unexplained actions (level 2); then minimise coincidences (level 1)". Priority levels are ordinal, so no fake probabilities are needed. The user already knows this tool.

**LLM-as-judge.** LLMs have broad commonsense about what people plausibly do, and no formal system will match their coverage. They are also inconsistent across calls, sensitive to position and wording, and, per FlawedFictions (§7), *barely above chance* at spotting plot holes. The sensible role is a **fallback oracle for what the ontology doesn't cover**, asked narrow, structured questions (yes/no plus a cited justification), with answers *cached as facts* so the same question gets the same answer.

**Verdict.** Use ordinal and defeasible methods for character plausibility, and weak constraints for ranking. Skip fuzzy and probabilistic logic unless calibrated data later shows up.

## 5. Epistemic state: who knows what

**Dynamic epistemic logic.** DEL ([van Ditmarsch, van der Hoek & Kooi, *Dynamic Epistemic Logic*, 2007](https://doi.org/10.1007/978-1-4020-5839-4); Baltag, Moss & Solecki's action models, 1998) models public announcements, private observations, and lies as updates to Kripke models. It handles exactly the cases a story needs: Mara sees Kiran pocket the letter, but the guard doesn't; Kiran *believes* the guard didn't see. Epistemic *planning* in DEL ([Bolander & Andersen, J. Applied Non-Classical Logics 2011](https://doi.org/10.3166/jancl.21.9-34)) is undecidable in general and decidable for restricted action models.

**Practice.** Sabre and Talk of the Town both avoid full Kripke models. They use **per-agent belief states with bounded nesting** (Sabre allows arbitrary nesting but is explicit about it). For checking a story, what matters is mostly depth 1 ("does Kiran know p?") and depth 2 ("does Kiran think Mara knows p?"). Dramatic irony is a depth-0-versus-depth-1 gap: the reader (or narrator) knows p, and the character does not. Suspense is a reader-uncertainty gap (Cheong & Young's *Suspenser*; [Bae & Young's flashback/foreshadowing work](https://www.researchgate.net/publication/220920067_A_Use_of_Flashback_and_Foreshadowing_for_Surprise_Arousal_in_Narrative_Using_a_Plan-Based_Approach)). A good model is an *observation-based* update: everyone co-located with a perceptible event learns it, speech transfers belief with provenance, and nothing else changes beliefs. That catches the commonest LLM knowledge error, a character referring to something they never witnessed or were told.

## 6. Scene and story representations

- **Story Intention Graph** ([Elson, *Modeling Narrative Discourse*, Columbia PhD 2012](https://academiccommons.columbia.edu/doi/10.7916/D8BG2W7W); DramaBank, LREC 2012). It has three layers: the textual layer (spans), a timeline layer of propositions, and an *interpretive* layer of goals, plans, and beliefs with relations such as *actualizes*, *ceases*, *wouldPrevent*, and *attemptToCause*. This is the most langlib-shaped existing representation. It ties text spans to propositions and propositions to agent intentions, and it was designed to be annotated over real prose.
- **Labov & Waletzky (1967)** give the parts of a narrative: abstract, orientation, complicating action, evaluation, resolution, coda. Evaluation (why it matters to the teller) is a useful *scene-function* tag.
- **Ontologies.** [OntoMedia](https://www.researchgate.net/publication/221024283_OntoMedia_An_Ontology_for_the_Representation_of_Heterogeneous_Media) (Jewell et al. 2005) covers events, entities, and timelines in media. [Drammar](https://doi.org/10.1007/978-3-030-00668-6_9) (Lombardo, Damiano et al., ISWC 2018) covers agents, plans, units, and conflicts in drama. Both are worth mining for vocabulary, and neither should be adopted wholesale, since OWL open-world semantics is the wrong default for a checker.
- **Scene graphs** ([Johnson et al., CVPR 2015](https://doi.org/10.1109/CVPR.2015.7298990)) are object/attribute/relation graphs. A scene's spatial state (who is in the room, what is on the table) is exactly a scene graph and is the right granularity for location continuity.
- **Beat sheets** (Snyder, *Save the Cat*, 2005; Truby, *The Anatomy of Story*) are outline-level structure. They are good as soft constraints at the act level ("the midpoint must reverse the protagonist's belief about X") and useless for local consistency.
- **Verb-frame lexicons.** VerbNet, PropBank, and FrameNet are not narrative work, but they sit underneath everything else. They supply typed thematic roles (Agent, Patient, Theme, Destination) and, in VerbNet's case, **event-structure semantics with preconditions and results** ([Brown et al., "VerbNet representations: subevent semantics" 2019](https://aclanthology.org/W19-3318/)). VerbNet's `has_location(e1, Theme, Initial_Location) ... has_location(e3, Theme, Destination)` is a STRIPS operator. This is the bridge from langlib's parts-of-speech layer to events.
- **Type-theoretic NL semantics.** Bekki's [Dependent Type Semantics](https://www.lirmm.fr/tytles/Articles/Tanaka.pdf) handles anaphora and presupposition as dependent-type obligations: "the key" type-checks only if a key is in context. Chatzikyriakidis & Luo implement [natural language inference in Coq](https://dl.acm.org/doi/10.1007/s10849-014-9208-x) with Modern Type Theory and coercive subtyping. These are the formal-semantics precedent for "references are typed and must resolve".

## 7. LLM long-story coherence

**Hierarchical generation.** Plan-and-Write ([Yao et al., AAAI 2019](https://arxiv.org/abs/1811.05701)) generates a storyline and then the story. Re3 ([Yang et al., EMNLP 2022](https://arxiv.org/abs/2210.06774)) runs plan, draft, rewrite, and edit, with a *rewrite* module that reranks continuations for coherence and an *edit* module that detects contradictions against a structured character-attribute store. DOC ([Yang et al., ACL 2023](https://arxiv.org/abs/2212.10077)) uses a detailed hierarchical outline plus a controller that keeps passages on-outline. Dramatron ([Mirowski et al., CHI 2023](https://arxiv.org/abs/2209.14958)) generates title, characters, and plot, then scenes, then dialogue, and shows that hierarchical prompting maintains coherence for co-writing. The common lesson is that **a persistent structured state beats a long context**. Each system invented an ad hoc state, and langlib can make it typed.

**Hybrid systems.** [StoryVerse (Wang, Zhou & Ledo, FDG 2024)](https://arxiv.org/abs/2405.13042) has authors write *abstract acts* (preconditions plus high-level conflict), and an LLM "act director" produces character action sequences against a world state. [Wang & Kreminski (Wordplay @ ACL 2024)](https://arxiv.org/abs/2406.00554) use a small ASP program to generate diverse outlines that the LLM then realises. This is the closest published analogue to the user's clingo renderer combined with an LLM. [ConWriter (Li et al., Findings of EMNLP 2026)](https://arxiv.org/abs/2608.05169) does scene-level stateful generation with *symbolic transition checking* and localised repair before errors propagate. Architecturally it is nearly the proposed langlib loop, minus types and proofs.

**Benchmarks.**
- [FlawedFictions (Ahuja, Sclar & Tsvetkov, 2025)](https://arxiv.org/abs/2504.11900) builds a benchmark of Gutenberg stories with injected plot holes. o3-mini reaches about 63% and Qwen2.5-32B about 53% against a 50% baseline. LLM-written and LLM-summarised stories contain 50–100% more plot holes than human originals. **LLMs are poor plot-hole detectors and active plot-hole producers.**
- [ConStory-Bench, "Lost in Stories" (ACL Findings 2026)](https://arxiv.org/abs/2603.05890) has 2,000 prompts for 8–10k-word stories, a taxonomy of 5 categories and 19 subtypes of consistency error (timeline, character, world facts, and so on), and a checker that extracts errors, pairs contradictions, and builds evidence chains. Its taxonomy is a good test-suite spec for langlib.
- [NCP-Bench (Ma et al., ICML 2026)](https://arxiv.org/abs/2608.08160) tests interactive narratives under adversarial user turns. Fact-conflict rates run from 40% to 68%, and the best model holds the script only 42% of the time after 20 turns.
- [NarraBench (Hamilton et al., EACL 2026)](https://arxiv.org/abs/2510.09869) surveys narrative-understanding benchmarks.

Together these are the motivation. Unaided LLMs neither keep nor detect consistency at length, and the published fixes are all "keep explicit state and check transitions".

## 8. Narrative in proof assistants and type theory

The prior art is thin. [Bosser, Courtieu, Forest & Cavazza, Structural Analysis of Narratives with the Coq Proof Assistant (ITP 2011)](https://link.springer.com/chapter/10.1007/978-3-642-22863-6_7) encode narratives as intuitionistic linear logic sequents, read stories off cut-free proofs, and prove second-order properties *over all proofs* (all possible stories) in Coq. Martens' Ceptre work relies on the same proofs-as-traces correspondence. The type-theoretic semantics line (DTS, MTT-in-Coq, and [dependently typed event calculi of telicity, 2025](https://arxiv.org/abs/2506.06968)) formalises sentence meaning, not story state. As far as this review could find, **nobody has built a dependently typed story-state checker driven by an LLM**, so langlib would be new here.

**Contrast with the earlier ASP/event-calculus renderer.** That system went *symbol → text*. Clingo found a model of the event calculus, and the renderer verbalised it, so consistency held by construction and the hard problem was surface realisation. langlib goes *text ↔ symbol*. The LLM writes, and the formal layer has to *extract* what was asserted before it can check it. Three things follow:
1. **The extraction step is the weak link.** A perfect checker over a bad parse proves nothing.
2. Prose asserts *partial* information. "She slipped out" does not say where she went, so the state needs explicit unknowns, which closed-world ASP doesn't want.
3. Checking a *given* trace is far cheaper than *searching* for one, so the decidable-in-Lean fragment can be much richer than what was practical as an ASP generator.

---

## Recommended design for the langlib story layer

The core opinion: **use three logics in strict layers, not one clever logic.** Mixing hard continuity with soft plausibility in a single formalism (everything in weighted ASP, or everything fuzzy) makes failures unexplainable. Each layer has its own verdict type.

### Layer 0: text to typed events (the bridge)

- Verbs map to **event schemas with typed thematic roles**, seeded from VerbNet/PropBank. Each schema has `pre : State → Prop` and `post : State → State`, written STRIPS style. VerbNet subevent semantics already supply most of these.
- Noun phrases map to **entity references that must resolve** against the scene's entity context, in the DTS spirit: an unresolved definite description ("the key") is a *type error*, not a warning.
- **Generate the event first, then the prose.** The LLM emits a structured `Event` and then realises it. A second, independent extraction pass parses the prose back into events and diffs them against the first. Disagreement means the prose says something the event doesn't, so the step is rejected or re-extracted. This round trip is the only cheap defence against the extraction problem.

### Layer 1: hard invariants, decided in Lean

This layer covers location, possession, alive/dead, physical capability, timeline order, and knowledge.

- State is a record of **functional fluents** (exclusion-logic style: `location : Char → Option Place`, `holder : Obj → Option Holder`) plus **per-character belief sets with provenance**, bounded to depth 2 (Sabre-lite). `Option`/`unknown` is explicit, because prose is partial.
- Knowledge updates are observation-based: co-located perceivers learn perceptible effects, and speech transfers beliefs with a `source` tag. Checking "does X mention only what X knows?" is then decidable set membership.
- Timeline is a partial order of events (Ceptre/POCL causal order), with absolute timestamps optional. The check is acyclicity plus consistency with stated durations, using a small difference-constraint solver, which is decidable and certifiable.
- Every check is a `Decidable` instance with a soundness lemma against an inductive spec. A *story fact* (`knows kiran (location letter drawer) at t7`) is a Lean proposition proven by the derivation through the events, which provides the requested "Lean derivations of facts".
- Verdict: `ok` or `violation (which precondition, which earlier event established the contrary)`.

### Layer 2: character plausibility as defeasible, value-based argumentation, also in Lean

- Use **defeasible logic (Nute/Governatori) with a value-based superiority relation (Bench-Capon)**. Personality is a *value ordering* plus a handful of trait facts, and archetype rules are defeasible. Situational facts act as **defeaters** in the undercutter sense.
- Defeasible logic proof theory is inductive and linear-time, so +∂/−∂ go in Lean as inductive predicates with a verified evaluator. An accepted action comes with an **argument tree** that can be shown to the author ("Kiran shouted *because* Mara was threatened; loyalty > safety for Kiran").
- **Motivation (IPOCL/Sabre explained actions)** belongs here. A significant action needs a link to a goal the actor holds in their *own* belief state. Where none exists, the result is `unexplained` rather than `inconsistent`.
- Verdict: `plausible proof | implausible counterargument | unexplained`. An implausible or unexplained action is not banned. It creates a **justification debt**: the LLM must either revise the action or add, *earlier or in the same scene*, a fact that defeats the blocking argument (a provocation, a drink, a threat). This turns "out of character" into a repair task with a precise target. Real stories have characters act against type, but they *pay for it in setup*.

### Layer 3: graded preference, offloaded

- **Clingo weak constraints** rank candidate continuations and outlines, and handle *search* tasks: "what minimal setup fact would discharge this debt?" or "generate 5 outline variants satisfying the beat sheet". Results come back as concrete facts and events, and Lean *re-checks* them, so clingo is an untrusted oracle with checked certificates.
- The **LLM judge** handles what the ontology cannot express: tone, subtext, whether an unmodelled action is physically or socially sane. It answers narrow yes/no questions with cited spans, and answers are cached as facts with `source := llm_judge` so they are defeasible and auditable. The judge is never the last word on anything Layer 1 can decide.
- **No fuzzy logic.** Graded traits ("very timid") map to an ordinal strength that feeds rule superiority.

### What is decided where

| Concern | Logic | Where | Decidable? |
|---|---|---|---|
| Reference resolution | dependent typing (DTS-style) | Lean elaborator | yes |
| Location/possession/alive | functional fluents, STRIPS pre/post | Lean `Decidable` | yes |
| Timeline | partial order + difference constraints | Lean (certified solver) | yes |
| Who-knows-what (depth ≤ 2) | observation-based belief sets | Lean | yes |
| In-character action | defeasible logic + value ordering | Lean (verified evaluator) | yes, linear time |
| Motivation (explained actions) | IPOCL/Sabre intention links | Lean check; ASP to *find* links | check yes, search offloaded |
| Repairs, outline search, ranking | ASP with weak constraints | clingo, Lean re-checks | offloaded |
| Tone, subtext, unmodelled commonsense | — | LLM judge, cached | no |

### Worked example (pseudo-Lean)

```lean
-- Layer 0: verb frame → typed event
inductive Op | shout (at : Char) | give (o : Obj) (to : Char) | walk (to : Place) ...
structure Event where
  agent : Char
  op    : Op
  time  : Time
  span  : TextSpan            -- provenance into the prose

-- Layer 2: personality as values + traits
inductive Value | safety | loyalty | pride | honesty
structure Persona where
  traits : List Trait                   -- [.timid]
  prefers : Value → Value → Prop        -- strict partial order
  [dec : DecidableRel prefers]

def kiran : Persona :=
  { traits := [.timid],
    prefers := fun a b => (a, b) ∈ [(.loyalty, .safety), (.safety, .pride)] }

-- Defeasible theory: rules carry the value they promote/protect.
inductive Rule
  | strict    (name) (body : List Lit) (head : Lit)
  | defeasible(name) (body : List Lit) (head : Lit) (val : Value)
  | defeater  (name) (body : List Lit) (blocks : RuleName)   -- undercutter

def rules : List Rule := [
  .defeasible `timidQuiet  [.trait c .timid]                 (.neg (.does c (.shout _))) .safety,
  .defeasible `protect     [.threatens x y, .ally c y, .present c] (.does c (.shout x))   .loyalty,
  .defeater   `drunk       [.drunk c]                         `timidQuiet,
  .strict     `gagged      [.gagged c]                        (.neg (.does c (.shout _)))
]

-- superiority derived from the persona's value order (value-based argumentation)
def sup (p : Persona) (r₁ r₂ : Rule) : Prop := p.prefers r₁.val r₂.val

-- +∂ as an inductive predicate (Governatori et al. 2001), evaluator proven sound
inductive DefProv (T : Theory) (S : State) : Lit → Prop | ...
instance : Decidable (DefProv T S l) := ...   -- linear-time evaluator + soundness proof

inductive Plausibility (e : Event)
  | plausible   (pf : DefProv T S (.does e.agent e.op))
  | unopposed                                  -- no rule says anything: ask Layer 3
  | implausible (counter : DefProv T S (.neg (.does e.agent e.op)))
```

Three scenes run through this theory:

1. **Scene 3, the market.** The LLM proposes `kiran shouts at merchant`. State: `trait kiran timid`, no threat, not drunk. `timidQuiet` fires (safety) and nothing defeats it, so the verdict is `implausible counter=timidQuiet`. The orchestrator returns a *justification debt*: "Kiran is timid (rule timidQuiet, value safety). Either revise the action, or establish a defeater: drunk, or a threat to an ally (protect, loyalty > safety)."
2. **Scene 7, the gate.** Earlier in the scene the event `guard grabs mara` was checked, and Layer 1 derives `threatens guard mara`. `ally kiran mara` is in the story bible and `present kiran` holds. Both `timidQuiet` (safety) and `protect` (loyalty) fire. `kiran.prefers loyalty safety`, so `protect` wins, and the verdict is `plausible`. The proof term is the argument "loyalty overrides safety", which the UI can show and which a later scene can cite ("Kiran surprised herself at the gate").
3. **Scene 9.** `gagged kiran` holds, so the strict rule wins whatever the values are, and the proposal "Kiran shouts" is a hard error. Strict rules always beat defeasible ones, which is exactly the Layer 1 versus Layer 2 boundary.

The same machinery handles knowledge. If the LLM writes Kiran saying "the letter is in the drawer", Layer 1 needs `Believes kiran (in letter drawer)` with a provenance chain (she was present at `hide letter drawer`, or someone told her). Without one the line is rejected as a knowledge leak, a plot-hole class FlawedFictions and ConStory both list.

### Build order

1. Event schemas plus functional-fluent state plus Layer 1 checks on hand-written event traces. No LLM yet, and use ConStory's taxonomy as the test list.
2. The round-trip extraction harness (event → prose → re-extracted event → diff), which measures the weak link.
3. The defeasible evaluator in Lean with a soundness proof, and personas as value orderings.
4. The clingo bridge for repair search, then the LLM judge with caching.

Skip fuzzy logic, MLNs, and full DEL until a concrete story failure needs them.
