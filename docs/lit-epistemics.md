# Evidence, sources and trust: a literature review for StoryLangLib's minds

*Status: research note, November 2026. Scope: how characters (and the texts that describe them) weigh evidence, sources and trust, and what that means for `LangLib/World/Mind.lean`. Companion to `lit-story-logic.md` (section 5, epistemic state) and `lit-linguistic-encoding.md`.*

## 0. Where we are, and what is wrong with it

`Mind.lean` gives every belief a `Source` (`seen | told c`). Characters close their beliefs under Horn lore, and `mindsConsistent` can be required as an invariant. Revision follows one fixed rule for every character: **seeing beats hearsay**. `see` overwrites whatever it contradicts and drops clashing hearsay. `hear` is rejected if it contradicts anything seen or would make the view inconsistent. Either way the hearer records `bel d b`, "d claims b".

That rule is a reasonable default, but it is wrong in four ways the literature makes precise:

1. **Two sources are not enough.** Every evidential system in the world distinguishes more than two kinds of source. Inference, other senses, second-hand report and rumour all behave differently.
2. **Hearsay is all one thing.** Testimony from a trusted sister and testimony from a known liar get the same treatment. Testimony between two speakers is never weighed: hearing *q* from your mother after hearing *¬q* from a stranger is rejected only if it clashes with the view, and if it doesn't clash the newer one simply wins.
3. **The policy is the same for everyone.** Gullible, skeptical and paranoid characters behave identically. So do characters who are motivated to believe something.
4. **Revision loses information.** `add` and the filter in `see` *delete* beliefs. If the evidence that defeated them is later itself defeated, those beliefs cannot come back. Darwiche & Pearl showed this is exactly what goes wrong with iterated revision.

The lexicon has a related bug. `mindLex` maps *claim* and *swear* to `lie`. In English *claim* marks the reporter's distance from the content, not its falsity, and *swear* marks strong commitment.

## 1. The linguistics of evidence

### 1.1 Evidentiality: grammaticalised source

Willett's survey ([*Studies in Language* 12, 1988](https://doi.org/10.1075/sl.12.1.04wil)) defines evidentiality as the grammatical coding of the speaker's source of information, and gives the standard taxonomy:

- **Direct (attested):** visual, auditory, other sensory.
- **Indirect, reported:** second-hand ("X told me"), third-hand / hearsay, folklore ("it is said").
- **Indirect, inferring:** from *results* (visible traces), or from *reasoning* (assumption, general knowledge).

Aikhenvald's typology of 500+ languages ([*Evidentiality*, OUP 2004](https://academic.oup.com/book/51161)) refines this into six recurring semantic parameters: **visual, non-visual sensory, inference (from visible results), assumption (from reasoning/general knowledge), hearsay (unnamed source), quotative (named source)**. Systems range from two terms (firsthand vs non-firsthand) to five or more (Tariana, Tuyuca).

Two typological facts matter for us:

- **Hierarchies exist but are defeasible.** Where several evidentials could apply, languages show a preference roughly like *visual > non-visual sensory > inferential > assumed > reported*. Aikhenvald stresses that this is a preference for *marking*, not a fixed trust ranking. Many cultures treat a named elder's report or a myth (quotative/folklore) as authoritative, and inference from fresh traces can outrank a vague glimpse. The hierarchy is a **default prior**, not a law. That is exactly the status "seeing beats hearsay" should have.
- **Quotative vs hearsay.** A named source (*Mara said*) is a different evidential from an unnamed one (*they say, apparently*). The first can be weighted by trust in Mara. The second cannot be weighted by anyone, so it has to be weighted by the hearer's general gullibility.

The semantics literature splits on what evidentials contribute. Faller ([Cuzco Quechua, 2002](https://research.manchester.ac.uk/en/publications/semantics-and-pragmatics-of-evidentials-in-cuzco-quechua/)) and Murray ([Cheyenne; "A Hamblin semantics for evidentials"](https://www.semanticsarchive.net/Archive/2I5ZjdmY/Murray_A-Hamblin-Semantics-for-Evidentials.pdf)) argue that the reportative is **not-at-issue**: *p-si* ("p, reportedly") does not commit the speaker to *p* at all, only to having heard it. That is precisely the gap between `bel d b` ("d claims b") and `b`. The direct evidential *-mi*, in contrast, adds a sincerity condition that the speaker witnessed it. **For us:** a report updates the *claim* layer unconditionally and the *content* layer only conditionally on trust. The current code already does this, and it is the part worth keeping.

### 1.2 English lexical evidentials

English has no grammatical evidentials but a rich lexical stock, which the verb lexicon should read:

| Marker | Evidential type | Commitment of the *reporter* (narrator/speaker) |
|---|---|---|
| *saw / watched / noticed / spotted that p* | visual, direct | factive: p true |
| *heard / smelled / felt* + NP or gerund (*heard the door slam*) | non-visual sensory | factive |
| *heard that p* | **reportative**, not sensory | non-factive |
| *apparently, evidently, clearly, it seems/looks like* | inferential from results (sometimes reportative: *apparently* is ambiguous) | weak/none |
| *must (have)* | inferential | strong but indirect (see 1.4) |
| *might, may, could, perhaps* | assumption, low strength | none |
| *supposedly, allegedly, reportedly, they say, word was, rumour had it* | hearsay (unnamed) | none, often distancing |
| *X said / told / claimed / insisted / swore that p* | quotative (named) | none (*claim*: distancing) |
| *X admitted / confessed that p* | quotative, against interest | factive-leaning (presupposes p) |
| *X lied that p / lied about p* | quotative | anti-factive: narrator asserts ¬p |

Note *heard*. "Kiran heard the glass break" is sensory evidence, but "Kiran heard that the glass broke" is hearsay. The parser's complement vs object distinction (`c.comp` vs `c.obj`) is enough to separate them.

### 1.3 Factivity and presupposition

Kiparsky & Kiparsky's "Fact" (1970) separates **factive** predicates (*know, realise, discover, regret, notice, find out, remember that*) from **non-factive** ones (*believe, think, suppose, claim, say, assume, suspect, fear*). Factives presuppose the truth of their complement, and the presupposition **projects**: "Mara didn't realise the letter was gone" still commits the *narrator* to the letter being gone. The projection literature ([Simons, Tonhauser, Beaver & Roberts, "What projects and why", SALT 20](https://doi.org/10.3765/salt.v20i0.2584)) treats this as not-at-issue content tied to the question under discussion. Karttunen's implicatives (*manage to, forget to*) are the same kind of trigger.

For a checker this is a gift. A factive verb **makes two claims**: (a) the subject believes *p*, and (b) the text asserts *p* is true in the world. So "Kiran knew the letter was in the office" can be checked twice: against `Truth w φ`, and against Kiran's view, with an evidence path. Each check catches a different LLM error. The first catches a narrator contradicting the world. The second catches the *knowledge-leak* error, where a character "knows" something they never saw, heard or could infer. Non-factive verbs make only claim (a).

### 1.4 Epistemic modals

Kratzer's modal semantics ([*Modals and Conditionals*, OUP 2012](https://doi.org/10.1093/acprof:oso/9780199234684.001.0001)) relativises *must/might* to a **modal base** (what is known) and an **ordering source** (what is normal or expected). *Must p* holds when *p* is true in all the best-ranked worlds compatible with the evidence. That is a plausibility ordering, structurally the same object as the plausibility models in section 4. Von Fintel & Gillies ([*Must ... stay ... strong!*, NLS 2010](https://link.springer.com/article/10.1007/s11050-010-9058-2)) argue that *must* is not weak. It is strong but **presupposes indirect evidence**, which makes it an English inferential evidential: "the butler must have done it" is infelicitous if you watched him do it. Rodenhäuser's thesis (section 4) interprets epistemic modals directly as **dynamic attitudes**, that is, as upgrade operators. This gives us the bridge from words to revision operators: *must p* → inferred, radical; *might p* → assumed, conservative or merely entertained.

### 1.5 Perspective, free indirect discourse, unreliable narrators

Narrative adds a layer that conversation lacks: **whose** commitment is it? In **free indirect discourse** ("Of course the letter was in the office. Where else would Theo have put it?") a past-tense, third-person sentence expresses a *character's* belief, not the narrator's (Banfield, *Unspeakable Sentences*, 1982; [overview](https://en.wikipedia.org/wiki/Free_indirect_speech)). Signals include evaluative words, questions and exclamations, deictics anchored to the character (*now, here, tomorrow* with past tense), and epithets in the character's voice. A Booth-style **unreliable narrator** (*The Rhetoric of Fiction*, 1961) is the limiting case: the whole narration is one agent's belief state.

Zunshine ([*Why We Read Fiction*, 2006](https://philarchive.org/archive/ZUNEPC)) builds on Cosmides & Tooby's ["Consider the source"](https://www.cep.ucsb.edu/wp-content/uploads/2023/05/metarep.pdf). Her argument is that readers store fictional content with **source tags** ("Mara believes / Mara said / the narrator asserts"), and that much of the pleasure of fiction is managing those tags. Source tags in her sense are our `Held.src`, and her point is that readers keep them on *narrator* content too.

**For us:** every extracted proposition needs an *attribution*: the narrator, or a focalising character. Only narrator-attributed, at-issue or factive content is checked against `Truth`. Character-attributed content (FID, *thought that*, reportative adverbs) is checked only against that character's view.

## 2. The philosophy of testimony

The [SEP entry on testimony](https://plato.stanford.edu/entries/testimony-episprob/) lays out the central debate.

- **Reductionism** (Hume, *Enquiry* §X): testimony is justified only by the hearer's independent, inductive evidence that this kind of speaker is reliable. *Global* reductionists ask about testimony in general, *local* reductionists about this speaker on this topic (E. Fricker 1994). Hume's miracles argument is the classic credibility-limited move: reject a report when its falsehood would be less surprising than its truth.
- **Anti-reductionism** (Reid's twin principles of veracity and credulity; Coady, *Testimony*, OUP 1992; Burge's acceptance principle): testimony is a basic source. A hearer is entitled to accept it *unless there are defeaters*.
- **Epistemic vigilance** ([Sperber et al., *Mind & Language* 2010](https://onlinelibrary.wiley.com/doi/abs/10.1111/j.1468-0017.2010.01394.x)): the empirical middle ground. Hearers default to trust but run cheap checks on **competence** (could the speaker know?), **benevolence** (does the speaker want me to know?) and **content coherence** (does it fit what I already believe?).
- **Credibility and injustice** (Miranda Fricker, [*Epistemic Injustice*, OUP 2007](https://doi.org/10.1093/acprof:oso/9780198237907.001.0001)): hearers assign a *credibility level* to speakers, often driven by prejudice. A "credibility deficit" is a testimonial injustice. For fiction this is a feature: characters who wrongly disbelieve the servant, the child or the outsider drive many plots.

**What this implies.** There is no single right policy, and the literature is effectively a menu of character types. A Reidian character accepts unless defeated. A Humean character accepts only with a track record. A vigilant character checks competence (was the speaker *there*?), benevolence (trust and tension bonds), and coherence (entrenchment of what they already believe). All three checks can be decided from data we already have: `loc` histories for competence, `HasBonds` for benevolence, the view for coherence. Fricker's prejudice is a speaker-class bias term in the same weighting.

## 3. Formal belief change

**AGM** ([Alchourrón, Gärdenfors & Makinson, JSL 1985](https://doi.org/10.2307/2274239); [SEP](https://plato.stanford.edu/entries/logic-belief-revision/)) axiomatises revision *K \* p* for deductively closed sets, with **success** (*p ∈ K\*p*) and minimal change. It is characterised by *epistemic entrenchment* or by a plausibility ordering of worlds (Grove spheres). Entrenchment is exactly the "how attached is the character to this belief" parameter.

**Iterated revision.** AGM says nothing about the *next* revision. [Darwiche & Pearl (AIJ 1997)](https://dl.acm.org/doi/abs/10.1016/S0004-3702(96)00038-0) revise the *epistemic state* (the ordering), not just the belief set, and add postulates C1–C4 that preserve conditional beliefs. Three canonical operators differ in how much the ordering moves: **natural** (Boutilier: minimal; only the best *p*-worlds move to the top), **lexicographic** (Nayak: all *p*-worlds go above all ¬*p*-worlds) and **restrained** (Booth & Meyer). The engineering lesson is to **keep the ranked base and compute the view, never delete**. Spohn's ranking functions (*The Laws of Belief*, OUP 2012) give the integer-valued version of this, which is what a decidable implementation should use.

**Non-prioritised revision** drops *success*. Hansson's [survey](https://link.springer.com/article/10.1023/A:1005534223776) covers *screened* revision (some beliefs are immune), *semi-revision* (add, then consolidate, possibly discarding the input) and **credibility-limited revision** ([Hansson, Fermé, Cantwell & Falappa, JSL 2001](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/credibility-limited-revision/17FF52DB0AFBAD9D315B8F49B02D8316); propositional version [Booth, Fermé, Konieczny & Pino Pérez, KR 2012](https://aaai.org/proceeding/01-kr12/)). In credibility-limited revision an input is accepted iff it belongs to a set *C* of credible sentences, and otherwise the state is unchanged. Our `hear` is a crude credibility-limited operator whose *C* is "consistent with what I saw". The right generalisation is to make *C* depend on the source and on the hearer.

**Trust-sensitive revision.** Booth & Hunter, ["Trust as a precursor to belief revision"](https://jair.org/index.php/jair/article/view/11186) (JAIR 61, 2018), make trust **domain-relative**. Each source gets a partition of states it can distinguish (its expertise), and a report is weakened to the cell of that partition before revising. A doctor's report about the patient is trusted; her report about the weather is coarsened to nothing. They also show trust-sensitive revision is **manipulable**: sources can profit from misleading. Liau's BIT logic ([AIJ 149, 2003](https://homepage.iis.sinica.edu.tw/pages/liaucj/publications_en.html)) has the axiom pattern *B_i I_j p ∧ T_ij p → B_i p*: if *i* believes *j* informed it of *p*, and *i* trusts *j* on *p*, then *i* believes *p*. That is exactly a Horn rule over our `bel d b` claims, with trust as an extra premise. It slots straight into lore-style closure.

**Merging with source reliability.** When several sources disagree, belief merging ([Konieczny & Pino Pérez, JLC 2002](https://plato.stanford.edu/entries/belief-merging/)) aggregates their bases under integrity constraints, with weighted (reliability) variants. For a story, merging is the right model of a character assembling a picture from three witnesses. In practice, a priority-ordered union with greedy consistency (below) is the decidable approximation.

## 4. Dynamic epistemic logic

**Hard information.** Public announcement *!p* deletes ¬*p*-worlds. Baltag, Moss & Solecki's action models (TARK 1998; [SEP: DEL](https://plato.stanford.edu/entries/dynamic-epistemic/)) generalise this to private and semi-private events: whispering, peeking, being watched while peeking. Our `tell` / `whisper` / `witness` (everyone present sees, and sees the others see) already implement a bounded fragment of action-model update.

**Soft information.** Van Benthem's ["Dynamic logic for belief revision"](https://doi.org/10.3166/jancl.17.129-155) (JANCL 2007) and Baltag & Smets' ["A qualitative theory of dynamic interactive belief revision"](https://www.researchgate.net/publication/228626555_A_qualitative_theory_of_dynamic_interactive_belief_revision) (2008) put a **plausibility order** on worlds and distinguish three operators:

- **update** *!p*: hard; ¬*p*-worlds are eliminated, so the change is irrevocable;
- **radical upgrade** *⇑p*: all *p*-worlds become more plausible than all ¬*p*-worlds (lexicographic), so *p* becomes strongly believed;
- **conservative upgrade** *↑p*: only the *best p*-worlds move to the top (natural revision), so *p* is believed but easily overturned.

Baltag and Smets' key observation: these correspond to the **trust the agent has in the source**. Rodenhäuser's thesis ([*A Matter of Trust: Dynamic Attitudes in Epistemic Logic*, ILLC 2014](https://eprints.illc.uva.nl/id/eprint/2125/)) makes this the central notion. A **dynamic attitude** towards a source is a belief-revision policy. *Infallible trust* applies !, *strong trust* ⇑, *minimal trust* ↑, *neutrality* the identity (note the claim, change nothing), and the duals (*strong distrust* ⇑¬*p*, i.e. believing the opposite of what a known liar says). Rodenhäuser also shows that epistemic modals can denote such attitudes. **This is the design we want:** trust selects the operator, per hearer and per source.

**Lying and bluffing.** Van Ditmarsch's ["Dynamics of lying"](https://link.springer.com/article/10.1007/s11229-013-0275-3) (*Synthese* 2014) models a lie *¡p* as an update that the hearer processes like a truthful announcement while the speaker's model is unchanged. Two features matter here. Lies to a *skeptical* hearer, modelled with plausibility, are just soft upgrades that may fail. And a believed lie is a **false belief that is consistent** in the hearer, so no consistency invariant catches it; only `falseBelief` does. Catching a liar (seeing ¬*p* after being told *p* by *d*) should lower trust in *d*. That is Rodenhäuser's reliability dynamics, and it is a natural `Social` side-effect.

**Evidence logic.** Van Benthem & Pacuit, ["Dynamic logics of evidence-based beliefs"](https://link.springer.com/article/10.1007/s11225-011-9347-x) (*Studia Logica* 2011), keep the agent's **pieces of evidence** as sets, which may be mutually inconsistent, and derive belief from maximally consistent bundles. The agent can hold conflicting evidence without holding conflicting beliefs. Our provenance list is already an evidence base; the view should be a derived maximal consistent bundle.

**Justification logic.** Artemov's ["The logic of justification"](https://www.cambridge.org/core/journals/review-of-symbolic-logic/article/abs/logic-of-justification/ABD22C8DEC052CC92E26EC1B6DB03DFF) (RSL 2008; [SEP](https://plato.stanford.edu/entries/logic-justification/)) replaces □*p* with *t : p*, "*t* is a justification of *p*", with application (*s·t*) and sum (*s+t*). This is the formal version of "keep the reason, not just the belief". Our `closure` should record *which* lore rule and premises produced each inferred literal. The evidential type of an inferred belief is then computable (weakest link of its premises), and `why` can explain why Kiran believes it.

## 5. Theory of mind in narrative and in LLMs

The benchmarks give a catalogue of failure modes:

- **ToMi** ([Le, Boureau & Nickel, EMNLP 2019](https://aclanthology.org/D19-1598/)): Sally–Anne-style first- and second-order false belief, controlled so that it cannot be solved by heuristics.
- **Hi-ToM** ([He, Wu et al. 2023](https://arxiv.org/abs/2310.16755)): up to fourth-order beliefs, *plus deception and communication*. Agents lie and the hearer may or may not trust them. Performance falls sharply with order.
- **FANToM** ([Kim et al. 2023](https://arxiv.org/abs/2310.15421)): information asymmetry in multi-party conversation, where people join and leave. Models answer as if absent participants heard everything.
- **OpenToM** ([Xu et al. 2024](https://arxiv.org/abs/2402.06044)): characters with personalities and intentions. Models track physical-world beliefs well and *psychological* ones (attitudes, emotions) badly.
- Robustness critiques: Ullman's [trivial alterations](https://arxiv.org/abs/2302.08399) break LLM ToM. Sclar et al.'s [SymbolicToM](https://arxiv.org/abs/2306.00924) shows that an explicit per-character belief tracker fixes much of it, which is our architecture.

Failure modes a checker should catch, and which our model decides:

1. **Knowledge leak:** a character acts on or states *p* with no evidence path (not seen, not told, not inferable). This is the commonest error. Decided by a provenance check on factive verbs and on action preconditions.
2. **Omniscient eavesdropping:** an absent or not-yet-arrived character "heard" something (the FANToM error). Decided by `loc` at the time of the tell.
3. **Stale belief:** a character witnessed a change and still acts on the old state.
4. **Liar believes own lie;** speaker's model updated by their own lie.
5. **Second-order slips:** "Kiran thought Mara didn't know", when Mara told Kiran she knew.
6. **Narrator/character conflation:** FID content checked as world truth, or factive verbs used for false content ("she knew the butler did it" when he didn't). The second is a *narrator* error unless the narration is marked unreliable.
7. **Out-of-character credulity:** the skeptic swallows a rumour from an enemy, or the loyal friend disbelieves their sister without cause. This is the new class this note enables.

## 6. Character-dependent epistemic style

Psychology gives the parameters directly:

- **Gullibility vs skepticism** = default trust in testimony, i.e. a Reidian vs Humean prior. Sperber's vigilance threshold.
- **Paranoia** = a benevolence check that defaults to *fail*. Testimony from anyone low in trust or high in tension is discounted or even inverted (Rodenhäuser's strong distrust).
- **Confirmation bias** ([Nickerson 1998](https://doi.org/10.1037/1089-2680.2.2.175)) = asymmetric entrenchment. Belief-consistent input gets a bonus and belief-inconsistent input a penalty, i.e. existing beliefs are more entrenched.
- **Motivated reasoning** ([Kunda 1990](https://doi.org/10.1037/0033-2909.108.3.480)) = entrenchment that depends on *desirability*. Beliefs the character wants true (from `Persona.values` or explicit desires) are harder to dislodge and easier to adopt. Kunda's point is that this works through a raised evidence threshold, not through ignoring evidence. That maps exactly to a rank offset, not to a veto.
- **Stubbornness / dogmatism** = conservative rather than radical upgrades on ties. **Open-mindedness** = the opposite.

Each of these is a small integer offset or a tie-breaking choice in a ranked base. None needs probabilities, and all of them stay decidable.

## Recommended design for StoryLangLib

**Thesis.** Replace "seeing beats hearsay" with **ranked evidence bases plus per-event upgrades whose type is chosen by the hearer's dynamic attitude toward the source**. The attitude is computed from three inputs: the evidential type of the information, the hearer's trust bond with the speaker, and the hearer's persona. Beliefs are never deleted. The view is the greedy, priority-ordered, maximal consistent subset of the evidence base. This is a Spohn/Nebel-style linear base revision, which is decidable by construction. "Seeing beats hearsay" survives as the **default persona's** behaviour, which is a property we can prove.

### D1. Evidence, not beliefs

```lean
inductive Evid (C : Type) where
  | seen                 -- visual, direct
  | sensed               -- heard/felt/smelled the event itself
  | inferred             -- by lore from held premises (weakest-link source)
  | assumed              -- guess, "might", general expectation
  | told (c : C)         -- quotative: named source, first-hand claim
  | relayed (c : C)      -- c passed on what someone else said
  | rumour               -- hearsay with no named source ("apparently", "they say")
  | self                 -- own action/intent; infallible
  deriving DecidableEq, Repr

inductive Upgrade | hard | radical | conservative | note
  deriving DecidableEq, Repr

structure Held (C Φ : Type) where
  b     : Belief C Φ
  src   : Evid C
  rank  : Nat            -- Spohn-style firmness; higher = more entrenched
  stamp : Nat            -- event index, for tie-breaking
  up    : Upgrade        -- how it entered (decides ties)
  deriving DecidableEq, Repr
```

`self` and the lore's strict rules are the only `hard` information. Seeing is *radical at the top rank*, not hard, because `Magic.glamour` already makes seeing fallible and a story should be able to say "she saw through the glamour".

### D2. Strength: evidential prior + trust + persona

```lean
def evidPrior : Evid C → Nat
  | .self => 6 | .seen => 5 | .sensed => 4 | .inferred => 3
  | .told _ => 3 | .relayed _ => 2 | .assumed => 1 | .rumour => 1

def strength (w : W) (hearer : C) (e : Evid C) : Int :=
  let p := persona w hearer
  evidPrior e
  + (match e with
     | .told d | .relayed d =>
         (if bond w hearer d .trust ≥ 2 then 1 else 0)
       - (if bond w hearer d .trust == 0 then 1 else 0)
       - (if bond w hearer d .tension ≥ 2 then 1 else 0)
     | _ => 0)
  + (if p.has .gullible  && e.isTestimony then 1 else 0)
  - (if p.has .skeptical && e.isTestimony then 1 else 0)
  - (if p.has .paranoid  && e.isTestimony && bond w hearer (speaker e) .trust < 2 then 2 else 0)
```

Add `gullible | skeptical | paranoid | stubborn | openMinded` to `Persona.Trait`. Make the trust offset domain-relative later (Booth & Hunter) by indexing `Dim.trust` by topic. Start without that.

### D3. Dynamic attitude: choose the upgrade

The hearer's attitude maps strength to an operator, following Rodenhäuser's classification:

```lean
def attitude (p : Persona) (s : Int) : Upgrade :=
  if s ≥ 6 then .hard
  else if s ≥ acceptAt p then (if p.has .stubborn then .conservative else .radical)
  else if s ≥ entertainAt p then .conservative
  else .note                              -- record `bel d b` only (neutrality)
```

with `acceptAt` 3 by default (2 gullible, 4 skeptical) and `entertainAt` = `acceptAt - 1`. A `note` still records the claim `⟨.bel d b, .told d, …⟩`. That is the not-at-issue reportative layer, and the speaker's commitment is always learned. Strong distrust (believing ¬*p* because an enemy said *p*) is a fifth attitude. I would add it only for `paranoid` with tension ≥ 3, because it is rare and makes stories feel contrived.

This choice should also be a **defeasible theory in `DL.lean`**, mirroring `flirtTheory`, so that `why` can explain an acceptance or rejection: "skeptics doubt hearsay" (safety), "a sister's word is good" (loyalty), "what I saw outranks it" (strict), with `valueSup` from the persona. The numeric ranks order the *base*. The DL theory licenses the *upgrade type*, and its labels give the LLM-facing explanation. If that is too much machinery at first, start with the numeric `attitude` and add the DL theory once explanations are needed.

### D4. Revision as ordering, and the view as a greedy consistent prefix

An upgrade only **inserts** a `Held` with `rank := max s 0` (or the top rank for `hard`). Nothing is deleted. The order is: higher rank first. On ties, a *radical* newcomer goes before older items, and a *conservative* one goes after them (it is believed only if nothing of equal standing objects). Entrenchment and motivated reasoning are offsets applied when *sorting*: `+1` to existing beliefs for `stubborn` / confirmation bias, and `+1` to literals the character `wants`.

```lean
def ordered (w : W) (c : C) (hs : List (Held C Φ)) : List (Held C Φ) :=
  hs.mergeSort fun x y => key w c x > key w c y ||
    (key w c x == key w c y && tieFirst x y)   -- radical newer first; conservative older first

/-- Keep each item iff it is consistent (under lore closure) with what is kept so far. -/
def admitted (hs : List (Held C Φ)) : List (Held C Φ) :=
  hs.foldl (fun kept h =>
    if consistent (closure ((kept ++ [h]).filterMap (litOf ·.b))) then kept ++ [h] else kept) []

def view (w : W) (c : C) : List (BLit Φ) :=
  closure ((admitted (ordered w c (beliefs w c))).filterMap (litOf ·.b))
```

This gives three properties:

- `mindConsistent` holds **by construction** (`admitted` only keeps consistent prefixes). So it becomes a theorem, not an invariant the story can fail. Consistency stays useful as a *check on the text*: a text that says Kiran believes something outside his `admitted` set is the error.
- **Iterated revision for free.** A belief suppressed by hearsay returns once that hearsay is itself outranked, as in Darwiche–Pearl and evidence logic.
- **Decidable and cheap.** Everything is a finite fold over lists with `DecidableEq`. Cost is O(n² · |lore|), fine for story scale.

### D5. Stated as inductive relations

Keep the Boolean functions as the checker, and state the spec relationally so the important lemmas can be proved, following the `DL.lean` pattern (relation + certificate + `decide`):

```lean
/-- `Admits c hs h`: `h` is in the greedy consistent prefix of `hs` (already ordered). -/
inductive Admits (hs : List (Held C Φ)) : List (Held C Φ) → Prop
  | nil  : Admits [] []
  | keep {pre kept h} : Admits pre kept → consistent (lits (kept ++ [h])) = true →
           Admits (pre ++ [h]) (kept ++ [h])
  | skip {pre kept h} : Admits pre kept → consistent (lits (kept ++ [h])) = false →
           Admits (pre ++ [h]) kept

/-- `Hears w c d b w'`: c receives b from d with the attitude its persona and bonds pick. -/
inductive Hears : W → C → C → Belief C Φ → W → Prop
  | adopt {w c d b} (u : Upgrade) : attitude (persona w c) (strength w c (.told d)) = u →
      u ≠ .note → Hears w c d b (insert w c ⟨b, .told d, rankOf u w c d, now w, u⟩ |> noteClaim c d b)
  | note  {w c d b} : attitude (persona w c) (strength w c (.told d)) = .note →
      Hears w c d b (noteClaim w c d b)

theorem admitted_consistent : consistent (lits (admitted hs)) = true
theorem admitted_spec : Admits hs (admitted hs)                     -- function = relation
theorem default_seeing_beats_hearsay :                               -- the old policy as a lemma
  persona w c = default → (seen p) ∈ beliefs w c → told d ¬p ... → ¬ thinksNot w c p
```

`default_seeing_beats_hearsay` is the regression test that we have *generalised* the old policy, not discarded it. It holds because `seen` (5) beats `told` (3 ± 1) whenever no persona offsets apply.

### D6. Inference carries its reasons

Make `closure` return `List (BLit Φ × Just)` where `Just` is the lore-rule index plus premise indices (Artemov's *t : p*, shallowly). An inferred literal's evidential strength is the **minimum** of its premises' ranks, capped at `evidPrior .inferred`. Then "Kiran inferred the letter was taken because the drawer was empty and Mara was the last in the room" carries the weaker of the two sources, and `why` can print the chain.

### D7. Side effects on trust

Add one rule in `Social`. When `c` *admits* a `seen`/`sensed` literal that contradicts a claim `bel d b` that `c` noted, apply `bump w c d .trust (-1)`. Being caught out costs credibility (Rodenhäuser's reliability dynamics, Fricker's credibility economy). Being confirmed could add `+1`, but I would hold off on that because it makes trust inflate in long stories.

### D8. The lexicon marks evidentiality, factivity and attribution

Each lexicon entry returns, besides the event, a **report record**:

```lean
structure Report (C Φ : Type) where
  holder  : Option C       -- whose belief (none = narrator)
  content : Φ × Bool
  evid    : Evid C
  factive : Bool           -- narrator commits to `content` being true
  anti    : Bool           -- narrator commits to its falsity ("lied")
```

| Verb / marker | Event | `evid` | factive |
|---|---|---|---|
| *see, watch, notice, spot, witness that* | `see` | seen | yes |
| *hear/smell/feel* + NP | `see` | sensed | yes |
| *hear that, learn that (from X)* | `hear` | told X / rumour | no |
| *know, realise, discover, find out, remember* | check only | (must have a path) | **yes** |
| *believe, think, suspect, assume, fear, suppose* | check only | — | no |
| *deduce, conclude, figure, work out* | check only | inferred (must be derivable) | no |
| *say, tell, explain, announce* | `tell` | told | no |
| *claim, insist, swear* | `tell` (**not** `lie`) | told | no |
| *admit, confess* | `tell` | told, +1 strength (against interest) | yes |
| *whisper* | `whisper` | told | no |
| *lie, deceive* | `lie` | told | **anti** |
| adverbs *apparently, supposedly, allegedly, reportedly, they say* | — | rumour (downgrade clause) | no |
| *must* | — | inferred | no |
| *might, may, perhaps* | — | assumed, conservative | no |

The checker then runs two judgements per report. **Narrator truth:** `factive → Truth w content` and `anti → ¬Truth w content`. **Holder support:** `holder = some c → content ∈ view w c`, and for factive and inferential verbs `c` must have an `Admits` path. Clauses detected as free indirect discourse (evaluative or interrogative main clauses, character deixis, inside a focalised paragraph) get `holder := focaliser` and are never checked against `Truth`. That keeps unreliable narration and dramatic irony legal while still catching the knowledge-leak error.

### What to build first

1. `Evid`, `rank`, `stamp`, the persona traits, `strength`/`attitude`, and order-then-`admitted` in place of `add`/`see`/`hear` deletion. Prove `admitted_consistent` and `default_seeing_beats_hearsay`.
2. Fix `mindLex` (*claim*/*swear* → `tell`) and add the `Report` record with factivity and the adverb downgrades.
3. Add justification-carrying closure and the "caught lying" trust rule.
4. Add domain-relative trust, the DL explanation theory and FID attribution.
