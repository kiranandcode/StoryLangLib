# Gaps: what an explicit friends-to-lovers story needs that StoryLangLib couldn't say

A stress test on a real text: chapter 1 of an original work on AO3 (adult,
explicit; two friends, a trans woman narrator and her childhood best friend; a
first time with a dom/sub dynamic). The text and its annotation live in the
gitignored `stories/private-ao3-boyremoval/`; nothing here quotes more than a
few words of it, and nothing explicit.

The chapter was read twice: at the Studio's grain (the five coarse acts of
`World/Social.lean`, where every act passed), and at the grain of the new
`World/Consent.lean` and `World/Relationship.lean`, where the same chapter is
plausible but not valid, and the kernel names the eleven acts that rest on
consent nobody gave out loud. That difference is the main finding: the coarse
model called the chapter fully consensual because it couldn't see what was
never negotiated.

Each gap: what failed, a minimal example, and the generalisation (with where
it now lives, if implemented).

## 1. Acts are too coarse

**Failed.** `Act = holdHands | kiss | touch | undress | sex`. A hand over the
mouth, a hand on the throat, hair pulling, biting, leaving marks, pushing a face
into a pillow and a caress of the cheek are all `touch`; fingering,
penetration, going harder and finishing inside are all `sex`. Agreeing to
`sex` once covered everything after it, including things the narrator never
heard named.

**Example.** She agrees to sex; later he grips her throat. Coarse model:
`act robin remy touch`, consented (she agreed to `touch` back at the first
kiss). Nothing flags it.

**Generalisation (implemented).** `Intim`, a finer act set where each act
refines a `Social` act (`Intim.coarse`, so the fine story abstracts to the
coarse one), with *edge* acts (gag, bite, mark, hair pull, choke, pin down) that
are only covered by being named. `covers` says which grant covers which finer
act (penetration covers the fingering that prepares it; rough covers
penetration), so agreement is to a scope, not a single token.

## 2. How consent was given (explicit, nonverbal, by deed, blanket)

**Failed.** `agree` is one bit. The text gives consent in at least five ways:
out loud, a nod, a deed that invites the act (leaving a garment on so he can
take it off; pushing back, which the text itself calls an invitation), begging,
and "whatever you want". The Studio has nowhere to put any of the
differences. Worse, the first touch comes before anything is said; to make
`act ... touch` pass I had to hang her `agree` on her question whether he finds
her attractive, and his on his answer: a reading forced by the model, not
given by the text.

**Example.** "Do you find me attractive?" ⟶ `agree remy robin touch`. Wrong in
kind: it's an invitation at most.

**Generalisation (implemented).** `Signal = verbal | nod | invite | blanket |
pressured` on every grant; verbal, nod and invite are *firm*, the others not.
An act resting only on a non-firm grant, or on nothing, is `unknown` (an
assumption `Plausible` lists), not a silent yes.

## 3. A blanket offer is not consent to an act

**Failed.** She says he can do whatever he wants; he refuses to act on it and
makes her name what she wants. Coarse model: both are `agree remy robin sex`,
and the refusal (a central beat of the scene and of his character) is
invisible, or a `request` with no content.

**Generalisation (implemented).** A blanket offer is an *offer to submit*
(`offer sub dom`), not a grant. Taking it (`take dom sub limits`) starts a
scene and sets blanket grants aside; inside the scene sex acts still need a
named grant. Theorem (private chapter): the verdicts are unchanged if the
blanket offer is deleted; he never relied on it. Theorem (public example
`Examples/Scene.lean`, `blanket_not_enough`): with only the blanket offer, sex
is an assumption.

## 4. Ongoing versus one-off; check-ins

**Failed.** "This ok?", "You all ready?", "Do you want…?" come after consent
was already given. In the Studio, `askAct` after `agree` does nothing, and
consent never expires, so a check-in can't be told from noise, and an
agreement to one act ("yes" to finishing inside) can't be used up.

**Generalisation (implemented).** `checkIn a b x` opens a check; the answer is a
fresh grant or a withdrawal. Grants can be `once` (consumed by the act).

## 5. Withdrawal must bind inside a scene

**Failed (in my own first draft, caught by the kernel).** My first `Consent`
let the dominant's scene cover an act whose grant had been withdrawn: it fell
back to "the scene covers it". `decide` refused the theorem that a withdrawal
before the first penetration rules it out.

**Generalisation (implemented).** `withdraw` records the refusal; `stop` (a
safeword) ends the scene and refuses everything; both rule acts *out* (`no`)
until a fresh grant, scene or no scene (`withdraw_rules_out`,
`stop_rules_out`, and in the example `withdrawal_binds`, `safeword_binds`,
`withdraw_then_yes`).

## 6. Power exchange is agreed, not a trait

**Failed.** The Studio has `dominant` and `submissive` as persona traits,
which only bias `flirt`/`agree`. Orders (to beg, to say what she wants, to go
and get ready) could only be `request` of a fact, or nothing; praise nothing
at all; and nothing says the roles were offered and
taken rather than imposed.

**Generalisation (implemented).** `Scene {dom, sub, limits}` exists only after
`offer` and `take`; `command` is in role inside a scene and an assumption
outside it; `take` without an offer is ruled out (`roles_agreed`). Inside a
scene the dominant may lead non-edge, non-sex acts without asking each one.
Not done: praise and degradation as role speech (see 13).

## 7. Edge acts nobody named

**Finding about the text, not just the model.** At the refined grain, the
chapter is plausible and every sex act was named and agreed to
(`sex_acts_named`), but eleven acts rest on assumptions
(`chapter_assumes`): the group-decided lap ride; groping before anything about
it was asked; a hand over her mouth before any scene existed; and, inside the
scene, biting, marking, a face pushed into a pillow, hair pulling and a hand on
the throat. A writer using the Studio would want exactly this list.

## 8. Group pressure and acquiescence

**Failed.** "Everyone but me in agreement": the group decides she rides in his
lap. The Studio has no group decision, so the reading became `make guys
remyOnLap` (the group as one character bringing about a state), with `guys`
standing in for several people of whom one spoke. Her reluctance has nowhere
to go; neither does his (he sits at the end because the group put him there).

**Generalisation.** `Signal.pressured`: compliance is recorded but never firm,
so the lap ride is listed as an assumption (implemented). Not done: groups as
agents (a decision taken by a group, a member speaking for it, membership,
"everyone but me"); this needs a `Group` module with majority and dissent.

## 9. Touch that isn't intimate

**Failed.** He smacks each drunk friend on the head to make them stop
bothering women. In the Studio, `act robin guys touch` would need the guys'
consent and fail, so the clause was judged a bare gesture.

**Generalisation (partly).** `Intim.contact` refines no coarse act and is
never edge: incidental or social contact (the lap ride, a hand on a
shoulder). Not done: norms that license some contact among friends (a smack
to snap someone out of it), which should be a defeasible rule in the
character theory, not a consent grant.

## 10. Firsts are history

**Failed.** "The first man to see…", "your first time", "for the first time I
think…". The Studio has a state atom `remyVirgin` flipped by `become`; it says
nothing about which acts were firsts, and nothing stops two "first times".

**Generalisation (implemented).** `ConsentState.never` (what each character
had never done when the story opened) and `done` (history); `firsts` reads
every first off the trace (`remy_firsts`, `firsts_from_history`). Firsts are
derived, not asserted.

## 11. Body and identity

**Failed.** She is a trans woman on HRT; she still uses the men's room out of
fear of the women's; her body is compared with how it was before HRT; he
tells her she'll present as his princess and drop the hoodie. Only as atoms:
`remyTrans`, `remyOnHrt`, `remyUsesMensRoom`. The model has no gendered spaces
(a bathroom she is entitled to but afraid to use), no difference between
identity and presentation, and no way to see that "none of this hoodie shit"
is one person claiming a say over another's presentation.

**Generalisation (proposed).** An `Identity` module: identity facts (fixed,
known to some), presentation (a state the person controls; another's demand
about it is a `request` she may refuse, like a relationship proposal),
gendered spaces with entitlement and perceived safety as separate facts
(`entitled` versus `safe`), and history ("before HRT") as dated facts rather
than prose.

## 12. Desire versus intention versus consent

**Failed.** Her stated need, her longing, the fantasy in the car.
The Studio offers `adopt` (a goal: a commitment that motivates later acts and
would wrongly license nothing) or an atom. Desire that is neither a plan nor
consent had no place, and a reader could mistake an interior want for a yes.

**Generalisation (implemented).** `wish c d x`: interior, recorded, inert for
consent (`wish_grants`, `wishes_inert`, `wish_not_consent`). Fantasy is a wish
in the hypothetical mood; the Studio's `hypothetical` judgement covers the
clause.

## 13. Speech inside the scene

**Failed.** Dirty talk, degradation, a slur used in the scene, "you're mine
forever": said, not asserted as facts the speaker believes. The Studio reads
speech as `tell` (sincere) or `sarcasm` (inverted); neither fits role speech.

**Generalisation (proposed).** A speech mode `inRole` for utterances inside a
scene: they update the scene (praise, degradation, claims of possession) but
not anyone's beliefs, and they don't commit the speaker outside it. Their
commitments outside the scene go through `Relationship.propose` (14).

## 14. Friends to lovers

**Failed.** Bonds are levels (trust, attraction, affection, tension). The
arc of the chapter is a change of *kind*: best friends, then lovers by deed,
with his "mine", "mine forever", "my princess everywhere we go" as declarations
she never answers. Coarse model: `childhoodFriends` atom and a few `tell`s.

**Generalisation (implemented).** `RelKind` with kinds that hold by deed
(`consummate`), by mutual word (`propose` + `accept`), or from history (the
start state); one-sided declarations stay pending (`propose_kinds`). The
chapter ends `bestFriends, lovers` with `partners` and `exclusive` pending
(`friends_to_lovers`).

## 15. Inference, evidence and interior monologue

**Worked, mostly.** Hypotheticals ("is it gonna hurt?", "maybe they'll see
me") were judged `hypothetical`; inferences ("anyone asleep is certainly awake
by now", "all but confirming") read as `notice … inferred`. Rough edges:
an evidential "because" (he clearly agrees, because he pushes her down) is
read by `Cause` as a cause; reactions without a fact ("WHAT???") can only be
`act`; involuntary bodily states (arousal in the car) are state atoms with no
agent, which is right, but nothing connects them to the consent model (forced
proximity producing arousal is not an act by anyone).

## Overlap with other modules

`Consent` refines `Social`'s consent (same acts at the coarse grain, via
`Intim.coarse`) and leaves `Social` untouched; the Studio still checks the
coarse acts, and `langlib consent <dir>` checks the fine reading
(`LangLib/Studio/Consent.lean`). A sibling study of another AO3 story may add
its own consent or relationship modules; `Relationship` is deliberately small
(kinds and proposals) so either can build on it.
