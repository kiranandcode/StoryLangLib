# Gaps: a slow burn across volumes

A private series (two volumes, ten chapters) is a slow-burn romance with Kiran
as the protagonist: a demisexual researcher who assumes nobody could be
interested in her, a love interest with his own reasons to go slowly, weekly
meetings over most of a year, and heat that stops at kissing. The task was to
make the burn itself checkable: a move made too early (a feeling, a belief, a
touch, a tie) must fail as out of character, with a reason that names the setup
that would earn it. This file records what the model could not say, what was
added, and what is still open. No story text.

## 1. Ties rose as fast as events allowed (implemented: `slow`, `Studio/Ext`)

**Failed.** `raise a close b` three times in one scene was as valid as once a
week for three months. Nothing in `Ties` knows about time or scenes.

**Generalisation.** A story names its slow ties (`"slow": ["close",
"romance"]`). Each paragraph knows its beat (story.json's outline), and a slow
tie rises at most one level per beat in each direction; a second rise in the
same beat is out of character ("to justify it, first establish: another scene
between them"). Only real rises count (a `relate` of a tie already held changes
nothing). The walk records `(tie, from, to, beat)` in the ext state.

## 2. Desire that needs a bond first (implemented: `World/Affect.AffectBond`)

**Failed.** `feel c desire` was always allowed. A demisexual character feels
desire only toward someone she is already close to.

**Generalisation.** `AffectBond.needs c e = some (r, n)`: `c` can feel `e` only
while she holds tie `r` at level `n` toward someone (`bondOk`). Nobody needs a
bond by default (`bondOk_free`); where one does, the feeling is ruled out before
it (`bond_no_feel`). Combined with the existing anomaly reading (examine,
recognise, own), desire now has three gates in order: the bond, the
examinations, the recognition. In story.json: `"bondNeeds": [["kiran",
"desire", "close", "5"]]`.

## 3. A belief held against the evidence (implemented: `World/Conviction`)

**Failed.** `Mind` revises on the first piece of evidence strong enough to
outrank what is held. "She won't believe he is interested for a long time,
with evidence piling up" had two bad encodings: as her own knowledge (rank 10)
nothing short of her own conclusion ever moves it, and no count of signs is
kept; as an inference (rank 3) one sensed sign flips it at once (and a state
atom goes stale on the first contrary sign).

**Generalisation.** `ConvictionSight.holdout c x = some n`: `c` registers signs
of `x` (`datum`), explains them away (`dismiss`, which needs a sign not yet
explained), and may `concede` only once `n` signs are in (`concede_needs_data`,
`concede_free`, `bump_counts`). In the Mind she holds the negation as her own
knowledge, so each sign she perceives sits outranked in her base and each tell
is only noted: the Minds view shows the dramatic irony. The flip is her own
conclusion (`notice c x self`).

**Still open.** The two readings are coupled by a check in `workflows.py`
(`conviction_objections`: a `notice c x self` of a held-out `x` must come with
`concede c x` in the same paragraph, and the other way round), not in the
kernel. The general fix is the one roof-eleven's gap 6 proposes: let one
reading's rules read another's state.

## 4. Intimacy gated by where they are (implemented: `gates`, `Studio/Ext`)

**Failed.** `World/Consent` checks that an act was asked and answered; it says
nothing about whether a kiss in the fourth week is in character for two people
who are not yet anything to each other. Social's `agree` gate (attraction and
trust at 2) is reached in a few scenes.

**Generalisation.** `"gates": {"kiss": ["romance", "1"], "grope": ["romance",
"2"], ...}`: an act of the paragraph's consent reading needs the tie at the
level both ways, checked at the paragraph's end in the ext walk, with a
theorem per gated act that it was out of reach at the opening
(`act_gated_i`). With `romance` requiring `close` at 6 and `close` slow, the
first kiss cannot come before six scenes of closeness on her side.

## 5. Plans were not checked against the personas (implemented)

**Failed.** `plan-check` judged a plan's main events only; the ext reading (ties,
care, affect) and the consent reading read prose readings (`events.json`) only,
so a plot could put a feeling or a kiss too early and pass until the prose was
written.

**Generalisation.** For a paragraph with no prose yet, `langlib ext` and `langlib
consent` read its plan (`NN.plan.json`, `ext` and `consent` as bare strings in
story order), and `plan-check` reports their issues. So the burn is checked
before any prose: the series bible is a story directory with one plan per beat,
and the early-move tests above fail there.

## 6. A story longer than one directory (implemented: chained chapters)

**Failed.** Every check and proof replays a directory's paragraphs, so a story
of volumes would outgrow the 600 s proof budget and make every
`paragraph-check` slow.

**Generalisation.** One directory per chapter, each opening where the one
before ends. `langlib end <dir>` prints the end state of all three readings in
story.json's opening vocabulary (places, holdings, bonds, views as own
knowledge, goals, state atoms; ties, needs, names, pronouns, secrets, feelings,
examined and recognised anomalies, conviction counts; what each character has
never done, relationship kinds). `workflows.py chain <prev> <next>` writes it
into the next chapter; `chain-check` (and `plan-check`) fail when a chapter's
opening is not where the one before ends. Plans count, so a whole series can be
chained and checked before any prose. The ext start state gained `examined`,
`recognised`, `data`, `dismissed`, `conceded` for this.

**Still open.** The link is checked by the CLI (the same Lean definitions
compute both sides), not proved in one kernel term: each chapter's
`Proofs.lean` proves its own story from its literal opening.

**Caught by the chain check, fixed.** The first version carried each view as
its holder's own knowledge (rank 10). Chapter 4 then could not let Kiran see
that the walk was never on his way: her chapter-1 inference that it was had
become unrevisable at the break. A belief now crosses with its rank and
evidence (`"walkOnHisWay@3:inferred"` in `knows`, `Spec.held`), so later
evidence weighs against it as before; `rec_start` (the L5 record invariant) is
re-proved for openings with such beliefs. What a character only noted (a tell
she did not believe) still does not cross; the conviction's count carries in
the ext state, which is where the burn needs it.

## 7. Talk across places (open)

Texting is how a weekly friendship lives between meetings. `tell`, `hint`,
`ask` need the two together, so a message from his office to hers cannot be
read; the series keeps its key exchanges in person and lets texts be narrated
summary. Proposed: a `channel` (a phone, a letter) that makes two places
adjacent for speech only, with no perception of anything else.

## 8. Recurring events cannot be beat keys (worked around)

A beat's key event must occur once, in that beat. A weekly story repeats its
moves (to the shop, up the avenue), so keys are scene-specific facts (a state
atom that changes once) or speech acts about a fact told once.

## 9. A reason not to act is not a gate (open)

His rule (no asking anyone in the group out while he convenes it) is a fact and
a state, and the plot honours it, but nothing makes a proposal while he
convenes out of character: ties have `requires` (a positive level) and
`excludes` (one tie ends another), not "only while the other is absent".
Proposed: `requires` with a bound (`["convenes", "<", 1]`).

## 10. "Nobody fixes her outlook" is an absence (partly)

Her outlook (nothing outside research) is a true fact she holds; the series
asserts she still holds it at the end (a claim of the last beat). That nobody
argues her out of it is a property of every event, not of an end state; it
holds because no event in any reading tells her otherwise, which is checked
only by reading the plans. Proposed: a story-level theorem over all chapters'
events (no `tell _ kiran !kiranLifeIsWork`), once chapters chain in Lean.

## 11. A lexicon word with two senses

The story's emotion lexicon listed "hungry" under desire; "She had not known she
was hungry" then read as desire she could not yet feel (the bond gate), when it
was the food need she is blind to. The checker was right about the words; the
lexicon was wrong. Emotion words that also name a need belong to neither list.

## 12. Voice measured by proxy

The `fixpoint` style (`Style/Fixpoint.lean`) adds `playful` (interjections and
exclamation marks inside quotes) for her cutesy talk, alongside clinical
interiority and banter share. It counts markers, not charm.
