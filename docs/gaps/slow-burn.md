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

**Coupled in the kernel (implemented).** The ext reading of a paragraph also
reads the main reading's `notice c x self` events for held-out propositions
(`XPara.flips`), and the walk requires a `concede c x` exactly where there is a
flip (`convCoupled`), so `ext_valid` proves the two readings move together. (A
first version checked this in `workflows.py` only.)

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

**Proved (implemented: `Studio/Chain.lean`, `workflows.py chain-prove`).** Each
reading's state projects to sorted lines of plain names (`mainLines`, `xLines`,
`consentLines`). `langlib chain-lean <prev> <next>` writes `Chain.lean` into the
next chapter: the previous chapter's spec, events, ext paragraphs and consent
events as literals, each `#guard`ed against the previous directory's files
through `include_str`, and three theorems by `decide +kernel` that replay the
previous chapter once and equate its end with the next chapter's opening
(`chain_main`, `chain_ext`, `chain_consent`). A chapter told out of order is
refused (the replay is in told order).

**Caught by the chain check, fixed.** The first version carried each view as
its holder's own knowledge (rank 10). Chapter 4 then could not let Kiran see
that the walk was never on his way: her chapter-1 inference that it was had
become unrevisable at the break. A belief now crosses with its rank and
evidence (`"walkOnHisWay@3:inferred"` in `knows`, `Spec.held`), so later
evidence weighs against it as before; `rec_start` (the L5 record invariant) is
re-proved for openings with such beliefs. What a character only noted (a tell
she did not believe) still does not cross; the conviction's count carries in
the ext state, which is where the burn needs it.

## 7. Talk across places (implemented: `MindEv.message`)

Texting is how a weekly friendship lives between meetings. `tell`, `hint`,
`ask` need the two together, so a message from his office to hers could not be
read. `message c d l` is a tell that needs no co-location: only `d` learns it,
as testimony from `c`, and `c` must believe it. It joins the L5 record proofs
(`mind_grows`) and the Fight example's projection, and "text", "message",
"write", "type" are verbs of saying for completeness. (The series was written
before this, with its texts as narrated summary.)

## 8. Recurring events as beat keys (implemented: indexed keys)

A beat's key event had to occur once: a weekly story repeats its moves (to the
shop, up the avenue), so keys had to be scene-specific facts. A key may now
name an occurrence, `"move kiran errata#1"`: the n-th time the event happens in
the story. Beats abstract occurrence-tagged events (`tagOcc`, `Beats.absOcc`),
and without indexed keys this is exactly the old abstraction (`absOcc_plain`).
The series' first beat is now keyed by her first arrival at the shop. Keys of
beats outside a chapter are dropped from its vocabulary, since an occurrence
count is per chapter.

## 9. A reason not to act is a gate (implemented: `TieLaws.forbids`)

His rule (no asking anyone in the group out while he convenes it) was a fact the
plot honoured and nothing enforced. Ties now have `forbids r = some (r', k)`: `r`
cannot start or rise while `r'` holds at `k` either way (`forbids_no_start`).
The series declares `romance` forbidden by `convenes`, which Ryan holds toward
Kiran from his first words to her until the handover; without the handover the
romance tie is out of character ("another tie between them rules this one out
for now"), tested on a scratch copy.

## 10. "Nobody fixes her outlook" (implemented: `Spec.kept`)

Her outlook (nothing outside research) is a true fact she holds. A story can
now declare beliefs that must be held after every paragraph (`"kept":
[["kiran", "kiranLifeIsWork"]]`): `paragraph-check` reports the paragraph that
breaks one, and `Proofs.lean` proves each at every checkpoint (`pNN_kept0`).
With the chain theorems this covers the whole series.

## 11. A lexicon word with two senses (implemented: directed words)

The story's emotion lexicon listed "hungry" under desire; "She had not known she
was hungry" then read as desire she could not yet feel (the bond gate), when it
was the food need she is blind to. But "hungry for him" is desire. A lexicon
word may now name a preposition (`"hungry+for"`): it counts only when the
predicate adjective has a complement with that preposition pointing at a
character. Predicate adjective phrases (`ADJP` heads) are now read too; before,
"she was hungry for him" escaped the check entirely. Tested on scratch copies:
directed and unrecognised is flagged, directed and recognised passes, bare
"hungry" is never desire.

## 12. Voice measured by proxy

The `fixpoint` style (`Style/Fixpoint.lean`) adds `playful` (interjections and
exclamation marks inside quotes) for her cutesy talk, alongside clinical
interiority and banter share. It counts markers, not charm.
