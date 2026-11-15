# Gaps: what a hurt/comfort story with a trans heroine needs that StoryLangLib couldn't say

A stress test on a real text: chapter 1 of a fan work on AO3 (a no-powers
alternate universe; a mechanic finds a trans woman fleeing three men who outed
and attacked her, shelters her, and drives her to the police; the chapter ends
with her telling him her real name). It is about 6,300 tokens, cut into 95
paragraph files (short dialogue lines grouped), told in the present tense from
his point of view. The text, its annotation and its reading live in the
gitignored `stories/private-ao3-sweet-girl/`; nothing here quotes more than a
few words of it.

Two kinds of finding. First, **scale**: the Studio had only been run on stories
of 9 to 27 paragraphs, and a real chapter broke it before any semantics did.
Second, **semantics**: names, pronouns, privacy, care, threat and feeling carry
this chapter, and the base model could say almost none of it.

Each gap: what failed, a minimal example, and the generalisation (with where it
now lives, if implemented).

## Scale

### 1. A long story took minutes per check (fixed)

**Failed.** `langlib story` on the 95 paragraphs' plans took 147 s (at 60
paragraphs, 29 s; at 30, 3.7 s): past the Studio's 120 s timeout, so the
story showed as an error and every `paragraph-check` was killed. Profiling
(`sample` on the running binary) found three causes, each superlinear:

* the report re-walked the story from the start for every paragraph, and
  re-ran motives, scenes and perception from the start too;
* `Mind.admit` checked the consistency of everything kept for every literal it
  considered: cubic in a character's beliefs, run at every witnessed event;
* the untrusted timeline solver ran Bellman–Ford on lists (O(n) reads and
  writes) from zero for every constraint: the largest cost of all.

**Generalisation (implemented, 2301e56).** The report walks once and a
paragraph whose events are a prefix of the whole reads its steps off that
walk; `admitPlain` (checking each literal only against what was kept) is
proved equal to `admit` when a story has no lore, and `view` uses it
(`view_eq_viewSpec` still holds); `solve` is implemented by an array version
that starts each feasibility check from the previous least solution (same
fixpoint, same choices; the solver is untrusted anyway). Sweet Girl: 147 s to
about 1 s. A story *with* lore still takes the cubic path; an incremental
closure would fix that too.

### 1a. The proofs do not scale either (open; checkpointing under way)

**Failed.** `prove` timed out (600 s) on the chapter's `Proofs.lean`. The
whole-story theorem `story_valid` alone took 2542 s: kernel time for `Valid`
over the first n events grows about as n³ (60 events 5.8 s, 120 events 45 s),
and the 186-event run reached a 16 GB footprint and swapped. Kernel
diagnostics put the time in `Mind.ordered`'s insertion sort (which sorts
nested beliefs it then discards), the clash scans of `admitPlain` and `stale`,
and re-walking the `upd` chains that encode the world's function fields. The
kernel shares reductions within one declaration (so the bundled `paragraphs`
conjunction does share prefixes) but not across declarations, so
`story_valid` and `paragraphs` each replay the whole story.
**Generalisation (proposed; the boyremoval stress test is implementing the
first two).** A first-order world (association lists, `DecidableEq`) with a
literal checkpoint per paragraph, each proved from the previous one, and
`story_valid` derived from them by `valid_append`; per-paragraph checks stated
from the checkpoint; filter nested beliefs before sorting; strings compared in
the kernel (atom groups, setting words) interned as numbers, since 4.35's
kernel compares strings as UTF-8 byte lists.

### 2. The shared lock starves under several agents

**Failed.** Every `langlib` call takes one machine-wide lock. With two stress
tests annotating at once, a single check waited more than ten minutes behind
twenty queued calls, and the lock is not fair (`flock`). Batching helped: the
story's `chk.py` checks many paragraphs with one `langlib story` and one
`langlib ext` run.

**Generalisation (proposed).** A FIFO ticket lock, or one lock per story
directory for the read-only report (the lock exists to bound load, and a
report of a cut story is cheap now).

## The setting

### 3. Places had no owners (fixed)

**Failed.** "his yard", "his home", "his property": a possessive on a place
was an error (`it has no owner in story.json`), though fixtures could have
owners. **Generalisation (implemented, f906e12):** places take `"owner"`.

### 4. A vehicle is a place that moves

**Failed.** The truck is where they sit for the drive, and it goes from the
carport to the station lot. A place cannot move, so the street, the town
square and the streetlights they pass had to be fixtures *of the truck*.
**Example.** streetlights casting over her cheeks through the truck windows.
**Generalisation (proposed).** Places with a location that is itself a fluent
(`placeAt truck station`), with fixtures of the place outside visible from
inside it.

### 4a. Sound and sight cross places

**Failed.** Perception is per place: everyone in a place sees what happens
there, and nobody else. But he hears a trashcan go over and voices in the
alley from his yard, and she, inside the house, hears his lie to the men on
the deck ("his voice carries, even through doors and walls"). Her belief
that he had been to jail had to be read as told to her, which it was not.
Leaving is also invisible from where one leaves: a move is seen only at its
destination, so he could not see the men go back over the fence and needed a
separate `notice ... sensed`.
**Generalisation (proposed).** Perception channels with reach: `sound` carries
to adjacent places (a layout `near`/`leadsTo`), `sight` to places in view; a
move is witnessed at both ends; overhearing as an evidence kind (heard, not
addressed).

### 4b. Groups, sets and positions between places

**Failed.** "two of them climb over", "they trash talk", "the items", "their
case file": the three men act as one, three garments are one handover, a file
belongs to two people. None has a world id, so a group subject cannot carry
an event or an `act`, and the annotators had to split each into per-member
claims. A man straddling the top of the fence is in neither the yard nor the
alley.
**Generalisation (proposed).** Group entities with members, distributing
events (`move G p` is `move m p` for each member) and owning things jointly;
an `on` position between two places for walls and thresholds.

### 4c. Objects that appear, are worn, or have owners

**Failed.** A strip of her dress tears off on the fence and he later pulls it
free: an object that comes into existence. She wears his clothes; he throws on
a hoodie: wearing is not holding. "his keys" was an error: plot objects had no
owners (fixed, 4b11330: objects take `"owner"`). "her borrowed shirt" names the
holder, not the owner, and is still a hack.
**Generalisation (proposed).** `split o o'` for objects made from others; a
`wears` relation next to `holds`; a possessive that may name the current
holder of a lent thing.

### 4d. Things the text implies happened

**Failed.** The shovel he carried "stays outside": the drop is never told. The
dog, last seen hiding on the deck, is wagging indoors: the move is never told.
She "is brought to a different room": the mover is an unnamed officer, but a
move needs the mover's own motive, so the plan had to say she wanted to go.
**Generalisation (proposed).** Implied events as assumptions (`Plausible`
already lists unknown preconditions: the same for an unknown *event* whose
effect a later clause presupposes), and moves with an agent other than the
mover (`escort a c p`, motivated by `a`).

## Identity

### 5. Pronouns are per document, not per referrer (fixed, by Ext)

**Failed.** An annotation declares one pronoun series per entity, and
`langlib check` rejects any other: the men's "he" for her could not be
annotated at all, except by declaring her with no series in that paragraph
(a hack: then nothing is checked). And nothing tied the narration's pronouns
to the story: the narrator calls the stranger "they" until she says she is a
girl, then "she", and the model had no way to say that this is right, or that
"she" a paragraph earlier would have been a knowledge leak.
**Example.** The narration uses "their ankles" before she says she is a girl,
and "her ruined dress" in the clause after.
**Generalisation (implemented: `World/Identity.lean`, `Studio/Ext.lean`).**
Pronouns are what each character takes another's to be (unknown, assumed,
learned, told). Every pronoun, name and gendered noun ("boyfriend", "girl")
that refers to a character is held to its referrer's knowledge, in token
order: the narration to the point-of-view character's (unknown means "they"),
speech to the speaker's. A series that is not the person's must be read as a
`refer` event, which records misgendering, deliberate when the speaker knew
better (the men knew: one starts "sh-" and corrects to "he"), mistaken when
they had only assumed (the police chief's "boyfriend").

### 6. One name per character

**Failed.** She gives a nickname first and her real name only at the end; he
is told the nickname, asks whether it is a dead name, is told it is not, and
is asked to wait for the real one; she coins a nickname for him from a
smudged note; the police chief has a given name, a nickname and a title. The
base model has one `name` per character, known to all, so the narrator could
call her by a name nobody had said.
**Generalisation (implemented: `World/Identity.lean`).** Several names per
character, each with a kind (given, nick, family, title, coined, dead) and
the trust it takes to be told it; who knows which name is state;
`introduce`, `tellName`, `coin`, `call`; a dead name used is recorded.
**Found by it.** The text never shows how she learns the chief's nickname,
which she then uses: read as `learnName`, an assumption.

### 7. Disclosure is a privilege; outing is a harm

**Failed.** The chapter states its own norm: who is trans is nobody's
business, shared on a trust basis, and she applies the same rule to her real
name. The base model had no private facts: a fact is known or not, and
`confide` only bumps trust.
**Generalisation (implemented).** Private facts and private names carry the
trust needed to share them; `disclose` is allowed only at that trust, and
trust (a `Ties` relation) is raised by care. The generated `Ext.lean` proves,
for each gated disclosure, that it was not allowed at the opening
(`gated_i`): the care in between is what makes it possible. Learning a
private fact any other way (walking in on someone) is `out`, allowed and
recorded.

## Care, threat and ties

### 8. Care acts

**Failed.** Water, a torn dress noticed and clothes found, shoes, a jacket
against the cold, a drive, "take a breath": the base model has `give` (of a
plot object) and nothing else. Whether care was needed, and whether it was
wanted, was not representable, so neither was hurt/comfort.
**Generalisation (implemented: `World/Care.lean`).** Needs, declared per
story, created by `harm` and met by `tend`; `offer`/`accept`/`decline`; kinds
of care that touch someone need consent (explicit, or a recorded quiet
acceptance where the story allows it); tending raises the recipient's trust
in the carer.

### 9. Protecting someone from a threat

**Failed.** He sends her inside, faces three men with a shovel, lies that he
has seen nobody, and threatens them off his property. The base model can say
the lie and the moves; that he is protecting her from them, it cannot.
**Generalisation (implemented).** A threat is a `Ties` relation
(`threatens`, which by a declared law ends `friends`: "the only friends I had
just chased me"); `shield a c x` needs `x` to threaten `c`, and makes `a`
protect `c`.

### 10. Typed relations

**Failed.** Bonds are four fixed dimensions; the chapter needs friends,
roommates, threatens, protects, trusts, each with its own laws.
**Generalisation (implemented: `World/Ties.lean`).** Story-declared tie types,
graded, with `symmetric`, `excludes` and `requires` laws.

## Feeling

### 11. Emotion words were excused, not checked

**Failed.** "frightened", "teary", "trembling", "relieved", "bashful": an
adjective said of a character must be a trait or marked `impression`, so the
prose's feelings were waved through.
**Generalisation (implemented: `World/Affect.lean`).** Feelings are state,
appraised from other modules' events by story-declared rules (harm brings
distress, a threat fear, tending or shielding calms) plus `feel`/`calm` where
no rule applies; an emotion word said of a character must be backed by it.

### 12. Feelings that are bodily, mixed or caused by words

**Still open.** A wobbling lip, tight shoulders, a blush that blooms, tears
that fall and stop, a shaky exhale: bodily signs of a feeling, read only as
gestures or as atoms that are simply always true. Distress caused by his
*words* (his warning that the men are still out there) has no harmer but the
men. He wants to leave and the floor seems to hold him back: competing
desires have no representation. Embarrassment with a history ("since primary
school") has no time.
**Proposed.** Affect's `feel` with a cause (an event, possibly speech), signs
as observable consequences of a feeling (`shows c e`), and feelings with
intensity over time, so a scene can say a feeling is new.

### 13. Slow burn as a trajectory

**Failed.** The chapter's romance is all in his reactions: the eyes, the
freckles he tries not to count, the pull at his chest, the name that settles
somewhere it shouldn't. Bonds only move through flirting, confiding and
intimate acts, none of which happen, so the annotators claimed one static atom
("he is drawn to her") at every one of those moments. Nothing says the pull
grows, or is new.
**Proposed.** Attraction raised by appraisal (care given, a name shared, an
attractive detail noticed: an Affect rule into a Ties relation), and a
trajectory constraint per beat (`attraction katsuki deku` non-decreasing and
below the level of a confession until the beat that allows one), checked like
any claim.

### 14. Threats, taunts, teasing and banter

**Failed.** His threats ("I'll let you pick where your graves will be") and
the men's taunts are only lies of an atom (he would kill them; he has been to
jail), and that the men leave *because* of them is not modelled. The chief's
innuendo, the coined nickname used to tease, the affectionate insults: `hint`
needs a fact, `sarcasm` means the opposite, and neither is play.
**Proposed.** Speech acts as events with effects on Ties and Affect:
`threaten a b` (raises the target's fear; a reason for a move), `tease a b`
(raises closeness when the tie is warm, tension when not).

### 15. Speech the checker cannot hold

* **Elliptical answers.** "N-No.", "y-yes.", a bare name: no clause, so an
  `answer`, `disclose` or `introduce` must sit on a neighbouring verb, or the
  word must be faked as a verb. Proposed: a FRAG reply to a question is a
  clause whose head is its only content word.
* **Verbs of saying.** mutter, mumble, grumble, grunt, huff, bark, whisper
  are not read as saying, so what they say is judged `act`; "will", "won't",
  "gotta", "probably" are not modals.
* **"without X"** is not read as negation, so "without looking" counts as if
  he looked.
* **"like" similes** are not read as "as if".
* **Rhetorical questions in free indirect thought** ("He's gotta get them
  back, right?") mean their opposite; there is no `muses` or `doubts`.
* **Retracting a lie** ("I lied") is only the new statement, not a link to
  the old one; "Then you were right" calls back to her earlier claim with no
  link either.

### 16. Purposes and causes without facts

**Failed.** "to hide" (the dog), "to face him", "to pet the dog's ears", "to
hide the red heat on his cheek": a purpose clause needs a fact its agent
wants, and these have none, so the annotators read them as complements to dodge
the check. "the light shines only on part of the yard, so he doesn't see" has
no rule from light to seeing.
**Proposed.** Goals over Affect and Space predicates (`hidden c`, `facing a
b`), and perception conditions (light) as preconditions of `notice ... seen`.

### 17. Fixtures and the clause's subject

**Failed.** A clause whose subject is a fixture or scenery needs a fact about
it, so "the doors that lead into the house" and "his boots get kicked off"
needed made-up atoms; and a clause about the grass or the fence had to name the
yard, so readings carried claims like "Katsuki is in the yard" only to cover
the place. A layout relation (`leadsTo deckdoors house`) is a fact about the
doors but does not count.
**Proposed.** Layout and attributes count as facts about their things;
changes to scenery (boots off, engine on) as `make` on scenery states.
**Fixed along the way (721b3d5):** a way (a door) is seen from the place it
leads to; "'s" is not a plural.

### 18. Time skips and parallel scenes

**Failed.** "five minutes later", "a couple more minutes", "within seconds",
a ten-minute drive: readings left them as nouns with a time sense; nothing
puts them on the timeline, though metric constraints exist. "They get
interrogated separately": two interviews in two rooms at once, summarised
in verbless fragments; `meanwhile` is for cuts, not for a summary.
**Proposed.** Readings for duration phrases into `Metric.gap`/`dur`, and a
`summary` phase: a span of story time whose events are only listed.

### 19. One point of view

Chapter 1 keeps to his point of view, and `Spec.pov` is one character. The
work's later chapters alternate; `Ext`'s narration check would need the point
of view per paragraph (a `pov` field in each reading) to follow them. Not
needed for this chapter, so not done.

## What the generalisations proved

`python3 studio/workflows.py ext-prove stories/private-ao3-sweet-girl`
generates `Ext.lean` (private) and checks it with `decide +kernel`: the
ties, care, identity and affect reading of all 95 paragraphs is valid, every
name and pronoun is one its referrer knew; the harms on record are stated
exactly (who misgendered her, and whether they knew better); and each
trust-gated disclosure (that she is trans; her real name) is proved out of
reach at the opening, so the care between is what makes it possible.

At the end of the chapter the record says: the three men misgendered her
seven times, each knowing better (one also called her "it"), and the one she
lived with learned she is trans without being told; the chief misgendered
her once, having assumed. Her trust in him stands at 8, from eight acts of
care (safety, water, comfort, clothes, shoes, warmth, the drive, his number);
he protects her; her fear and distress have been eased but not gone.
