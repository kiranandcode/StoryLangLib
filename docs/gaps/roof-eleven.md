# Gaps: a persona who doesn't know she needs people

`stories/roof-eleven` retells the roof story with Kiran's own persona, in her
words: she has no friends, only her research; she lacks a sense of humanity
others have, and never had it; most people need social support like air, but
she has gone without it so long she doesn't know what needing it feels like.
The task was to model that formally, so the checker would call a move out of
character if the prose made her act like someone who knows she needs people,
and to keep an explicit romance with Theo inside the consent model.

Each gap below gives what failed (or what the model could not say), a minimal
example, and the generalisation, with where it now lives if it was
implemented.

## 1. Needs a persona doesn't register (implemented: `World/Care.lean`)

**Failed.** Care assumed the carer sees the need: `offer` and `tend` only
asked that the need exist. Nothing said that Kiran works through hunger
without noticing, or that she would not see Mara's need to be reassured.

**Example.** Kiran, unprompted, tells Mara she looks lovely and should go up.
The old model allowed it (`offer kiran mara reassurance`).

**Generalisation.** `CareSight.blind a c k`: `a` does not register `c`'s need
`k` unprompted (`a = c` for one's own). Three events are new: `register`
(noticing, ruled out where `a` is blind), `point b a c k` (someone tells
`a`), and `seek c a k` (asking for care, which needs the asker to know the
need). Offering or giving care needs the carer to be aware of the need. With
nobody blind, nothing changes (`aware_of_sighted`); the gates are theorems
(`blind_no_offer`, `blind_no_seek`, `blind_no_register`). In the story, Theo
has to say she hasn't eaten before she can take the noodles (01), and Mara
has to ask outright before Kiran can reassure her (04) or comfort her (06).

## 2. Knowing a need is not feeling it (implemented: `Care.felt`, `Affect.signals`)

**Failed.** The persona's sharpest line is that Kiran can come to know she
needs people without knowing what it feels like. Registering a need was one
bit.

**Generalisation.** A registration records how it came: noticed (felt) or
told (known). A story can make a feeling the felt sign of a need
(`"signals": {"lonely": "company"}`), and that feeling needs the need felt.
So after Mara tells her she needs people (06), Kiran may ask Theo to stay
(`seek kiran theo company`, 15). The model rules out her feeling lonely,
before or after (`feel_sign_blind`). Her last lines in the story say this in
her own terms.

## 3. Feelings that arrive as data (implemented: `World/Affect.lean`, `ReadEv`)

**Failed.** Affect had levels and nothing else: a feeling, once present, was
itself. Kiran's affection and desire arrive as anomalies in her own data
(pulse, a lost lemma, a fall under the ribs) that she tries to explain away.

**Generalisation.** `AffectReading.anomaly c e = some n`: `c` must `examine`
the feeling `n` times before it can be recognised. It must be recognised
(`recognise`) before it can be owned as a want (`own`: "I want you"). Until
then, a word naming the feeling, said of her, is flagged. Theorems:
`recognise_needs_examination` and `own_needs_reading`. In the story she tries
caffeine (02) and her own data (08) on her affection; she tries caffeine,
cold, adrenaline and height on her desire (10). Only then does it read as a
want, and only then does she say it. The hurt she feels when Mara claims the
note is examined three times and never recognised.

## 4. Predicative feeling words went unchecked (implemented: `Ext.feelsOf`)

**Failed (found by testing the finished story).** The emotion-word check read
only attributive adjectives ("a frightened girl"). "She was jealous", added to
paragraph 05 on a scratch copy, passed, although jealousy (hurt) is still an
unexamined anomaly for her. So did Mara's "I'm mortified".

**Generalisation.** `Ext` now also reads predicative adjectives: an adjective
heading a clause with a copula, or with a contracted one in the subject
("I'm"), whose subject refers to a character. The shared completeness rules
are untouched. Tested on scratch copies: "She was jealous" and "She was fond"
added to 05 are now flagged as out of character; "She was fond" added to 15,
after recognition, passes. roof-eleven's own reading stays valid. The
stricter check also finds one sentence in the private sweet-girl chapter
(paragraph 93): a predicative word for his embarrassment that no event backs.
That reading is now invalid there until it gets a `feel`. I did not edit the
private story.

## 5. Ties from one side (worked; one law missing)

`Ties` relations need not be symmetric, so "Mara counts Kiran as a friend"
holds while Kiran counts no one; `estranged` (symmetric) excludes `family`.
**Still open:** a persona-level law that a character does not start a tie
(no `relate kiran friends _` until ...). As it stands, `friends` is gated
only by trust, which Theo's care raises to 4 by the end.

## 6. Personas in Social can't see Affect (open)

Social's in-character rules for `flirt` and `agree` read traits and bond
levels only. The `Trait` set is closed, so it has no "detached", and adding
one would change shared matches (`Mind.lean`, `Parse.lean`). Kiran's
coarse-grained `agree` to the kiss is in character for an uninteresting
reason: no rule fires either way, because her trust in Theo is 1. Similarly,
`Consent.wish` (wanting an act) does not consult `Affect`'s recognition; the
two readings are separate files. **Proposed:** let a story's rules read the
other readings' state (a desire recognised before a `wish`; an anomaly not
yet read blocks a `flirt` by her), and open `Trait` to story-declared traits
as `Ties` did for relations.

## 7. Smaller ones

* **A flashback across paragraphs.** "Up on the roof, Theo had told her ..."
  (06), read as a `flashback`, could not be ordered after Mara's move to the
  roof in 05, so it came out as an assumption. It is read in story order
  instead, which is what happened.
* **Polarity forced by negation.** "You haven't eaten" is a negated clause,
  so its `tell` must carry a negative literal. The atom became `kiranFed`
  (false at the start) rather than `kiranUnfed`.
* **Evidence strength, not stubbornness.** A first draft gave Kiran
  `stubborn`, and the checker showed she then could never revise "Theo wants
  Mara". Without it, a skeptic still discounts testimony, so she comes to
  believe Theo only by watching his face (`sensed`), not by being told.
* **Protection is not in the act set.** A condom is scenery; `Intim` has no
  barrier, so "finishing inside" with and without one is the same act. Left
  unmodelled.
* **Copulas with a phrase as predicate** anchor at the phrase's first token
  ("It was *the* simplest explanation").
* **The Studio** was not running on :5177 during the session, and :8765 (the
  API port `workflows.py` asks) was held by another app, so `prove` fell
  back to local runs under the shared Lean lock.
