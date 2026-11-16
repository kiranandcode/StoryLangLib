# Power export: the shape every rule-based module emits for the Studio

`langlib power <story-dir>` prints one JSON object. Any module whose moves have
preconditions (Nen, Magic, Death Note, the next one) emits this shape, and the
Studio's **Power** view draws all of them alike. The module decides what its
actors, resources, marks and clocks are; the view decides nothing about them.

The rule for the Studio: everything is data the module computed in Lean. The
view never re-derives a verdict, and every state is written out in words as
well as drawn.

```jsonc
{
  "schema": 1,
  "system": "nen",                       // module id: nen | magic | deathnote | ...
  "title": "Nen: Chrollo against Hisoka",
  "story": "hxh-chrollo-hisoka",         // the story directory it belongs to
  "source": "LangLib/World/Examples/Fight.lean",
  "valid": true,                         // every move allowed, in order
  "failure": null,                       // or {"move": 17, "why": "..."}: the first refused move

  "actors": [                            // everyone the rules talk about
    {"id": "chrollo", "name": "Chrollo", "kind": "person"},   // kind: free text (person, copy, shinigami, ...)
    {"id": "c1", "name": "copy 1", "kind": "copy", "of": "fan"}
  ],
  "resources": [                         // pools that moves spend; [] for a resource-free system
    {"id": "aura", "label": "aura", "max": {"chrollo": 60, "hisoka": 40}}
  ],
  "glossary": {"in_": "In: hides aura"}, // optional: words for ids that need them

  "moves": [
    {
      "i": 0,                            // position in the whole run
      "para": "01",                      // the story paragraph it belongs to ("" if none)
      "at": 12,                          // optional: the token in that paragraph
      "actor": "chrollo",                // who acts ("" for the world)
      "kind": "use",                     // the module's event name
      "text": "Chrollo uses Black Voice on the judge, left hand",
      "raw": "use chrollo blackVoice judge left",
      "targets": ["judge"],
      "t": null,                         // optional: story time in seconds, for clocks
      "ok": true,
      "why": "",                         // the module's own refusal, when !ok
      "checks": [                        // EVERY precondition, evaluated, in the module's order
        {"id": "alive", "kind": "status", "label": "Chrollo is alive",
         "pass": true, "why": "they are dead"},                // why: what the module says if it fails
        {"id": "aura", "kind": "resource", "label": "aura 60 ≥ cost 2",
         "pass": true, "why": "not enough aura (60 < 2)"}
      ],
      "agrees": true,                    // the first failing check's why is the module's why (or none fail and ok)
      "state": { ... }                   // the state AFTER this move (shape below)
    }
  ],
  "start": { ... },                      // the state before the first move

  "counterfactuals": [                   // runs the module proves fail, and where
    {"id": "moon_needs_the_book_shut",
     "label": "The moon with the right hand while the book is open",
     "theorem": "LangLib.World.Fight.moon_needs_the_book_shut",
     "change": "p1, the first 3 moves of p2, then the moon with the right hand",
     "move": 6, "para": "02", "why": "the right hand holds the book",
     "checks": [ ... ]                   // the failing move's checks, as above
    }
  ]
}
```

## State

```jsonc
{
  "actors": {
    "chrollo": {
      "status": ["present", "mobile"],   // flags that hold: present, gone, hidden, mobile, controlled, ...
      "resources": {"aura": 58},
      "fields": [                        // anything else, as labelled values
        {"key": "techs", "label": "techniques up", "value": ["gyo"]},
        {"key": "hands", "label": "free hands", "value": ["left"]},
        {"key": "book", "label": "book", "value": "held, open at Black Voice; bookmark: none"}
      ],
      "marks": [                         // what is on this actor, put there by someone
        {"kind": "antenna", "by": "chrollo", "via": "Black Voice", "note": "hidden (In)"}
      ]
    }
  },
  "active": [                            // standing effects: sustained abilities, contracts, ...
    {"by": "chrollo", "what": "Black Voice", "on": ["judge"]}
  ],
  "relations": [                         // directed pairs worth drawing: control, likeness, knows-name, ...
    {"from": "chrollo", "to": "judge", "kind": "controls", "label": "controls (antenna)"}
  ],
  "clocks": [                            // time windows (Death Note: 40 s, 6 min 40 s); [] if none
    {"id": "d1", "label": "heart attack: Lind L. Tailor", "actor": "light", "target": "tailor",
     "start": 0, "due": 40, "status": "running"}   // running | done | void
  ],
  "knowledge": [                         // optional: what the rules' preconditions read from minds
    {"who": "light", "of": "l", "what": "face", "holds": false, "true": true}
  ]
}
```

## Conventions

- **Check kinds** group the conditions in the view: `status` (alive, present,
  in Zetsu), `resource` (aura, mana), `possession` (owns the ability, the
  notebook), `body` (hands, head), `position` (reach, same place), `support`
  (book page or bookmark), `target` (what the target must be), `knowledge`
  (knows the face, the real name), `time` (inside a window), `rule` (anything
  else). Unknown kinds are drawn as `rule`.
- **Every** check is listed even after one fails; `agrees` is the module's own
  test that the list and its `why` say the same thing.
- Ids are plain strings; `text` and `label` are sentences for people.
- Moves are in story order; `para` links each to its paragraph, so the view
  follows the reading line.
- Sizes: the full state after every move is fine for a few hundred moves.
