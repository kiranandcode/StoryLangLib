"""Writes story.json for roof-eleven (kept as a script so the world reads as one place)."""
import json
from pathlib import Path

KIRAN_NOTES = (
    "In her words: Kiran doesn't have any friends; she only has her research. She lacks a sense of humanity "
    "that others have, and never had it, even before being disowned; she's an excellent researcher because of "
    "that. Most people need social support to live, like air, but she's been deprived of it so long she doesn't "
    "know what it feels like to even need it. "
    "For the model: a computer-science researcher (verification, proofs) who works past midnight most nights; "
    "trans, out at work; disowned by her family when she came out, and did not notice the absence the way people "
    "expect, which she takes as a finding about herself. Confident and proud in her work, blunt, literal, honest "
    "to a fault, skeptical of any claim without data. She does not register hunger, tiredness, loneliness or the "
    "wish to be comforted in herself, nor the need for comfort or reassurance in others, unless someone points "
    "it out or asks outright (story.json ext.blind). Affection and desire arrive as anomalies in her own data "
    "(pulse, lost concentration, heat) that she tries to explain away before they read as want (ext.anomaly). "
    "She can come to know, as a fact, that she needs company; she cannot feel lonely. Not to be recited in the prose.")

story = {
  "title": "Eleven, on the Roof (Kiran's version)",
  "pov": "kiran",
  "characters": [
    {"id": "kiran", "name": "Kiran", "pron": "she",
     "traits": ["skeptical", "confident", "proud", "honest"],
     "values": ["curiosity", "pride", "honesty", "desire", "safety"], "notes": KIRAN_NOTES},
    {"id": "theo", "name": "Theo", "pron": "he",
     "traits": ["confident", "honest", "romantic", "dominant"],
     "values": ["desire", "honesty", "curiosity", "pride"],
     "notes": "A visiting engineer from the hardware partner, three weeks in the lab bringing up its new GPU cluster; "
              "tomorrow is his last day. Direct, warm, unhurried; notices what people need and says it. Has come back "
              "to the lab after hours four nights running, for her. Likes to lead in bed, and will not act on 'whatever "
              "you want': he makes her name it, and checks in."},
    {"id": "mara", "name": "Mara", "pron": "she",
     "traits": ["romantic", "openMinded", "loyal"],
     "values": ["loyalty", "desire", "curiosity", "safety"],
     "notes": "Kiran's labmate of three years at the next desk; warm, quick to hope, a little in love with the idea of "
              "Theo. Counts Kiran as a friend and knows Kiran does not count anyone; says what she needs out loud "
              "because she has learned Kiran will not guess."},
    {"id": "family", "name": "her family", "pron": "they", "traits": ["proud", "stubborn"], "values": ["pride", "duty"],
     "notes": "Kiran's parents, offstage: they cut her off when she came out."}
  ],
  "places": [
    {"id": "lab", "kind": "a computer science lab, open plan, after hours", "words": ["lab"],
     "attrs": {"kind": "computer"},
     "fixtures": [
       {"id": "kdesk", "what": "Kiran's desk, in the corner by the window", "words": ["desk", "corner"], "owner": "kiran", "count": 1},
       {"id": "tdesk", "what": "the hot desk on Kiran's left that Theo has borrowed for three weeks", "words": ["desk"], "count": 1, "attrs": {"state": "bare"}},
       {"id": "mdesk", "what": "Mara's desk, on Kiran's right", "words": ["desk"], "owner": "mara", "count": 1},
       {"id": "shelf", "what": "the shelf over Kiran's and Mara's desks, which they share", "words": ["shelf"], "count": 1, "attrs": {"use": "shared"}},
       {"id": "kchair", "what": "Kiran's chair", "words": ["chair"], "owner": "kiran", "count": 1},
       {"id": "whiteboard", "what": "the whiteboard by Kiran's desk, covered in her proof", "words": ["whiteboard", "board"], "count": 1},
       {"id": "window", "what": "the window by Kiran's desk", "words": ["window"], "count": 1},
       {"id": "rack", "what": "the rack of the new GPU cluster at the far end of the lab", "words": ["rack", "cluster"], "count": 1},
       {"id": "labdoor", "what": "the lab door", "words": ["door"], "count": 1},
       {"id": "laptop", "what": "Kiran's laptop", "words": ["laptop", "screen"], "owner": "kiran", "count": 1},
       {"id": "corridor", "what": "the corridor from the lab to the kitchen and the quiet room", "words": ["corridor", "hall"], "count": 1},
       {"id": "stairs", "what": "the stairs up to the roof", "words": ["stair", "stairs", "stairwell"]}
     ]},
    {"id": "kitchen", "kind": "the small shared kitchen down the corridor", "words": ["kitchen"],
     "fixtures": [{"id": "coffeemachine", "what": "the kitchen's coffee machine", "words": ["machine"], "count": 1}]},
    {"id": "roof", "kind": "the flat roof of the building, over the city", "words": ["roof"], "outdoor": True,
     "fixtures": [
       {"id": "ledge", "what": "the low wall at the roof's edge", "words": ["ledge", "wall", "parapet"], "count": 1, "attrs": {"height": "low"}},
       {"id": "city", "what": "the city below, seen from the roof", "words": ["city"], "count": 1},
       {"id": "roofdoor", "what": "the door at the top of the stairs, which sticks", "words": ["door"], "count": 1},
       {"id": "tank", "what": "the water tank on its steel legs, with a lee out of the wind", "words": ["tank"], "count": 1, "attrs": {"kind": "water"}}
     ]},
    {"id": "quietRoom", "kind": "the quiet room off the corridor, where people nap through long runs", "words": ["room"],
     "attrs": {"kind": "quiet"},
     "fixtures": [
       {"id": "couch", "what": "the long couch under the window", "words": ["couch", "sofa"], "count": 1},
       {"id": "qlamp", "what": "the one floor lamp, on low", "words": ["lamp"], "count": 1, "attrs": {"light": "low"}},
       {"id": "qdoor", "what": "the quiet room's door, which locks from inside", "words": ["door", "lock"], "count": 1}
     ]}
  ],
  "objects": [{"id": "note", "what": "Theo's note, a page torn from his notebook", "words": ["note", "page", "paper"], "owner": "theo"}],
  "scenery": [
    {"id": "noodles", "what": "the takeaway noodles Theo brings", "words": ["noodles", "carton", "container"], "owner": "theo", "count": 2},
    {"id": "mug", "what": "Kiran's mug", "words": ["mug", "cup"], "owner": "kiran", "count": 1},
    {"id": "notebook", "what": "Theo's notebook", "words": ["notebook"], "owner": "theo", "count": 1},
    {"id": "coat", "what": "Theo's coat", "words": ["coat", "jacket"], "owner": "theo", "count": 1},
    {"id": "charger", "what": "Mara's laptop charger", "words": ["charger"], "owner": "mara", "count": 1},
    {"id": "blanket", "what": "the quiet room's blanket", "words": ["blanket"], "count": 1},
    {"id": "bottle", "what": "a bottle of water", "words": ["bottle", "water"], "count": 1}
  ],
  "layout": ["leftOf tdesk kdesk", "rightOf mdesk kdesk", "above shelf kdesk", "above shelf mdesk",
             "near kdesk window", "near whiteboard kdesk", "at kchair kdesk", "farFrom rack kdesk",
             "leadsTo corridor kitchen", "leadsTo corridor quietRoom", "leadsTo stairs roof",
             "near ledge city", "near tank ledge"],
  "atoms": [
    {"id": "noteForKiran", "label": "the note is for Kiran", "truth": True, "group": "noteFor", "who": ["theo", "kiran"]},
    {"id": "noteForMara", "label": "the note is for Mara", "truth": False, "group": "noteFor", "who": ["theo", "mara"]},
    {"id": "theoLikesKiran", "label": "Theo wants Kiran", "truth": True, "group": "theoLikes", "who": ["theo", "kiran"]},
    {"id": "theoLikesMara", "label": "Theo wants Mara", "truth": False, "group": "theoLikes", "who": ["theo", "mara"]},
    {"id": "kiranLikesTheo", "label": "Kiran wants Theo", "truth": True, "who": ["kiran", "theo"]},
    {"id": "theoReturns", "label": "Theo has come back to the lab after hours four nights running", "truth": True, "who": ["theo"]},
    {"id": "theoLeaving", "label": "tomorrow is Theo's last day in the lab", "truth": True, "who": ["theo"]},
    {"id": "kiranFed", "label": "Kiran has eaten since morning", "truth": False, "state": True, "who": ["kiran"]},
    {"id": "noodlesHot", "label": "the noodles are still hot", "truth": True, "about": "noodles", "kind": "condition"},
    {"id": "kiranAlone", "label": "Kiran has worked alone in the lab every night for three years", "truth": True, "who": ["kiran"]},
    {"id": "kiranFriendless", "label": "Kiran counts nobody as a friend", "truth": True, "who": ["kiran"]},
    {"id": "maraFriend", "label": "Mara counts Kiran as a friend", "truth": True, "who": ["mara", "kiran"]},
    {"id": "kiranDisowned", "label": "Kiran's family cut her off when she came out", "truth": True, "who": ["kiran", "family"]},
    {"id": "kiranTrans", "label": "Kiran is trans", "truth": True, "who": ["kiran"]},
    {"id": "labEmptied", "label": "everyone else has gone home from the lab", "truth": True},
    {"id": "clusterHum", "label": "the cluster hums at the far end of the lab", "truth": True, "about": "rack", "kind": "sound", "perceptible": True},
    {"id": "proofStuck", "label": "Kiran's proof is stuck on one lemma", "truth": True, "about": "whiteboard", "kind": "condition"},
    {"id": "coffeeSlow", "label": "the coffee machine takes its time", "truth": True, "about": "coffeemachine", "kind": "condition"},
    {"id": "cold", "label": "it is cold and windy on the roof", "truth": True, "kind": "weather", "perceptible": True},
    {"id": "cityLit", "label": "the city below is lit", "truth": True, "about": "city", "kind": "light", "perceptible": True},
    {"id": "roofDoorSticks", "label": "the roof door sticks", "truth": True, "about": "roofdoor", "kind": "condition"},
    {"id": "tankLee", "label": "the water tank breaks the wind", "truth": True, "about": "tank", "kind": "condition"},
    {"id": "lampLow", "label": "the quiet room's lamp is on low", "truth": True, "about": "qlamp", "kind": "light", "perceptible": True},
    {"id": "qdoorLocked", "label": "the quiet room's door is locked", "truth": False, "state": True, "about": "qdoor", "kind": "condition"}
  ],
  "lore": [{"if": ["noteForKiran"], "then": "theoLikesKiran"}, {"if": ["noteForMara"], "then": "theoLikesMara"}],
  "lexicon": [
    {"verb": "want", "subj": "theo", "obj": "kiran", "lit": "theoLikesKiran"},
    {"verb": "like", "subj": "theo", "obj": "kiran", "lit": "theoLikesKiran"},
    {"verb": "want", "subj": "theo", "obj": "mara", "lit": "theoLikesMara"},
    {"verb": "like", "subj": "theo", "obj": "mara", "lit": "theoLikesMara"},
    {"verb": "want", "subj": "kiran", "obj": "theo", "lit": "kiranLikesTheo"}
  ],
  "plans": [
    {"id": "coffeeRun", "agent": "kiran", "goal": "at(kiran,lab)", "steps": ["move kiran kitchen", "move kiran lab"]},
    {"id": "theNote", "agent": "theo", "goal": "at(kiran,roof)", "steps": ["drop theo note", "move theo roof"]},
    {"id": "maraUp", "agent": "mara", "goal": "at(mara,roof)", "steps": ["take mara note", "move mara roof"]},
    {"id": "theRoom", "agent": "theo", "goal": "qdoorLocked", "steps": ["move theo quietRoom", "make theo qdoorLocked"]}
  ],
  "start": {
    "at": {"kiran": "lab"},
    "holds": {"note": "theo"},
    "bonds": {
      "kiran>theo": {"trust": 1, "attraction": 1},
      "theo>kiran": {"trust": 2, "affection": 2, "attraction": 3},
      "kiran>mara": {"trust": 2},
      "mara>kiran": {"trust": 2, "affection": 2},
      "mara>theo": {"trust": 1, "attraction": 2},
      "theo>mara": {"trust": 1}
    },
    "knows": {
      "kiran": ["kiranTrans", "kiranDisowned", "kiranFriendless", "theoLeaving", "kiranAlone", "proofStuck"],
      "theo": ["theoLikesKiran", "noteForKiran", "!noteForMara", "!theoLikesMara", "theoLeaving", "theoReturns", "kiranTrans", "!kiranFed"],
      "mara": ["maraFriend", "kiranFriendless", "kiranAlone", "theoLeaving", "kiranTrans"]
    }
  },
  "beats": {
    "conds": ["lingering", "spark", "noteLeft", "misread", "maraGone", "truthOut", "together", "kiranKnows",
              "tested", "kissed", "negotiated", "bare", "paused", "lovers", "stays"],
    "init": [],
    "vocab": [
      {"id": "lingers", "label": "Theo comes back, with dinner", "add": ["lingering"], "keys": ["move theo lab"]},
      {"id": "spark", "label": "He flirts; she logs an anomaly", "pre": ["lingering"], "add": ["spark"], "keys": ["flirt theo kiran"]},
      {"id": "note", "label": "Theo leaves a note and goes up", "pre": ["spark"], "add": ["noteLeft"], "keys": ["drop theo note"]},
      {"id": "misread", "label": "Mara finds the note and reads it as hers", "pre": ["noteLeft"], "add": ["misread"], "keys": ["notice mara noteForMara inferred"]},
      {"id": "maraUp", "label": "Mara goes up; Kiran cannot work", "pre": ["misread"], "add": ["maraGone"], "keys": ["move mara roof"]},
      {"id": "amends", "label": "Mara comes down with the truth, and says what Kiran needs", "pre": ["maraGone"], "add": ["truthOut"], "keys": ["tell mara kiran noteForKiran"]},
      {"id": "climb", "label": "Kiran goes up", "pre": ["truthOut"], "add": ["together"], "keys": ["move kiran roof"]},
      {"id": "confess", "label": "Theo says it plainly; she reports her data", "pre": ["together"], "add": ["kiranKnows"], "keys": ["tell theo kiran theoLikesKiran"]},
      {"id": "test", "label": "She proposes an experiment: a kiss", "pre": ["kiranKnows"], "add": ["tested"], "keys": ["askAct kiran theo kiss"]},
      {"id": "kiss", "label": "The kiss, and the result", "pre": ["tested"], "add": ["kissed"], "keys": ["act kiran theo kiss"]},
      {"id": "negotiate", "label": "He won't take 'whatever you want'; she names it", "pre": ["kissed"], "add": ["negotiated"], "keys": ["askAct theo kiran sex"]},
      {"id": "undress", "label": "The quiet room; undressing", "pre": ["negotiated"], "add": ["bare"], "keys": ["act theo kiran undress"]},
      {"id": "pause", "label": "Too much data: she stops him, and he stops", "pre": ["bare"], "add": ["paused"], "keys": ["withdraw kiran theo sex"]},
      {"id": "sex", "label": "Sex, asked for again", "pre": ["paused"], "add": ["lovers"], "keys": ["act theo kiran sex"]},
      {"id": "stay", "label": "Aftercare; she asks him to stay", "pre": ["lovers"], "add": ["stays"], "keys": ["request kiran theo at(theo,quietRoom)"]}
    ],
    "story": ["lingers", "spark", "note", "misread", "maraUp", "amends", "climb", "confess", "test", "kiss",
              "negotiate", "undress", "pause", "sex", "stay"]
  },
  "outline": [
    {"beat": "lingers", "brief": "Nearly half past ten. Kiran alone in the lab with a stuck lemma, the cluster humming. Theo comes back for the fourth night running, with an excuse (the cluster's fans) and two cartons of noodles. He has noticed she has not eaten since morning and says so; she had not registered it, and accepts the food as fuel. She logs the fourth return as a datum."},
    {"beat": "spark", "brief": "He sits on the borrowed desk and flirts, plainly: he did not come back for the fans. She answers literally and deflates it; he reads her and grins. Her pulse does something; she logs it as an anomaly and tries an explanation (caffeine)."},
    {"beat": "note", "brief": "Kiran goes to the kitchen for coffee (she means to come straight back). Meanwhile Theo writes a note, unaddressed but initialled ('Roof, eleven. I want to ask you something, and not under these lights. -T'), leaves it on the shelf over Kiran's and Mara's desks, under Kiran's mug, and goes up to the roof."},
    {"beat": "misread", "brief": "Kiran comes back to find Mara, back for her charger, holding the note and glowing: she reads it as hers. Mara tells Kiran Theo has asked her up. Something drops in Kiran's stomach; she logs it as data and does not name it. Mara asks outright to be told she is not imagining it, and only then does Kiran give reassurance, precise and dry."},
    {"beat": "maraUp", "brief": "Mara checks her reflection in the dark window and goes up at eleven. Kiran, alone, cannot write a line; she tests explanations for the anomaly (hunger: no, she ate; fatigue) and finds none that fits."},
    {"beat": "amends", "brief": "Mara comes back down ten minutes later, red and laughing at herself: Theo told her, kindly, it was for Kiran. She tells Kiran so, and then tells Kiran what Kiran needs: she has eaten alone at that desk for three years; she should go up. Mara asks for something nice to be said to her, and Kiran says it."},
    {"beat": "climb", "brief": "Kiran takes the stairs. The roof door sticks; she shoulders it. Cold wind, the city lit below. Theo by the ledge, in the lee of the water tank."},
    {"beat": "confess", "brief": "Kiran opens with the methodology: the note had no addressee. Theo says plainly that it was for her, that he wants her, that the fans were a lie four nights running. She reports her data back: the pulse, the lost lemma, the drop when Mara said the note was hers. He offers a hypothesis."},
    {"beat": "test", "brief": "She proposes an experiment: she asks, out loud, whether she can kiss him, to see. He says yes, and that if the result is null she has to tell him."},
    {"beat": "kiss", "brief": "The kiss, in the lee of the tank. The result is not null. Desire arrives as data first and then, mid-kiss, reads as itself; for the first time she says she wants him."},
    {"beat": "negotiate", "brief": "He asks what she wants. She offers him whatever he wants and to take notes; he refuses: she has to name it. She names it: his hands, his mouth, his hands holding her wrists; no marks above the collar (a talk on Friday); a safeword, 'null'. He names what he wants. Both say yes out loud."},
    {"beat": "undress", "brief": "The quiet room down the corridor; he locks the door; the lamp on low. Undressing, his check-in before he takes off the rest, her yes."},
    {"beat": "pause", "brief": "On the couch, his hands pinning her wrists as asked, his fingers in her: too much signal at once. She says 'wait' and he stops at once, hands off, and asks. She takes stock, out loud, and says yes again, and what she wants next."},
    {"beat": "sex", "brief": "He fucks her, slow and then not, checking in; she comes, and for once she does not narrate it."},
    {"beat": "stay", "brief": "Aftercare: water, the blanket; he points out she is shaking and that she needs looking after, and she lets him. She tells him about her family as a fact. Then she asks him to stay, because she has been told she needs company, not because she feels it; she files it under things to understand."}
  ],
  "ext": {
    "ties": [{"id": "friends"}, {"id": "colleagues", "symmetric": True}, {"id": "family", "symmetric": True},
             {"id": "estranged", "symmetric": True, "excludes": ["family"]}, {"id": "trusts"}],
    "needs": [{"id": "food"}, {"id": "rest"}, {"id": "company"}, {"id": "comfort"}, {"id": "reassurance"},
              {"id": "warmth"}, {"id": "water"}],
    "builds": "trusts", "trust": "trusts",
    "names": {"kiran": [["Kiran", "given", 0]], "theo": [["Theo", "given", 0], ["T", "nick", 0]], "mara": [["Mara", "given", 0]], "family": []},
    "blind": [["kiran", "self", "food"], ["kiran", "self", "rest"], ["kiran", "self", "company"],
              ["kiran", "self", "comfort"], ["kiran", "self", "warmth"], ["kiran", "self", "water"],
              ["kiran", "others", "comfort"], ["kiran", "others", "company"], ["kiran", "others", "reassurance"]],
    "emotions": {"affection": ["fond", "tender", "affectionate", "smitten"],
                 "desire": ["aroused", "desperate", "eager", "wanting"],
                 "hurt": ["hurt", "jealous", "stung", "wounded"],
                 "lonely": ["lonely", "lonesome"],
                 "embarrassment": ["embarrassed", "mortified", "flustered", "red"],
                 "relief": ["relieved", "calm", "loose"]},
    "anomaly": [["kiran", "affection", "2"], ["kiran", "desire", "1"], ["kiran", "hurt", "9"]],
    "signals": {"lonely": "company"},
    "appraise": [["tend", "comfort", "relief", "1"], ["tend", "reassurance", "relief", "1"]],
    "start": {
      "needs": {"kiran": ["food", "rest", "company", "comfort"], "mara": ["reassurance"]},
      "ties": [["kiran", "estranged", "family", "1"], ["family", "estranged", "kiran", "1"],
               ["kiran", "colleagues", "mara", "1"], ["mara", "colleagues", "kiran", "1"],
               ["kiran", "colleagues", "theo", "1"], ["theo", "colleagues", "kiran", "1"],
               ["mara", "friends", "kiran", "1"],
               ["kiran", "trusts", "mara", "2"], ["mara", "trusts", "kiran", "2"], ["theo", "trusts", "kiran", "1"]],
      "names": [["kiran", "theo", "Theo"], ["kiran", "mara", "Mara"], ["theo", "kiran", "Kiran"],
                ["theo", "mara", "Mara"], ["mara", "kiran", "Kiran"], ["mara", "theo", "Theo"]],
      "pron": [["kiran", "theo", "he"], ["kiran", "mara", "she"], ["kiran", "family", "they"], ["theo", "kiran", "she"],
               ["theo", "mara", "she"], ["mara", "kiran", "she"], ["mara", "theo", "he"]]
    }
  },
  "consent": {"never": {"kiran": ["pinDown"]},
              "relations": [["kiran", "mara", "acquaintances"], ["kiran", "theo", "acquaintances"]]}
}
Path(__file__).with_name("story.json").write_text(json.dumps(story, indent=1, ensure_ascii=False) + "\n")
