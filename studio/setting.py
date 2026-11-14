"""The setting: what each place is and has, the things characters carry, and
how the fixed things are laid out, checked against the prose.

story.json declares, besides the plot ids langlib checks:

    "places":  [{"id": "lab", "kind": "computer lab", "desc": "...",
                 "fixtures": [{"id": "kdesk", "what": "Kiran's corner desk", "words": ["desk", "corner"]}],
                 "excludes": ["bench", "fume hood", "centrifuge"]}]
    "scenery": [{"id": "scarf", "what": "Ran's scarf", "of": "ran", "words": ["scarf"]}]
    "layout":  ["leftOf rdesk kdesk", "backToBack rowA rowB", ...]

and each reading (NN.events.json) lists, beside its events,

    "things":  [{"t": "kdesk", "at": 21, "w": "desk"}]            every physical thing or place named
    "staging": [{"s": "leftOf rdesk kdesk", "at": 110, "w": "left"}]  every spatial relation asserted

The checks, all deterministic:
  1. every thing the reading names is declared (a place, plot object, fixture or scenery);
  2. a fixture is only named while someone is at its place (or in a flashback / recalled item);
  3. every noun whose word belongs to a declared thing is listed in `things` (the reading missed it);
  4. no word a scene place excludes appears in the prose (this needs no reading at all);
  5. every staging relation is in the layout, up to symmetry and inverses.
"""

from __future__ import annotations

import json
from pathlib import Path

SYMMETRIC = {"beside", "backToBack", "facing", "near", "farFrom", "across"}
INVERSE = {"leftOf": "rightOf", "rightOf": "leftOf", "above": "below", "below": "above"}
DIRECTED = {"in", "on", "at", "partOf", "leadsTo"}
RELATIONS = SYMMETRIC | set(INVERSE) | DIRECTED
IMPLIES = {"leftOf": "beside", "rightOf": "beside"}

RELATION_TEXT = """\
Staging relations (fixed things only, never people or the plot objects that move):
  beside A B   backToBack A B   facing A B   near A B   farFrom A B   across A B   (symmetric)
  leftOf A B   rightOf A B   above A B   below A B   (A is left of B as one sits at B; leftOf implies beside)
  in A B   on A B   at A B   partOf A B   leadsTo A B   (A is in / on / at / part of B; A leads to place B)"""


def fixtures(spec: dict) -> dict[str, dict]:
    """Every declared thing by id: places, plot objects, fixtures (with their place), scenery."""
    out = {}
    for p in spec.get("places", []):
        out[p["id"]] = {"kind": "place", "what": p.get("kind", p["id"]), "words": [p["id"]] + p.get("words", [])}
        for f in p.get("fixtures", []):
            out[f["id"]] = {"kind": "fixture", "place": p["id"], "what": f.get("what", f["id"]), "words": f.get("words", [])}
    for o in spec.get("objects", []):
        out[o["id"]] = {"kind": "object", "what": o.get("what", o["id"]), "words": o.get("words", [])}
    for s in spec.get("scenery", []):
        out[s["id"]] = {"kind": "scenery", "of": s.get("of"), "what": s.get("what", s["id"]), "words": s.get("words", [])}
    return out


def world_lines(spec: dict) -> list[str]:
    """The setting as the reader sees it in `extract` (part of world_text, so of world_sha)."""
    lines = ["Setting (what each place is and has):"]
    for p in spec.get("places", []):
        if not (p.get("kind") or p.get("fixtures") or p.get("excludes")):
            continue
        lines.append(f"  {p['id']}: {p.get('kind', '')}" + (f"; {p['desc']}" if p.get("desc") else ""))
        for f in p.get("fixtures", []):
            lines.append(f"    {f['id']}: {f.get('what', '')}")
        if p.get("excludes"):
            lines.append(f"    never here: {', '.join(p['excludes'])}")
    if spec.get("scenery"):
        lines.append("Scenery (things people carry or use, not plot objects):")
        lines += [f"  {s['id']}: {s.get('what', '')}" + (f" (of {s['of']})" if s.get("of") else "") for s in spec["scenery"]]
    if spec.get("layout"):
        lines.append("Layout: " + "; ".join(spec["layout"]))
    return lines if len(lines) > 1 else []


def closure(layout: list[str]) -> set[tuple[str, str, str]]:
    facts = set()
    for line in layout:
        r, a, b = line.split()
        facts.add((r, a, b))
        if r in SYMMETRIC:
            facts.add((r, b, a))
        if r in INVERSE:
            facts.add((INVERSE[r], b, a))
        if r in IMPLIES:
            facts |= {(IMPLIES[r], a, b), (IMPLIES[r], b, a)}
    return facts


def layout_problems(spec: dict) -> list[str]:
    known = fixtures(spec)
    out = []
    for line in spec.get("layout", []):
        parts = line.split()
        if len(parts) != 3 or parts[0] not in RELATIONS:
            out.append(f"layout '{line}': write it as RELATION A B with RELATION one of {', '.join(sorted(RELATIONS))}")
            continue
        out += [f"layout '{line}': '{x}' is not a declared place, fixture or scenery" for x in parts[1:] if x not in known]
    return out


def leaves(doc: dict) -> list[dict]:
    def walk(t):
        return [t] if "w" in t else [x for k in t["k"] for x in walk(k)]
    return [x for s in doc.get("sentences", []) for x in walk(s)]


def scene_places(spec: dict, before: list[str], now: list[str]) -> set[str]:
    """Where anyone is at the start of the paragraph, and wherever anyone goes during it."""
    at = dict(spec.get("start", {}).get("at", {}))
    for e in before:
        p = e.split()
        if p[:1] == ["move"] and len(p) == 3:
            at[p[1]] = p[2]
    places = set(at.values())
    for e in now:
        p = e.split()
        if p[:1] == ["move"] and len(p) == 3:
            places.add(p[2])
    return places


def problems(spec: dict, toks: list[str], doc: dict | None, reading: dict, before: list[str]) -> list[str]:
    """What is wrong with the paragraph's setting, as the writer should hear it."""
    known = fixtures(spec)
    places = {p["id"]: p for p in spec.get("places", [])}
    now = [e["e"] for e in reading.get("events", [])]
    scene = scene_places(spec, before, now)
    out = []

    # 4. excluded words, straight from the prose (lemmas when the annotation lines up with the tokens)
    lv = leaves(doc) if doc else []
    lemmas = [(x.get("l") or x["w"]).lower() for x in lv] if len(lv) == len(toks) else [t.lower() for t in toks]
    words = [t.lower() for t in toks]
    for pid in sorted(scene):
        for ex in places.get(pid, {}).get("excludes", []):
            n = ex.lower().split()
            for i in range(len(toks) - len(n) + 1):
                if lemmas[i:i + len(n)] == n or words[i:i + len(n)] == n:
                    out.append(f"the prose says '{' '.join(toks[i:i + len(n)])}' (token {i}), but the {pid} is a "
                               f"{places[pid].get('kind', pid)} and has none: cut it or change the setting in story.json")

    # 1-2. what the reading names
    named = set()
    for th in reading.get("things", []):
        ids = th["t"] if isinstance(th["t"], list) else [th["t"]]
        i = th.get("at")
        if isinstance(i, int):
            named.add(i)
            if not (0 <= i < len(toks)) or toks[i] != th.get("w"):
                out.append(f"stale reading: thing {th['t']} points at token {i} "
                           f"'{toks[i] if 0 <= i < len(toks) else '?'}', not '{th.get('w')}'")
        for t in ids:
            k = known.get(t)
            if k is None:
                out.append(f"the prose names '{th.get('w')}' (token {i}) as '{t}', which the world does not have: "
                           f"declare it (a fixture of a place, or scenery) in story.json, or cut it")
            elif k["kind"] == "fixture" and k["place"] not in scene and th.get("phase") not in ("flashback", "recalled"):
                out.append(f"'{th.get('w')}' (token {i}) is {k['what']}, in the {k['place']}, but nobody is in the "
                           f"{k['place']} in this paragraph")

    # 3. nouns that belong to a declared thing but are missing from the reading
    if len(lv) == len(toks):
        vocab = {w.lower() for k in known.values() if k["kind"] != "place" for w in k["words"]}
        for i, x in enumerate(lv):
            if x.get("p") == "NOUN" and i not in named and ({x["w"].lower(), (x.get("l") or "").lower()} & vocab):
                out.append(f"the reading does not list '{x['w']}' (token {i}) among its things: add it "
                           f"(\"things\": [{{\"t\": \"<id>\", \"at\": {i}, \"w\": \"{x['w']}\"}}])")

    # 5. staging against the layout
    facts = closure(spec.get("layout", []))
    for sg in reading.get("staging", []):
        parts, i = sg["s"].split(), sg.get("at")
        if isinstance(i, int) and (not (0 <= i < len(toks)) or toks[i] != sg.get("w")):
            out.append(f"stale reading: staging '{sg['s']}' points at token {i}, not '{sg.get('w')}'")
        if len(parts) != 3 or parts[0] not in RELATIONS:
            out.append(f"staging '{sg['s']}': write it as RELATION A B ({RELATION_TEXT.splitlines()[0]})")
            continue
        r, a, b = parts
        bad = [x for x in (a, b) if x not in known]
        if bad:
            out.append(f"staging '{sg['s']}': {', '.join(bad)} not declared in story.json")
        elif (r, a, b) not in facts:
            says = sorted({f"{x} {y} {z}" for (x, y, z) in facts if {y, z} & {a, b} and y != z})
            out.append(f"the prose stages '{sg['s']}' (token {i}), which the layout does not have"
                       + (f"; the layout says: {'; '.join(says)}" if says else "")
                       + ": change the prose, or the layout in story.json")
    return out


def check(d: Path, k: int, toks: list[str], before: list[str]) -> list[str]:
    spec = json.loads((d / "story.json").read_text())
    if not any(p.get("kind") or p.get("fixtures") for p in spec.get("places", [])):
        return []  # a story without a declared setting is not checked for one
    ev = d / "paragraphs" / f"{k:02}.events.json"
    doc = d / "paragraphs" / f"{k:02}.json"
    if not ev.exists():
        return []
    reading = json.loads(ev.read_text())
    try:
        ann = json.loads(doc.read_text()) if doc.exists() else None
    except json.JSONDecodeError:
        ann = None
    return layout_problems(spec) + problems(spec, toks, ann, reading, before)
