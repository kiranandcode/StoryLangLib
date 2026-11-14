"""Direct edits to a story's model (story.json) from the Studio's inspector.

Kiran adjusts a character (traits, values, pronouns, where they start, what
they know), a starting bond, or a fact (label, truth). The edit is applied to
a scratch copy first and accepted only if `langlib story` still reads the
story; then story.json is rewritten and the edit is logged as a request
(kind "edit", status done) so the listening agent sees what changed. Prose
and readings are untouched: a model edit can make paragraphs fail, which is
the point. No model calls.
"""
from __future__ import annotations

import json
import re
import shutil
import tempfile
from pathlib import Path

import procs
import request_log
from procs import ROOT

DIMS = ["trust", "attraction", "affection", "tension"]


def vocab() -> dict:
    src = (ROOT / "LangLib/World/Persona.lean").read_text()

    def ctors(name: str) -> list[str]:
        m = re.search(rf"inductive {name}\b(.*?)(?:\n\s*deriving|\n\n)", src, re.S)
        return re.findall(r"\|\s*(\w+)", m.group(1)) if m else []
    return {"traits": ctors("Trait"), "values": ctors("Value"), "dims": DIMS, "bondMax": 3}


def _apply(spec: dict, target: str, ch: dict, voc: dict) -> list[str]:
    """Mutate spec; return a human summary of what changed."""
    kind, _, key = target.partition(":")
    out: list[str] = []
    if kind == "char":
        c = next((c for c in spec["characters"] if c["id"] == key), None)
        if c is None:
            raise ValueError(f"no character {key}")
        for f in ("name", "pron"):
            if f in ch and ch[f] != c.get(f):
                out.append(f"{key}.{f}: {c.get(f)} → {ch[f]}")
                c[f] = ch[f]
        for f, allowed in (("traits", voc["traits"]), ("values", voc["values"])):
            if f in ch:
                bad = [x for x in ch[f] if x not in allowed]
                if bad:
                    raise ValueError(f"unknown {f}: {', '.join(bad)} (allowed: {', '.join(allowed)})")
                if len(set(ch[f])) != len(ch[f]):
                    raise ValueError(f"repeated {f}")
                if ch[f] != c.get(f):
                    out.append(f"{key}.{f}: {', '.join(c.get(f, [])) or '-'} → {', '.join(ch[f]) or '-'}")
                    c[f] = ch[f]
        start = spec.setdefault("start", {})
        if "start_place" in ch:
            at = start.setdefault("at", {})
            old = at.get(key)
            new = ch["start_place"] or None
            if new and new not in [p["id"] for p in spec["places"]]:
                raise ValueError(f"no place {new}")
            if new != old:
                out.append(f"{key} starts at: {old or 'offstage'} → {new or 'offstage'}")
                if new:
                    at[key] = new
                else:
                    at.pop(key, None)
        if "knows" in ch:
            ids = {a["id"] for a in spec["atoms"]}
            bad = [l for l in ch["knows"] if l.lstrip("!") not in ids]
            if bad:
                raise ValueError(f"unknown facts: {', '.join(bad)}")
            old = start.setdefault("knows", {}).get(key, [])
            if ch["knows"] != old:
                out.append(f"{key} knows at the start: {', '.join(old) or '-'} → {', '.join(ch['knows']) or '-'}")
                start["knows"][key] = ch["knows"]
    elif kind == "bond":
        a, _, b = key.partition(">")
        chars = {c["id"] for c in spec["characters"]}
        if a not in chars or b not in chars or a == b:
            raise ValueError(f"bad bond {key}")
        bonds = spec.setdefault("start", {}).setdefault("bonds", {})
        cur = bonds.setdefault(key, {})
        for d in DIMS:
            if d in ch:
                n = int(ch[d])
                if not 0 <= n <= voc["bondMax"]:
                    raise ValueError(f"{d} must be 0..{voc['bondMax']}")
                if cur.get(d, 0) != n:
                    out.append(f"{key} {d} at the start: {cur.get(d, 0)} → {n}")
                    if n:
                        cur[d] = n
                    else:
                        cur.pop(d, None)
    elif kind == "fact":
        a = next((a for a in spec["atoms"] if a["id"] == key), None)
        if a is None:
            raise ValueError(f"no fact {key}")
        if "label" in ch and ch["label"].strip() and ch["label"] != a["label"]:
            out.append(f"fact {key} label: {a['label']} → {ch['label']}")
            a["label"] = ch["label"].strip()
        if "truth" in ch and bool(ch["truth"]) != a.get("truth"):
            out.append(f"fact {key} is now {'true' if ch['truth'] else 'false'}")
            a["truth"] = bool(ch["truth"])
    else:
        raise ValueError(f"cannot edit {target}")
    return out


def edit(story: str, target: str, changes: dict) -> dict:
    d = ROOT / "stories" / story
    spec_path = d / "story.json"
    spec = json.loads(spec_path.read_text())
    summary = _apply(spec, target, changes, vocab())
    if not summary:
        return {"changed": []}
    with tempfile.TemporaryDirectory(dir=ROOT / ".lake") as tmp:
        t = Path(tmp) / story
        shutil.copytree(d / "paragraphs", t / "paragraphs") if (d / "paragraphs").exists() else t.mkdir()
        (t / "story.json").write_text(json.dumps(spec, indent=2))
        res = procs.run(procs.langlib_argv("story", str(t)), timeout=120)
        try:
            rep = json.loads(res.stdout)
        except json.JSONDecodeError:
            rep = {"error": (res.stderr or res.stdout)[-1000:]}
        if "error" in rep:
            raise ValueError(f"the checker cannot read the story after this edit: {rep['error']}")
    spec_path.write_text(json.dumps(spec, indent=2, ensure_ascii=False) + "\n")
    request_log.create("story", "Edited in the Studio's inspector: " + "; ".join(summary), story, target=target,
                       status="done", reply="applied to story.json directly (not committed); paragraphs re-checked")
    return {"changed": summary}
