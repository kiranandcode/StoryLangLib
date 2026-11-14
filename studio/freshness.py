"""Is a paragraph's reading (NN.events.json) still a reading of its prose?

The annotation (NN.json) is tied to the prose by `langlib check`: its leaves
must be the prose's tokens, so a prose edit makes it fail. The reading has no
such tie, so it carries one: `text_sha`, the hash of the NN.txt it was read
from (`workflows.py extract` prints it), and per event optionally `w`, the
token its `at` index points at. After a prose edit either differs, and the
reading is stale until it is re-derived. Deterministic; no model calls.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path


def text_sha(text: str) -> str:
    return hashlib.sha256(text.strip().encode()).hexdigest()[:16]


def reading(pdir: Path, nm: str, tokens: list[str] | None = None) -> dict:
    """{"status": none | unstamped | fresh | stale, "why": [...], "sha": current hash}."""
    txt, ev = pdir / f"{nm}.txt", pdir / f"{nm}.events.json"
    sha = text_sha(txt.read_text()) if txt.exists() else ""
    if not ev.exists():
        return {"status": "none", "why": [], "sha": sha}
    try:
        data = json.loads(ev.read_text())
    except json.JSONDecodeError as e:
        return {"status": "stale", "why": [f"{ev.name} is not JSON: {e}"], "sha": sha}
    why = []
    stamped = data.get("text_sha")
    if stamped and stamped != sha:
        why.append(f"the prose changed after this reading was written (text_sha {stamped}, prose now {sha}): "
                   "re-derive the events and claims")
    if tokens is not None:
        for e in data.get("events", []):
            at = e.get("at")
            if isinstance(at, int) and not 0 <= at < len(tokens):
                why.append(f"'{e.get('e')}' is anchored to token {at}, past the end of the prose ({len(tokens)} tokens)")
            elif isinstance(at, int) and e.get("w") and tokens[at] != e["w"]:
                why.append(f"'{e.get('e')}' is anchored to token {at} \"{e['w']}\", but the prose now has \"{tokens[at]}\" there")
    status = "stale" if why else "fresh" if stamped else "unstamped"
    return {"status": status, "why": why, "sha": sha}
