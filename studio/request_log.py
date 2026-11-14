"""Kiran's requests from the Studio: changes to a story or to the tool.

An append-only log, `studio/requests.jsonl`: one line per event, either a
new request {"op": "new", "id", "kind": "story"|"tool", "story", "para",
"quote", "text", "at"} or a status change {"op": "status", "id", "status",
"reply", "by", "at"}. A request's state is the fold of its lines. The Studio
appends `new`; the agent (via studio_mcp.py) claims requests and replies.
Nothing here calls a model.
"""
from __future__ import annotations

import contextlib
import fcntl
import json
import time
import uuid
from pathlib import Path

LOG = Path(__file__).resolve().parent / "requests.jsonl"
STATUSES = ("open", "claimed", "working", "done", "declined")


@contextlib.contextmanager
def _locked():
    # no touch(): a+ creates the file, and bumping the mtime on every read made
    # the server's watcher push a change for each read, which clients re-read
    with open(LOG, "a+") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        try:
            yield f
        finally:
            fcntl.flock(f, fcntl.LOCK_UN)


def _fold(lines: list[str]) -> dict[str, dict]:
    reqs: dict[str, dict] = {}
    for line in lines:
        try:
            e = json.loads(line)
        except json.JSONDecodeError:
            continue
        if e.get("op") == "new":
            reqs[e["id"]] = {k: v for k, v in e.items() if k != "op"} | {"status": "open", "history": []}
        elif e.get("op") == "status" and e.get("id") in reqs:
            r = reqs[e["id"]]
            r["status"] = e["status"]
            if e.get("reply"):
                r["reply"] = e["reply"]
            if "checks" in e:
                r["checks"] = e["checks"]
            r["history"].append({k: e.get(k) for k in ("status", "reply", "by", "at")})
            r["updated"] = e["at"]
    return reqs


def _read(f) -> dict[str, dict]:
    f.seek(0)
    return _fold(f.read().splitlines())


def _append(f, e: dict) -> None:
    f.seek(0, 2)
    f.write(json.dumps(e) + "\n")
    f.flush()


def all_requests() -> list[dict]:
    with _locked() as f:
        return sorted(_read(f).values(), key=lambda r: r["at"])


def create(kind: str, text: str, story: str = "", para: str = "", quote: str = "",
           target: str = "", status: str = "open", reply: str = "") -> dict:
    if kind not in ("story", "tool"):
        raise ValueError("kind must be story or tool")
    if not text.strip():
        raise ValueError("empty request")
    e = {"op": "new", "id": uuid.uuid4().hex[:8], "kind": kind, "story": story, "para": para,
         "quote": quote[:2000], "text": text.strip()[:8000], "target": target, "at": time.time()}
    lines = [json.dumps(e)]
    if status != "open":  # recorded already settled (an edit Kiran made herself): never claimable
        lines.append(json.dumps({"op": "status", "id": e["id"], "status": status, "reply": reply, "by": "kiran", "at": e["at"]}))
    with _locked() as f:
        for l in lines:
            _append(f, json.loads(l))
    return _fold(lines)[e["id"]]


def get(rid: str) -> dict:
    with _locked() as f:
        reqs = _read(f)
    if rid not in reqs:
        raise KeyError(f"no request {rid}")
    return reqs[rid]


def set_status(rid: str, status: str, reply: str = "", by: str = "", checks: list | None = None) -> dict:
    if status not in STATUSES:
        raise ValueError(f"status must be one of {', '.join(STATUSES)}")
    with _locked() as f:
        reqs = _read(f)
        if rid not in reqs:
            raise KeyError(f"no request {rid}")
        e = {"op": "status", "id": rid, "status": status, "reply": reply, "by": by, "at": time.time()}
        if checks is not None:
            e["checks"] = checks
        _append(f, e)
        return _read(f)[rid]


def claim(by: str, story: str = "", kind: str = "") -> dict | None:
    """Atomically take the oldest open request (matching story/kind if given)."""
    with _locked() as f:
        for r in sorted(_read(f).values(), key=lambda r: r["at"]):
            if r["status"] != "open" or (story and r["story"] != story) or (kind and r["kind"] != kind):
                continue
            _append(f, {"op": "status", "id": r["id"], "status": "claimed", "by": by, "at": time.time()})
            return _read(f)[r["id"]]
    return None
