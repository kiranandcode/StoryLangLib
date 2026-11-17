"""Sync StoryLangLib stories with the folio relay on vibux (docs/folio.md, sections 2-4).

Each round: build the library bundle from stories/ and PUT it if its version changed,
turn new comments from the phone into Studio requests (request_log.py), and post the
status and replies of the requests made from comments back to the relay.

    python3 studio/folio_sync.py [--once] [--interval 30]

Reads story files, never writes them, and prints counts only, never story text.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
import time
import urllib.error
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import request_log as store  # noqa: E402

HERE = Path(__file__).resolve().parent
STORIES = HERE.parent / "stories"
STATE = HERE / "folio-sync.json"
BOOKS = HERE / "folio-books.json"
DEFAULT_BOOKS = ["private-fixpoint"]
RELAY = os.environ.get("FOLIO_RELAY", "http://100.107.43.4:7481")
PARA = re.compile(r"^(\d+)\.txt$")
CHAPTER = re.compile(r"v(\d+)c(\d+)(?::\s*(.*))?$")


def sha(s: str) -> str:
    return hashlib.sha256(s.encode()).hexdigest()


def _json(p: Path) -> dict:
    try:
        return json.loads(p.read_text())
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def iso(ts: float) -> str:
    return datetime.fromtimestamp(ts, timezone.utc).isoformat(timespec="milliseconds").replace("+00:00", "Z")


# --- the library bundle -------------------------------------------------------

def paragraphs(d: Path) -> list[dict]:
    pd = d / "paragraphs" if (d / "paragraphs").is_dir() else d
    files = sorted((p for p in pd.iterdir() if PARA.match(p.name)), key=lambda p: int(PARA.match(p.name)[1]))
    out = []
    for p in files:
        text = p.read_text().strip("\n")
        out.append({"n": PARA.match(p.name)[1], "sha": sha(text), "text": text})
    return out


def chapter(d: Path, title: str, volume: int | None = None, number: int | None = None) -> dict:
    ps = paragraphs(d)
    return {"id": d.name, "title": title, "volume": volume, "number": number,
            "sha": sha("\n\n".join(p["text"] for p in ps)), "paragraphs": ps}


def series_chapter(d: Path, stem: str, i: int) -> dict:
    """A series chapter titled from its meta.json "chapter" ("v1c03: Name")."""
    label = _json(d / "meta.json").get("chapter") or stem
    m = CHAPTER.match(label) or CHAPTER.match(stem)
    if not m:
        return chapter(d, label, None, i)
    vol, num, name = int(m[1]), int(m[2]), (m[3] or "").strip()
    title = f"Volume {vol}, Chapter {num}" + (f": {name}" if name else "")
    return chapter(d, title, vol, num)


def series_dirs(sd: Path) -> list[tuple[str, Path]]:
    """The series' chapter dirs (`<series>-<stem>` for each chapters/<stem>.json), in the
    order their story.json "after" links chain them; unchained ones follow by name."""
    dirs = {stem: sd.parent / f"{sd.name}-{stem}" for stem in sorted(p.stem for p in (sd / "chapters").glob("*.json"))}
    dirs = {s: d for s, d in dirs.items() if d.is_dir()}
    by_name = {d.name: s for s, d in dirs.items()}
    after = {s: Path(_json(d / "story.json").get("after") or "").name for s, d in dirs.items()}
    nxt: dict[str, list[str]] = {}
    for s, a in after.items():
        nxt.setdefault(by_name.get(a, ""), []).append(s)
    order, todo = [], list(nxt.get("", []))
    while todo:
        s = todo.pop(0)
        if s in order:
            continue
        order.append(s)
        todo = nxt.get(s, []) + todo
    order += [s for s in dirs if s not in order]
    return [(s, dirs[s]) for s in order]


def book(d: Path) -> dict:
    title = _json(d / "story.json").get("title") or d.name
    if (d / "chapters").is_dir() and _json(d / "meta.json").get("series"):
        chs = [series_chapter(cd, s, i + 1) for i, (s, cd) in enumerate(series_dirs(d))]
    else:
        chs = [chapter(d, title)]
    return {"id": d.name, "title": title, "chapters": chs}


def book_names(path: Path = BOOKS) -> list[str]:
    return _json(path).get("books") or DEFAULT_BOOKS


def build_library(stories: Path = STORIES, names: list[str] | None = None) -> dict:
    books = [book(stories / n) for n in (names or book_names()) if (stories / n).is_dir()]
    # generated_at stays out of the version, so an unchanged library keeps its version
    version = sha(json.dumps({"books": books}, sort_keys=True, separators=(",", ":"), ensure_ascii=False))
    return {"version": version, "generated_at": iso(time.time()), "books": books}


# --- the relay ----------------------------------------------------------------

class Relay:
    def __init__(self, url: str = RELAY, timeout: float = 60):
        self.url, self.timeout = url.rstrip("/"), timeout

    def call(self, method: str, path: str, body=None):
        data = None if body is None else json.dumps(body, ensure_ascii=False).encode()
        req = urllib.request.Request(self.url + path, data=data, method=method,
                                     headers={"Content-Type": "application/json"})
        with urllib.request.urlopen(req, timeout=self.timeout) as r:
            raw = r.read()
        return json.loads(raw) if raw else {}


# --- state: studio/folio-sync.json --------------------------------------------

def load_state(path: Path = STATE) -> dict:
    s = _json(path)
    return {"version": s.get("version"), "since": s.get("since", 0), "map": s.get("map", {}), "pushed": s.get("pushed", {})}


def save_state(s: dict, path: Path = STATE) -> None:
    tmp = path.with_suffix(".tmp")
    tmp.write_text(json.dumps(s, indent=1, sort_keys=True))
    tmp.replace(path)


# --- one round ----------------------------------------------------------------

def push_library(relay: Relay, s: dict, stories: Path, names: list[str] | None) -> bool:
    lib = build_library(stories, names)
    if lib["version"] == s["version"]:
        return False
    relay.call("PUT", "/v1/library", lib)
    s["version"] = lib["version"]
    return True


def pull_comments(relay: Relay, s: dict, state_path: Path) -> int:
    r = relay.call("GET", f"/v1/comments?since={int(s['since'])}")
    made = 0
    for c in sorted(r.get("comments", []), key=lambda c: c.get("seq", 0)):
        cid = c.get("cid")
        if cid and cid not in s["map"]:
            try:
                req = store.create("story", c.get("text", ""), story=c.get("chapter", ""), para=str(c.get("para", "")),
                                   quote=c.get("quote", ""), target="folio")
            except ValueError:  # an empty comment: nothing to ask the agents
                req = None
            if req:
                s["map"][cid] = req["id"]
                made += 1
        s["since"] = max(s["since"], c.get("seq", 0))
        save_state(s, state_path)  # after each comment, so a crash can't file one twice
    s["since"] = max(s["since"], r.get("seq", 0))
    return made


def push_replies(relay: Relay, s: dict) -> int:
    reqs = {r["id"]: r for r in store.all_requests()}
    out, keys = [], {}
    for cid, rid in s["map"].items():
        r = reqs.get(rid)
        if not r:
            continue
        at = r.get("updated") or r["at"]
        key = f"{r['status']}|{at}"
        if s["pushed"].get(rid) == key:
            continue
        by = r["history"][-1].get("by") if r["history"] else ""
        out.append({"cid": cid, "rid": rid, "status": r["status"], "reply": r.get("reply") or None,
                    "by": by or "", "at": iso(at)})
        keys[rid] = key
    if out:
        relay.call("POST", "/v1/replies", out)
        s["pushed"].update(keys)
    return len(out)


def sync_round(relay: Relay, stories: Path = STORIES, state_path: Path = STATE,
               names: list[str] | None = None) -> dict:
    s = load_state(state_path)
    pushed = push_library(relay, s, stories, names)
    save_state(s, state_path)
    made = pull_comments(relay, s, state_path)
    save_state(s, state_path)
    sent = push_replies(relay, s)
    save_state(s, state_path)
    return {"library": pushed, "comments": made, "replies": sent}


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--once", action="store_true", help="one round, then exit")
    ap.add_argument("--interval", type=float, default=30, help="seconds between rounds")
    a = ap.parse_args()
    relay = Relay()
    while True:
        try:
            r = sync_round(relay)
            if any(r.values()):
                print(f"{time.strftime('%H:%M:%S')} library {'pushed' if r['library'] else 'unchanged'}, "
                      f"{r['comments']} new comment(s), {r['replies']} status update(s)", flush=True)
        except (urllib.error.URLError, OSError) as e:
            print(f"{time.strftime('%H:%M:%S')} relay {relay.url} unreachable: {getattr(e, 'code', '') or type(e).__name__}",
                  file=sys.stderr, flush=True)
            if a.once:
                sys.exit(1)
        if a.once:
            return
        time.sleep(a.interval)


if __name__ == "__main__":
    main()
