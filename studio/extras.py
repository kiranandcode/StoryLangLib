"""The readings beside `langlib story`: ties, care and identity (`langlib ext`),
the refined consent reading (`langlib consent`), the style verdicts
(`langlib style`, `house`, `academic`) and a paper's argument graph
(`langlib argument`). Each runs through procs.arun (its lock, nice, timeout,
process-group reaping) and is cached until the story's files change.

Requests for the same reading share one run. The run is a task in the
server's `background` set, so shutdown cancels it, and cancelling it kills the
langlib process group; a client that goes away only stops waiting (shield).
"""
from __future__ import annotations

import ast
import asyncio
import json
from pathlib import Path
from typing import Callable

import procs
from procs import ROOT

STORIES = ROOT / "stories"
PAPERS = STORIES / "private-papers"

_cache: dict[tuple[str, str], dict] = {}
_running: dict[tuple[str, str], asyncio.Task] = {}


def papers() -> list[str]:
    """Private papers, and public essays (stories/essay-*: a story directory that is also read as a paper)."""
    priv = sorted(p.name for p in PAPERS.iterdir() if (p / "argument.py").exists()) if PAPERS.exists() else []
    return priv + sorted(p.name for p in STORIES.glob("essay-*") if (p / "argument.py").exists())


def paper_dir(name: str) -> Path:
    return PAPERS / name if (PAPERS / name).is_dir() else STORIES / name


def _literals(path: Path, names: tuple[str, ...]) -> dict:
    """Top-level literal assignments of a paper's argument.py, read without running it."""
    out = {}
    for node in ast.parse(path.read_text()).body:
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            if node.targets[0].id in names:
                try:
                    out[node.targets[0].id] = ast.literal_eval(node.value)
                except ValueError:
                    pass
    return out


async def _cli(*args: str, timeout: float = 180) -> dict:
    res = await procs.arun(procs.langlib_argv(*args), timeout=timeout)
    try:
        r = json.loads(res.stdout)
        if not isinstance(r, dict):
            r = {"value": r}
    except json.JSONDecodeError:
        r = {"error": (res.stderr or res.stdout or ("timed out" if res.timed_out else "no output"))[-2000:]}
    r["secs"] = res.secs
    return r


async def _story_readings(name: str) -> dict:
    d = str(STORIES / name)
    spec = json.loads((STORIES / name / "story.json").read_text())
    out: dict = {"name": name}
    out["ext"] = await _cli("ext", d) if "ext" in spec else None
    has_consent = any('"consent"' in f.read_text() for f in (STORIES / name / "paragraphs").glob("*.events.json"))
    out["consent"] = await _cli("consent", d) if has_consent else None
    out["style"] = await _cli("style", d)
    out["house"] = await _cli("house", d)
    return out


async def _paper(name: str) -> dict:
    d = paper_dir(name)
    lit = _literals(d / "argument.py", ("LORE", "EXCERPT", "LORE_RULES"))
    lore = json.dumps({"lore": lit.get("LORE", []), "excerpt": lit.get("EXCERPT", []),
                       "rules": [[list(b), h] for b, h in lit.get("LORE_RULES", [])]})
    spec = json.loads((d / "story.json").read_text())
    paras = [{"name": f.stem, "text": f.read_text()} for f in sorted((d / "paragraphs").glob("*.txt"))]
    verdict = d / "argument-verdict.json"
    return {"name": name, "title": spec.get("title", name), "paragraphs": paras,
            "argument": await _cli("argument", str(d), lore),
            "academic": await _cli("academic", str(d)),
            "proved": json.loads(verdict.read_text()) if verdict.exists() else None}


async def get(kind: str, name: str, spawn: Callable) -> dict:
    """The cached reading, or one shared run of it."""
    key = (kind, name)
    if key in _cache:
        return _cache[key]
    t = _running.get(key)
    if t is None or t.done():
        coro = _story_readings(name) if kind == "story" else _paper(name)

        async def go():
            try:
                r = await coro
                _cache[key] = r
                return r
            finally:
                if _running.get(key) is asyncio.current_task():
                    del _running[key]
        t = spawn(go())
        _running[key] = t
    return await asyncio.shield(t)


def invalidate(kind: str, name: str) -> None:
    _cache.pop((kind, name), None)
    t = _running.pop((kind, name), None)
    if t and not t.done():
        t.cancel()   # kills its langlib group; the next request starts afresh
