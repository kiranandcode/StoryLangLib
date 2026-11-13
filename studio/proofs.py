"""A story's Lean proofs: generate `Proofs.lean` with `langlib story-lean`,
check it with `lake env lean`, and record each theorem's fate in proofs.json.
Shared by the server (async) and the workflows CLI (blocking)."""
from __future__ import annotations

import json
import re
import time
from pathlib import Path

import procs
from procs import ROOT

STORIES = ROOT / "stories"
GEN_TIMEOUT = 120
LEAN_TIMEOUT = 600


def namespace(name: str) -> str:
    return "Stories." + "".join(w.capitalize() for w in re.split(r"[^A-Za-z0-9]+", name) if w)


def gen_argv(d: Path) -> list[str]:
    return procs.langlib_argv("story-lean", str(d), namespace(d.name))


def lean_argv(lean_file: Path) -> list[str]:
    return ["lake", "env", "lean", str(lean_file.relative_to(ROOT))]


def write_lean(d: Path, src: str) -> tuple[Path, dict]:
    lean_file = d / "Proofs.lean"
    if not lean_file.exists() or lean_file.read_text() != src:
        lean_file.write_text(src)
    thms = {}
    for i, line in enumerate(src.splitlines(), 1):
        m = re.match(r"theorem (\S+)", line)
        if m:
            thms[m.group(1)] = {"line": i, "statement": line.removeprefix("theorem ").split(" := by")[0]}
    return lean_file, thms


def verdict(d: Path, lean_file: Path, thms: dict, res: procs.Result, t0: float) -> dict:
    text = res.stdout + res.stderr
    errors: list[tuple[int, str]] = []
    for m in re.finditer(r"^[^\n]*Proofs\.lean:(\d+):\d+: error: (.*?)(?=^\S[^\n]*\.lean:\d+:\d+:|\Z)", text, re.M | re.S):
        errors.append((int(m.group(1)), m.group(2).strip()[:500]))
    starts = sorted(v["line"] for v in thms.values())
    for v in thms.values():
        v["ok"] = not res.timed_out
    for line, msg in errors:
        owner = max((k for k, v in thms.items() if v["line"] <= line), key=lambda k: thms[k]["line"], default=None)
        if owner:
            nxt = [l for l in starts if l > thms[owner]["line"]]
            if not nxt or line < nxt[0]:
                thms[owner]["ok"] = False
                thms[owner]["error"] = msg
    guards = [msg for line, msg in errors if "guard" in msg.lower() or not any(v["line"] <= line for v in thms.values())]
    status = "timeout" if res.timed_out else "ok" if res.returncode == 0 else "failed"
    out = {"status": status, "secs": round(time.time() - t0, 1), "theorems": thms,
           "errors": [m for _, m in errors][:20], "guards": guards[:10],
           "file": str(lean_file.relative_to(ROOT)), "at": time.time()}
    if res.timed_out:
        out["errors"].insert(0, f"lean timed out after {LEAN_TIMEOUT}s")
    (d / "proofs.json").write_text(json.dumps(out, indent=1))
    return out


def gen_error(res: procs.Result) -> dict:
    return {"status": "error", "error": (res.stderr or res.stdout)[-2000:], "theorems": {}, "at": time.time()}


def prove(d: Path) -> dict:
    """Blocking: generate and check the story's proofs."""
    t0 = time.time()
    g = procs.run(gen_argv(d), timeout=GEN_TIMEOUT)
    if g.returncode != 0:
        out = gen_error(g)
        (d / "proofs.json").write_text(json.dumps(out, indent=1))
        return out
    lean_file, thms = write_lean(d, g.stdout)
    return verdict(d, lean_file, thms, procs.run(lean_argv(lean_file), timeout=LEAN_TIMEOUT), t0)


async def aprove(d: Path) -> dict:
    """Async: as `prove`; cancelling it kills whichever child is running."""
    t0 = time.time()
    g = await procs.arun(gen_argv(d), timeout=GEN_TIMEOUT)
    if g.returncode != 0:
        out = gen_error(g)
        (d / "proofs.json").write_text(json.dumps(out, indent=1))
        return out
    lean_file, thms = write_lean(d, g.stdout)
    return verdict(d, lean_file, thms, await procs.arun(lean_argv(lean_file), timeout=LEAN_TIMEOUT), t0)
