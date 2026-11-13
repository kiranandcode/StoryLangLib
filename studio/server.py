"""StoryLangLib Studio backend.

Serves each story's checked report (`langlib story <dir>`), regenerates and
checks its Lean proofs (`langlib story-lean`, then `lake env lean`) in the
background, and pushes a server-sent event whenever a story's files change, so
the UI follows whatever the agent writes.

    uvicorn server:app --reload --port 8765      (studio/run.sh does this)
"""
from __future__ import annotations

import asyncio
import json
import os
import re
import subprocess
import time
from pathlib import Path

from fastapi import FastAPI, HTTPException
from fastapi.responses import FileResponse, StreamingResponse
from fastapi.staticfiles import StaticFiles
from watchfiles import awatch

ROOT = Path(__file__).resolve().parent.parent
STORIES = ROOT / "stories"
LANGLIB = ROOT / ".lake/build/bin/langlib"
DIST = Path(__file__).resolve().parent / "web/dist"

app = FastAPI(title="StoryLangLib Studio")

reports: dict[str, dict] = {}
proofs: dict[str, dict] = {}
proof_tasks: dict[str, asyncio.Task] = {}
clients: set[asyncio.Queue] = set()


def story_dirs() -> list[str]:
    if not STORIES.exists():
        return []
    return sorted(p.name for p in STORIES.iterdir() if (p / "story.json").exists())


def namespace(name: str) -> str:
    return "Stories." + "".join(w.capitalize() for w in re.split(r"[^A-Za-z0-9]+", name) if w)


def run_report(name: str) -> dict:
    t0 = time.time()
    p = subprocess.run([str(LANGLIB), "story", str(STORIES / name)],
                       capture_output=True, text=True, timeout=120)
    try:
        r = json.loads(p.stdout)
    except json.JSONDecodeError:
        r = {"error": (p.stderr or p.stdout)[-2000:]}
    r["secs"] = round(time.time() - t0, 2)
    r["name"] = name
    for extra in ["meta.json", "runs/summary.json"]:
        f = STORIES / name / extra
        if f.exists():
            try:
                r[extra.split("/")[-1].removesuffix(".json")] = json.loads(f.read_text())
            except json.JSONDecodeError:
                pass
    story = STORIES / name / "story.json"
    try:
        r["title"] = json.loads(story.read_text()).get("title", name)
    except (json.JSONDecodeError, OSError):
        r["title"] = name
    return r


async def broadcast(msg: dict) -> None:
    for q in list(clients):
        q.put_nowait(msg)


async def check_proofs(name: str) -> None:
    """Regenerate the story's Lean file and check it; record each theorem's fate."""
    d = STORIES / name
    lean_file = d / "Proofs.lean"
    proofs[name] = {**proofs.get(name, {}), "status": "running", "started": time.time()}
    await broadcast({"type": "proofs", "story": name, "proofs": proofs[name]})
    t0 = time.time()
    gen = await asyncio.create_subprocess_exec(
        str(LANGLIB), "story-lean", str(d), namespace(name),
        stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE)
    out, err = await gen.communicate()
    if gen.returncode != 0:
        proofs[name] = {"status": "error", "error": err.decode()[-2000:], "theorems": {}}
        await broadcast({"type": "proofs", "story": name, "proofs": proofs[name]})
        return
    src = out.decode()
    if not lean_file.exists() or lean_file.read_text() != src:
        lean_file.write_text(src)
    lines = src.splitlines()
    thms = {}
    for i, line in enumerate(lines, 1):
        m = re.match(r"theorem (\S+)", line)
        if m:
            thms[m.group(1)] = {"line": i, "statement": line.removeprefix("theorem ").split(" := by")[0]}
    proc = await asyncio.create_subprocess_exec(
        "lake", "env", "lean", str(lean_file.relative_to(ROOT)), cwd=ROOT,
        stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.STDOUT)
    try:
        lout, _ = await proc.communicate()
    except asyncio.CancelledError:
        proc.kill()
        raise
    text = lout.decode()
    errors: list[tuple[int, str]] = []
    for m in re.finditer(r"^[^\n]*Proofs\.lean:(\d+):\d+: error: (.*?)(?=^\S[^\n]*\.lean:\d+:\d+:|\Z)", text, re.M | re.S):
        errors.append((int(m.group(1)), m.group(2).strip()[:500]))
    starts = sorted((v["line"], k) for k, v in thms.items())
    for k, v in thms.items():
        v["ok"] = True
    for line, msg in errors:
        owner = None
        for l, k in starts:
            if l <= line:
                owner = k
        if owner and thms[owner]["line"] <= line:
            # an error inside a theorem's own lines
            nxt = [l for l, _ in starts if l > thms[owner]["line"]]
            if not nxt or line < nxt[0]:
                thms[owner]["ok"] = False
                thms[owner]["error"] = msg
    guards = [msg for line, msg in errors if "guard" in msg.lower() or not any(
        v["line"] <= line for v in thms.values())]
    proofs[name] = {"status": "ok" if proc.returncode == 0 else "failed",
                    "secs": round(time.time() - t0, 1), "theorems": thms,
                    "errors": [m for _, m in errors][:20], "guards": guards[:10],
                    "file": str(lean_file.relative_to(ROOT)), "at": time.time()}
    (d / "proofs.json").write_text(json.dumps(proofs[name], indent=1))
    await broadcast({"type": "proofs", "story": name, "proofs": proofs[name]})


def schedule_proofs(name: str) -> None:
    t = proof_tasks.get(name)
    if t and not t.done():
        t.cancel()

    async def later():
        await asyncio.sleep(1.5)
        await check_proofs(name)
    proof_tasks[name] = asyncio.create_task(later())


async def refresh(name: str, prove: bool = True) -> None:
    reports[name] = await asyncio.to_thread(run_report, name)
    await broadcast({"type": "story", "story": name, "at": time.time()})
    if prove and os.environ.get("STUDIO_PROOFS", "1") == "1":
        schedule_proofs(name)


async def watch() -> None:
    STORIES.mkdir(exist_ok=True)
    async for changes in awatch(STORIES, LANGLIB, debounce=300):
        touched = set()
        for _, path in changes:
            p = Path(path)
            if p == LANGLIB:
                touched |= set(story_dirs())
                continue
            try:
                rel = p.relative_to(STORIES)
            except ValueError:
                continue
            if p.name in ("Proofs.lean", "proofs.json") or "runs" in rel.parts[1:2]:
                continue
            if rel.parts:
                touched.add(rel.parts[0])
        for name in touched:
            if (STORIES / name / "story.json").exists():
                try:
                    await refresh(name)
                except Exception as e:
                    reports[name] = {"error": str(e), "name": name}


async def warm() -> None:
    for name in story_dirs():
        f = STORIES / name / "proofs.json"
        if f.exists():
            try:
                proofs[name] = json.loads(f.read_text())
            except json.JSONDecodeError:
                pass
        try:
            await refresh(name, prove=not f.exists())
        except Exception as e:  # a broken story must not stop the server
            reports[name] = {"error": str(e), "name": name}


@app.on_event("startup")
async def startup() -> None:
    # serve at once; reports fill in (and are pushed) as they are computed
    asyncio.create_task(warm())
    asyncio.create_task(watch())


@app.get("/api/stories")
async def list_stories():
    return [{"name": n, "title": reports.get(n, {}).get("title", n)} for n in story_dirs()]


@app.get("/api/story/{name}")
async def get_story(name: str):
    if name not in story_dirs():
        raise HTTPException(404, f"no story {name}")
    if name not in reports:
        reports[name] = await asyncio.to_thread(run_report, name)
    return {**reports[name], "proofs": proofs.get(name, {"status": "none"})}


@app.post("/api/story/{name}/prove")
async def prove(name: str):
    schedule_proofs(name)
    return {"ok": True}


@app.get("/api/story/{name}/runs")
async def runs(name: str):
    d = STORIES / name / "runs"
    out = []
    if d.exists():
        for f in sorted(d.glob("*.jsonl")):
            out.append({"workflow": f.stem,
                        "steps": [json.loads(l) for l in f.read_text().splitlines() if l.strip()]})
    return out


@app.get("/api/events")
async def events():
    q: asyncio.Queue = asyncio.Queue()
    clients.add(q)

    async def stream():
        try:
            yield "retry: 1000\n\n"
            while True:
                try:
                    msg = await asyncio.wait_for(q.get(), timeout=20)
                    yield f"data: {json.dumps(msg)}\n\n"
                except asyncio.TimeoutError:
                    yield ": ping\n\n"
        finally:
            clients.discard(q)
    return StreamingResponse(stream(), media_type="text/event-stream",
                             headers={"Cache-Control": "no-cache", "X-Accel-Buffering": "no"})


if DIST.exists():
    app.mount("/assets", StaticFiles(directory=DIST / "assets"), name="assets")

    @app.get("/{path:path}")
    async def spa(path: str):
        return FileResponse(DIST / "index.html")
