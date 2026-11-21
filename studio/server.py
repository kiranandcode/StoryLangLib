"""StoryLangLib Studio backend.

Serves each story's checked report (`langlib story <dir>`), regenerates and
checks its Lean proofs (`langlib story-lean`, then `lake env lean`) in the
background, and pushes a server-sent event whenever a story's files change, so
the UI follows whatever the agent writes.

    uvicorn server:app --reload --port 8765      (studio/run.sh does this)
"""
from __future__ import annotations

import asyncio
import atexit
import json
import os
import time
from pathlib import Path

from fastapi import Body, FastAPI, HTTPException
from fastapi.responses import FileResponse, PlainTextResponse, StreamingResponse
from fastapi.staticfiles import StaticFiles
from watchfiles import awatch

import extras
import freshness
import procs
import request_log
import rules_docs
import rules_story
import spec_edit
import proofs as lean
from procs import LANGLIB, ROOT

STORIES = ROOT / "stories"
DIST = Path(__file__).resolve().parent / "web/dist"
PROOF_DEBOUNCE = 1.0

app = FastAPI(title="StoryLangLib Studio")

reports: dict[str, dict] = {}
proofs: dict[str, dict] = {}
proof_tasks: dict[str, asyncio.Task] = {}
report_tasks: dict[str, asyncio.Task] = {}
background: set[asyncio.Task] = set()
clients: set[asyncio.Queue] = set()
atexit.register(procs.kill_all)


def story_dirs() -> list[str]:
    if not STORIES.exists():
        return []
    return sorted(p.name for p in STORIES.iterdir() if (p / "story.json").exists())


async def run_report(name: str) -> dict:
    res = await procs.arun(procs.langlib_argv("story", str(STORIES / name)), timeout=120)
    try:
        r = json.loads(res.stdout)
    except json.JSONDecodeError:
        r = {"error": (res.stderr or res.stdout)[-2000:]}
    r["secs"] = res.secs
    r["name"] = name
    pdir = STORIES / name / "paragraphs"
    for p in r.get("paragraphs", []):
        p["freshness"] = freshness.reading(pdir, p["name"])  # hash only; anchors are checked by the CLI
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
    """Regenerate the story's Lean file and check it; record each theorem's fate.
    Cancelling this task kills the running story-lean or lean process group."""
    proofs[name] = {**proofs.get(name, {}), "status": "running", "started": time.time()}
    await broadcast({"type": "proofs", "story": name, "proofs": proofs[name]})
    try:
        proofs[name] = await lean.aprove(STORIES / name)
    except asyncio.CancelledError:
        proofs[name] = {**proofs.get(name, {}), "status": "superseded"}
        raise
    await broadcast({"type": "proofs", "story": name, "proofs": proofs[name]})


def schedule_proofs(name: str) -> None:
    """Debounced: a newer change cancels (and kills) the story's previous run."""
    t = proof_tasks.get(name)
    if t and not t.done():
        t.cancel()

    async def later():
        await asyncio.sleep(PROOF_DEBOUNCE)
        await check_proofs(name)
    proof_tasks[name] = asyncio.create_task(later())


async def refresh(name: str, prove: bool = True) -> None:
    reports[name] = await run_report(name)
    await broadcast({"type": "story", "story": name, "at": time.time()})
    if prove and os.environ.get("STUDIO_PROOFS", "1") == "1":
        schedule_proofs(name)


def schedule_refresh(name: str, prove: bool = True) -> None:
    t = report_tasks.get(name)
    if t and not t.done():
        t.cancel()

    async def go():
        try:
            await refresh(name, prove)
        except asyncio.CancelledError:
            raise
        except Exception as e:  # a broken story must not stop the server
            reports[name] = {"error": str(e), "name": name}
    report_tasks[name] = asyncio.create_task(go())


async def watch() -> None:
    STORIES.mkdir(exist_ok=True)
    request_log.LOG.touch(exist_ok=True)
    async for changes in awatch(STORIES, LANGLIB, request_log.LOG, debounce=300):
        touched = set()
        for _, path in changes:
            p = Path(path)
            if p == request_log.LOG:
                await broadcast({"type": "requests", "at": time.time()})
                continue
            if p == LANGLIB:
                touched |= set(story_dirs())
                for name in extras.papers():
                    extras.invalidate("paper", name)
                    await broadcast({"type": "paper", "paper": name, "at": time.time()})
                continue
            try:
                rel = p.relative_to(STORIES)
            except ValueError:
                continue
            if rel.parts[:1] == ("private-papers",) and len(rel.parts) > 2:
                if not rel.parts[2].startswith(".") and rel.parts[1] in extras.papers():
                    extras.invalidate("paper", rel.parts[1])
                    await broadcast({"type": "paper", "paper": rel.parts[1], "at": time.time()})
                continue
            if p.name in ("Proofs.lean", "proofs.json") or p.name.startswith(".") or "runs" in rel.parts[1:2]:
                continue
            if rel.parts:
                touched.add(rel.parts[0])
        for name in touched:
            if name in extras.papers():   # an essay is a story and a paper
                extras.invalidate("paper", name)
                await broadcast({"type": "paper", "paper": name, "at": time.time()})
            if (STORIES / name / "story.json").exists():
                extras.invalidate("story", name)
                extras.invalidate("power", name)
                schedule_refresh(name)


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


def spawn(coro) -> asyncio.Task:
    t = asyncio.create_task(coro)
    background.add(t)
    t.add_done_callback(background.discard)
    return t


@app.on_event("startup")
async def startup() -> None:
    procs.reap_stale()  # groups a killed predecessor left behind
    # serve at once; reports fill in (and are pushed) as they are computed
    spawn(warm())
    spawn(watch())


@app.on_event("shutdown")
async def shutdown() -> None:
    tasks = [t for t in [*background, *proof_tasks.values(), *report_tasks.values()] if not t.done()]
    for t in tasks:
        t.cancel()
    await asyncio.gather(*tasks, return_exceptions=True)
    procs.kill_all()


@app.get("/api/stories")
async def list_stories():
    return [{"name": n, "title": reports.get(n, {}).get("title", n)} for n in story_dirs()]


@app.get("/api/story/{name}")
async def get_story(name: str):
    if name not in story_dirs():
        raise HTTPException(404, f"no story {name}")
    if name not in reports:
        reports[name] = await run_report(name)
    return {**reports[name], "proofs": proofs.get(name, {"status": "none"})}


@app.get("/api/story/{name}/readings")
async def readings(name: str):
    """ext, consent, style and house for the story (langlib, under its lock)."""
    if name not in story_dirs():
        raise HTTPException(404, f"no story {name}")
    try:
        return await extras.get("story", name, spawn)
    except Exception as e:  # noqa: BLE001  a broken reading must not break the panel
        return {"name": name, "error": str(e)}


@app.get("/api/story/{name}/power")
async def power(name: str):
    """The story's power system, move by move (`langlib power`; studio/power-schema.md)."""
    if name not in story_dirs():
        raise HTTPException(404, f"no story {name}")
    try:
        return await extras.get("power", name, spawn)
    except Exception as e:  # noqa: BLE001
        return {"name": name, "error": str(e)}


@app.get("/api/papers")
async def list_papers():
    return extras.papers()


@app.get("/api/paper/{name}")
async def get_paper(name: str):
    """A paper's argument graph (`langlib argument`) and academic style."""
    if name not in extras.papers():
        raise HTTPException(404, f"no paper {name}")
    try:
        return await extras.get("paper", name, spawn)
    except Exception as e:  # noqa: BLE001
        return {"name": name, "error": str(e)}


async def rules_doc(doc: str) -> dict:
    if doc.startswith("story:"):
        name = doc[6:]
        if name not in story_dirs():
            raise KeyError(doc)
        if name not in reports:
            reports[name] = await run_report(name)
        spec = json.loads((STORIES / name / "story.json").read_text())
        return rules_story.story_doc(name, reports[name], spec, await extras.get("power", name, spawn))
    return await rules_docs.aget(doc)


@app.get("/api/rules/docs")
async def list_rules_docs():
    """What the Rules view can open: papers, essays, deslop sides, stories, the Death Note arc."""
    return rules_docs.docs(story_dirs())


@app.get("/api/rules")
async def get_rules(doc: str):
    """A document's inferences as rules (`langlib rules`, studio/rules_docs.py, studio/rules_story.py)."""
    try:
        return await rules_doc(doc)
    except KeyError:
        raise HTTPException(404, f"no document {doc}")
    except Exception as e:  # noqa: BLE001  a broken reading must not break the panel
        return {"id": doc, "error": str(e), "paragraphs": []}


@app.get("/api/rules/md")
async def get_rules_md(doc: str):
    """The same, as markdown (tools/house/rules_md.py)."""
    try:
        d = await rules_doc(doc)
    except KeyError:
        raise HTTPException(404, f"no document {doc}")
    if d.get("error"):
        raise HTTPException(500, d["error"])
    return PlainTextResponse(rules_docs.markdown(d), media_type="text/markdown; charset=utf-8")


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


@app.get("/api/requests")
async def list_requests():
    return await asyncio.to_thread(request_log.all_requests)


@app.post("/api/requests")
async def new_request(body: dict = Body(...)):
    try:
        return await asyncio.to_thread(
            request_log.create, body.get("kind", "story"), body.get("text", ""),
            body.get("story", ""), body.get("para", ""), body.get("quote", ""), body.get("target", ""))
    except ValueError as e:
        raise HTTPException(400, str(e))


@app.get("/api/vocab")
async def vocab():
    return spec_edit.vocab()


@app.post("/api/story/{name}/edit")
async def edit_story(name: str, body: dict = Body(...)):
    if name not in story_dirs():
        raise HTTPException(404, f"no story {name}")
    try:
        return await asyncio.to_thread(spec_edit.edit, name, body.get("target", ""), body.get("changes") or {})
    except ValueError as e:
        raise HTTPException(400, str(e))


@app.post("/api/requests/{rid}/withdraw")
async def withdraw(rid: str):
    try:
        return await asyncio.to_thread(request_log.set_status, rid, "declined", "withdrawn by Kiran", "kiran")
    except KeyError as e:
        raise HTTPException(404, str(e))


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
