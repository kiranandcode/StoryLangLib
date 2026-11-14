#!/usr/bin/env python3
"""StoryLangLib Studio MCP server: Kiran's requests from the Studio window,
for an interactive agent to act on (stdio JSON-RPC, no deps, no model calls).

    await_request  block until Kiran asks for something (progress pings keep
                   the call alive past the client's tool timeout)
    reply          mark a request working / done / declined, with a reply
                   the Studio shows under it
    list_requests  what is open, in hand, done

The listening loop: await_request -> do the work (write, annotate, check,
prove with studio/workflows.py; commit) -> reply -> await_request.

Registered for the repo in .mcp.json. CLI for poking:
    python3 studio/studio_mcp.py list_requests '{}'
"""
import json
import os
import sys
import threading
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import request_log as store  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
WHO = os.environ.get("COVE_SESSION") or f"agent-{os.getpid()}"


class Cancelled(BaseException):
    """The client cancelled the request (notifications/cancelled)."""


_req = threading.local()
_cancelled: set = set()
_out_lock = threading.Lock()


def send(obj):
    with _out_lock:
        sys.stdout.write(json.dumps(obj) + "\n")
        sys.stdout.flush()


def describe(r: dict) -> dict:
    """The request plus where to look, so the agent can start at once."""
    out = {k: r.get(k) for k in ("id", "kind", "story", "para", "quote", "text", "status")}
    out["asked"] = time.strftime("%Y-%m-%d %H:%M", time.localtime(r["at"]))
    if r.get("kind") == "story" and r.get("story"):
        d = ROOT / "stories" / r["story"]
        out["story_dir"] = str(d.relative_to(ROOT))
        if r.get("para"):
            out["paragraph_files"] = [str(p.relative_to(ROOT)) for p in sorted((d / "paragraphs").glob(f"{r['para']}.*"))]
        out["how"] = ("Edit the story files, then annotate/extract and run `python3 studio/workflows.py "
                      "paragraph-check` and `prove` (--log requests); commit; then reply.")
    else:
        out["how"] = "A change to the Studio or langlib: make it, check it, commit; then reply."
    return out


def await_request(args, poll=1.0, progress_every=15.0):
    timeout = float(args.get("timeout_s") or 3600)
    story, kind = args.get("story") or "", args.get("kind") or ""
    t0 = last = time.monotonic()
    ticks = 0
    while True:
        rid = getattr(_req, "id", None)
        if rid is not None and rid in _cancelled:
            raise Cancelled()
        r = store.claim(WHO, story=story, kind=kind)
        if r:
            return describe(r)
        if time.monotonic() - t0 > timeout:
            return {"status": "timeout", "note": f"no request in {int(timeout)}s; call await_request again to keep listening"}
        token = getattr(_req, "progress", None)
        if token is not None and time.monotonic() - last >= progress_every:
            ticks += 1
            last = time.monotonic()
            send({"jsonrpc": "2.0", "method": "notifications/progress",
                  "params": {"progressToken": token, "progress": ticks, "message": "listening for Kiran's requests"}})
        time.sleep(poll)


def reply(args):
    r = store.set_status(args["id"], args.get("status") or "done", args.get("text") or "", WHO)
    return {k: r.get(k) for k in ("id", "status", "reply")}


def list_requests(args):
    st = args.get("status")
    return [describe(r) | {"reply": r.get("reply", "")} for r in store.all_requests() if not st or r["status"] == st]


TOOLS = {
    "await_request": (
        "Block until Kiran submits a request in the Studio (a change to a story or to the tool), claim it and "
        "return it. Keeps the call alive with progress pings; returns {status: timeout} after timeout_s "
        "(default 3600), when you should call it again. While blocked you are idle: Kiran can interrupt you "
        "from the terminal.",
        {"type": "object", "properties": {
            "story": {"type": "string", "description": "only requests about this story"},
            "kind": {"type": "string", "enum": ["story", "tool"]},
            "timeout_s": {"type": "number"}}},
        await_request),
    "reply": (
        "Update a request: status working (you started), done (with what you changed and the commit), or "
        "declined (with why). The Studio shows the reply under Kiran's request.",
        {"type": "object", "required": ["id", "status"], "properties": {
            "id": {"type": "string"},
            "status": {"type": "string", "enum": ["working", "done", "declined", "open"]},
            "text": {"type": "string"}}},
        reply),
    "list_requests": (
        "Kiran's requests and their status (open, claimed, working, done, declined).",
        {"type": "object", "properties": {"status": {"type": "string"}}},
        list_requests),
}
BLOCKING = {"await_request"}


def handle(msg):
    method = msg.get("method")
    if method == "initialize":
        return {"protocolVersion": msg.get("params", {}).get("protocolVersion", "2024-11-05"),
                "capabilities": {"tools": {"listChanged": False}},
                "serverInfo": {"name": "studio", "version": "0.1"}}
    if method == "tools/list":
        return {"tools": [{"name": n, "description": d, "inputSchema": s} for n, (d, s, _) in TOOLS.items()]}
    if method == "tools/call":
        p = msg.get("params", {})
        t = TOOLS.get(p.get("name"))
        if not t:
            return {"content": [{"type": "text", "text": f"unknown tool {p.get('name')}"}], "isError": True}
        try:
            out = t[2](p.get("arguments") or {})
            return {"content": [{"type": "text", "text": json.dumps(out, indent=1)}]}
        except Cancelled:
            raise
        except Exception as e:  # report to the model, don't kill the server
            return {"content": [{"type": "text", "text": f"{type(e).__name__}: {e}"}], "isError": True}
    if method == "ping":
        return {}
    return None


def answer(msg):
    params = msg.get("params") or {}
    _req.id = msg["id"]
    _req.progress = (params.get("_meta") or {}).get("progressToken")
    try:
        res = handle(msg)
        out = ({"jsonrpc": "2.0", "id": msg["id"], "result": res} if res is not None else
               {"jsonrpc": "2.0", "id": msg["id"], "error": {"code": -32601, "message": f"method not found: {msg.get('method')}"}})
    except Cancelled:
        return  # a cancelled request gets no reply
    except Exception as e:
        out = {"jsonrpc": "2.0", "id": msg["id"], "error": {"code": -32000, "message": str(e)}}
    finally:
        _cancelled.discard(msg["id"])
    send(out)


def serve():
    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        msg = json.loads(line)
        if "id" not in msg:
            if msg.get("method") == "notifications/cancelled":
                _cancelled.add((msg.get("params") or {}).get("requestId"))
            continue
        if msg.get("method") == "tools/call" and (msg.get("params") or {}).get("name") in BLOCKING:
            threading.Thread(target=answer, args=(msg,), daemon=True).start()
            continue
        answer(msg)


if __name__ == "__main__":
    if len(sys.argv) > 1:
        a = json.loads(sys.argv[2]) if len(sys.argv) > 2 else {}
        print(json.dumps(TOOLS[sys.argv[1]][2](a), indent=1))
    else:
        serve()
