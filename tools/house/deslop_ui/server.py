"""Deslop UI: the certification of a text, before and after, laid out for reading.

    python3 tools/house/deslop_ui/server.py [--port 8790]

Documents live in docs/deslop/<name> (the committed demos) and
stories/private-deslop/<name> (anything pasted into the UI; git ignores it),
each with original/ and rewrite/ as certify.py lays them out.

The server never calls a model. Certifying is deterministic and runs here.
Annotating and rewriting are queued as `deslop` requests in the Studio's
request log (studio/request_log.py); an interactive agent claims them with the
studio MCP (`await_request {"kind": "deslop"}`) and replies, following
~/.claude/skills/verified-deslopify. LANGLIB_BIN overrides the langlib binary.
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlparse

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent.parent
sys.path.insert(0, str(ROOT / "tools/house"))
sys.path.insert(0, str(ROOT / "studio"))
import certify  # noqa: E402
import request_log  # noqa: E402

ROOTS = [ROOT / "docs/deslop", ROOT / "stories/private-deslop"]


def rel(p: Path) -> str:
    return str(p.relative_to(ROOT))


def doc_dir(doc_id: str) -> Path:
    d = (ROOT / doc_id).resolve()
    if not any(d.parent == r.resolve() for r in ROOTS) or not d.is_dir():
        raise KeyError(doc_id)
    return d


def title_of(d: Path) -> str:
    for side in ("original", "rewrite"):
        h = d / side / "headings.json"
        if h.exists():
            t = json.loads(h.read_text()).get("title")
            if t:
                return t
    s = d / "source.md"
    if s.exists():
        m = re.match(r"#\s*(.+)", s.read_text())
        if m:
            return m.group(1).strip()
    return d.name


def score(side: Path) -> dict | None:
    r = side / "report.json"
    if not r.exists():
        return None
    rep = json.loads(r.read_text())
    if not rep.get("rules"):
        return {"holds": 0, "of": 0, "certified": False, "annotation": rep.get("annotation", [])}
    return {"holds": sum(x["holds"] for x in rep["rules"]), "of": len(rep["rules"]),
            "certified": rep.get("certified", False)}


def list_docs() -> list[dict]:
    out = []
    for r in ROOTS:
        if not r.exists():
            continue
        for d in sorted(p for p in r.iterdir() if (p / "original/paragraphs").is_dir()):
            out.append({"id": rel(d), "name": d.name, "title": title_of(d),
                        "group": "demos" if r.name == "deslop" else "mine",
                        "before": score(d / "original"), "after": score(d / "rewrite")})
    return out


# ---------------------------------------------------------------- one side

def classes_for(lex: dict, words: list[dict]) -> list[list[str]]:
    """Word classes per leaf: single-word keys by lemma or form, then multiword keys."""
    out = []
    for w in words:
        cs = set()
        for k in {w["w"].lower(), (w.get("l") or w["w"]).lower(), f"{(w.get('l') or w['w']).lower()}/{w['p']}"}:
            e = lex.get(k)
            if isinstance(e, dict):
                cs.update(e.get("cls", []))
                if e.get("rel"):
                    cs.add("rel:" + e["rel"])
        out.append(cs)
    forms = [w["w"].lower() for w in words]
    for k, e in lex.items():
        if " " not in k or not isinstance(e, dict):
            continue
        ks = k.split()
        for i in range(len(forms) - len(ks) + 1):
            if forms[i:i + len(ks)] == ks:
                for j in range(i, i + len(ks)):
                    out[j].update(e.get("cls", []))
                    if e.get("rel"):
                        out[j].add("rel:" + e["rel"])
    return [sorted(c - {"ing", "be", "and", "agent", "that", "wh", "light", "rel:demonstrative", "rel:quote"})
            for c in out]


def refs_in(t: dict) -> set[str]:
    s = {t["ref"]} if t.get("ref") else set()
    for k in t.get("k", []):
        s |= refs_in(k)
    return s


def side_data(side: Path) -> dict | None:
    pdir = side / "paragraphs"
    if not pdir.is_dir():
        return None
    lex = {}
    if (side / "lexicon.json").exists():
        lex = json.loads((side / "lexicon.json").read_text())
    rep = json.loads((side / "report.json").read_text()) if (side / "report.json").exists() else None
    flags: dict[str, list[str]] = {}
    if rep:
        for r in rep.get("rules", []):
            if r["holds"] and r["name"] not in ("characters: few agentless passives", "few noun stacks", "point first",
                                               "no stacked asides", "no non-sequitur stacks", "few exhortations",
                                               "few observation-and-response joins", "actions: few hidden in nouns"):
                continue
            for a in r.get("at", []):
                if a["at"] != "lexicon":
                    flags.setdefault(a["at"], []).append(r["name"] + ("" if not r["holds"] else " (within limits)"))
    headings = json.loads((side / "headings.json").read_text()) if (side / "headings.json").exists() else {}
    notes = json.loads((side / "notes.json").read_text()) if (side / "notes.json").exists() else {}
    paras = []
    for txt in sorted(pdir.glob("[0-9][0-9].txt")):
        n = int(txt.stem)
        src = txt.read_text()
        para = {"n": n, "nn": txt.stem, "text": src.strip(), "heading": headings.get(str(n)),
                "annotated": (pdir / f"{txt.stem}.json").exists() or (pdir / f"{txt.stem}.sx").exists(),
                "sentences": [], "entities": {}}
        jp = pdir / f"{txt.stem}.json"
        if jp.exists():
            try:
                doc = json.loads(jp.read_text())
            except json.JSONDecodeError:
                doc = None
            if doc:
                para["entities"] = {e["id"]: {"name": e.get("name", e["id"]), "kind": e.get("kind")}
                                    for e in doc.get("entities", [])}
                pos = 0
                for i, s in enumerate(doc.get("sentences", []), 1):
                    lv = certify.leaves(s)
                    toks, start = [], None
                    for w in lv:
                        k = src.find(w["w"], pos)
                        if k < 0:
                            break
                        if start is None:
                            start = k
                        toks.append({"w": w["w"], "p": w["p"], "r": w.get("r"), "l": w.get("l"),
                                     "ref": w.get("ref"), "a": k, "b": k + len(w["w"])})
                        pos = k + len(w["w"])
                    cls = classes_for(lex, lv)
                    for t, c in zip(toks, cls):
                        t["cls"] = c
                    para["sentences"].append({
                        "i": i, "at": f"{n}:{i}", "a": start or 0, "b": pos, "tokens": toks, "tree": s,
                        "refs": sorted(refs_in(s)),
                        "words": len([w for w in lv if w["p"] not in ("PUNCT", "SYM")]),
                        "flags": flags.get(f"{n}:{i}", [])})
        para["note"] = notes.get(txt.stem)
        paras.append(para)
    for nn, note in notes.items():
        if note.get("dropped") and not (pdir / f"{nn}.txt").exists():
            paras.append({"n": int(nn), "nn": nn, "dropped": note["dropped"], "note": note, "text": "",
                          "heading": headings.get(str(int(nn))), "sentences": [], "entities": {}})
    paras.sort(key=lambda p: p["n"])
    return {"paragraphs": paras, "report": rep, "title": headings.get("title")}


def doc_data(doc_id: str) -> dict:
    d = doc_dir(doc_id)
    reqs = [r for r in request_log.all_requests() if r.get("kind") == "deslop" and r.get("story") == doc_id]
    return {"id": doc_id, "title": title_of(d),
            "source": (d / "source.md").read_text() if (d / "source.md").exists() else "",
            "original": side_data(d / "original"), "rewrite": side_data(d / "rewrite"),
            "requests": reqs[-40:], "version": version(d)}


def version(d: Path) -> float:
    m = 0.0
    for p in d.rglob("*"):
        if p.is_file() and not p.name.endswith(".json") or p.name in ("report.json", "notes.json", "headings.json"):
            try:
                m = max(m, p.stat().st_mtime)
            except OSError:
                pass
    try:
        m = max(m, request_log.LOG.stat().st_mtime)
    except OSError:
        pass
    return m


# ---------------------------------------------------------------- actions

def new_doc(title: str, text: str) -> str:
    base = ROOT / "stories/private-deslop"
    slug = re.sub(r"[^a-z0-9]+", "-", title.lower()).strip("-")[:40] or "untitled"
    d, k = base / slug, 2
    while d.exists():
        d, k = base / f"{slug}-{k}", k + 1
    pdir = d / "original/paragraphs"
    pdir.mkdir(parents=True)
    headings, n, pending = {"title": title}, 0, None
    for block in re.split(r"\n", text.replace("\r", "")):
        line = block.strip()
        if not line:
            continue
        # a short line with no closing punctuation is a heading for what follows
        if len(line) < 90 and not re.search(r"[.!?:;\"”)]$", line):
            if n == 0 and title == "Untitled":
                headings["title"] = line
            else:
                pending = line if pending is None else f"{pending} / {line}"
            continue
        n += 1
        (pdir / f"{n:02d}.txt").write_text(line + "\n")
        if pending:
            headings[str(n)] = pending
            pending = None
    (d / "original/headings.json").write_text(json.dumps(headings, indent=1))
    (d / "source.md").write_text(f"# {headings['title']}\n\nPasted into the deslop UI on {time.strftime('%Y-%m-%d')}.\n")
    return rel(d)


def run_certify(doc_id: str, side: str) -> dict:
    d = doc_dir(doc_id) / side
    p = subprocess.run(["nice", "-n", "10", sys.executable, str(ROOT / "tools/house/certify.py"), str(d)],
                       capture_output=True, text=True, timeout=600, env=os.environ)
    return {"ok": p.returncode == 0, "out": p.stdout[-4000:], "err": p.stderr[-2000:]}


ACTIONS = {"annotate": "Annotate and certify the original",
           "rewrite": "Rewrite in Kiran's voice until the house rules pass"}


def queue(doc_id: str, action: str, para: str, note: str) -> dict:
    doc_dir(doc_id)
    if action not in ACTIONS:
        raise ValueError(action)
    what = ACTIONS[action] + (f", paragraph {para}" if para else ", whole document")
    return request_log.create("deslop", what + (f". Note: {note}" if note.strip() else "."),
                              story=doc_id, para=para, target=action)


def worker_seen() -> float | None:
    """When an agent last claimed a deslop request (a rough 'is anyone listening')."""
    t = None
    for r in request_log.all_requests():
        if r.get("kind") == "deslop" and r.get("status") != "open":
            t = max(t or 0, r.get("updated", r["at"]))
    return t


# ---------------------------------------------------------------- http

class H(BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def send(self, code: int, body, ctype="application/json"):
        data = body if isinstance(body, bytes) else json.dumps(body).encode()
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(data)

    def do_GET(self):
        u = urlparse(self.path)
        q = {k: v[0] for k, v in parse_qs(u.query).items()}
        try:
            if u.path in ("/", "/index.html"):
                return self.send(200, (HERE / "index.html").read_bytes(), "text/html; charset=utf-8")
            if u.path == "/api/docs":
                return self.send(200, list_docs())
            if u.path == "/api/doc":
                return self.send(200, doc_data(q["id"]))
            if u.path == "/api/version":
                return self.send(200, {"version": version(doc_dir(q["id"]))})
            if u.path == "/api/worker":
                return self.send(200, {"last": worker_seen()})
        except KeyError as e:
            return self.send(404, {"error": f"no document {e}"})
        self.send(404, {"error": "not found"})

    def do_POST(self):
        u = urlparse(self.path)
        n = int(self.headers.get("Content-Length") or 0)
        body = json.loads(self.rfile.read(n) or b"{}")
        try:
            if u.path == "/api/new":
                return self.send(200, {"id": new_doc(body.get("title") or "Untitled", body["text"])})
            if u.path == "/api/certify":
                return self.send(200, run_certify(body["id"], body.get("side", "rewrite")))
            if u.path == "/api/request":
                return self.send(200, queue(body["id"], body["action"], body.get("para", ""), body.get("note", "")))
        except (KeyError, ValueError) as e:
            return self.send(400, {"error": str(e)})
        self.send(404, {"error": "not found"})


def main():
    port = int(sys.argv[sys.argv.index("--port") + 1]) if "--port" in sys.argv else 8790
    (ROOT / "stories/private-deslop").mkdir(parents=True, exist_ok=True)
    srv = ThreadingHTTPServer(("127.0.0.1", port), H)
    print(f"deslop UI: http://localhost:{port}", flush=True)
    srv.serve_forever()


if __name__ == "__main__":
    main()
