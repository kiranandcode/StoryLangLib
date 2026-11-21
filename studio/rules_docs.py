"""Documents for the Rules view (studio/web/src/Rules.tsx): an argument's
inferences drawn as natural-deduction rules, beside the text they come from.

A document id names where the reading lives:

    paper:<name>            a private paper or an essay (extras.papers())
    deslop:<dir>            a deslop side, e.g. deslop:stories/private-deslop/basis-pitch/original
    story:<name>            a story (server.py; studio/rules_story.py maps its inferences)
    lean:deathnote          the Death Note arc, read from its Lean source (rules_story.deathnote)

The rules come from `langlib rules <dir>` (LangLib/Studio/RulesView.lean) when
the directory has an argument.json. An `infer` move without a `rule` field is
still an inference: it is added here as a rule of kind `unclassified`, its
premises tagged the way RulesView.lean tags them (from the move that put each
forward), its quotes the sentence the move points at (`s`, counted from 1)
when there is one. Both the Studio (procs.arun) and the deslop UI (procs.run)
build documents here, so the two views read the same data.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

import extras
import procs
import rules_story
from procs import ROOT

STORIES = ROOT / "stories"
DESLOP_ROOTS = [ROOT / "docs/deslop", STORIES / "private-deslop"]
sys.path.insert(0, str(ROOT / "tools/house"))

_cache: dict[str, tuple[float, dict]] = {}


# ------------------------------------------------------------------ which documents

def deslop_sides() -> list[tuple[Path, str]]:
    out = []
    for r in DESLOP_ROOTS:
        if not r.exists():
            continue
        for d in sorted(p for p in r.iterdir() if p.is_dir()):
            for side in ("original", "rewrite"):
                if list((d / side / "paragraphs").glob("[0-9][0-9].argument.json")):
                    out.append((d / side, f"{_title(d)} ({'before' if side == 'original' else 'after'})"))
    return out


def _title(d: Path) -> str:
    for side in ("original", "rewrite"):
        h = d / side / "headings.json"
        if h.exists():
            try:
                t = json.loads(h.read_text()).get("title")
            except json.JSONDecodeError:
                t = None
            if t:
                return t
    return d.name


def docs(stories: list[str]) -> list[dict]:
    """Everything the Rules view can open, grouped for a picker."""
    out = [{"id": f"paper:{p}", "title": p, "group": "papers"} for p in extras.papers()]
    out += [{"id": f"deslop:{side.relative_to(ROOT)}", "title": t, "group": "deslop"} for side, t in deslop_sides()]
    out += [{"id": f"story:{s}", "title": s, "group": "stories"} for s in stories]
    if rules_story.DN_SOURCE.exists():
        out.append({"id": "lean:deathnote", "title": "Death Note: Light against L", "group": "lean"})
    return out


def doc_dir(doc: str) -> Path:
    kind, _, rest = doc.partition(":")
    if kind == "paper" and rest in extras.papers():
        return extras.paper_dir(rest)
    if kind == "deslop":
        d = (ROOT / rest).resolve()
        if d.name in ("original", "rewrite") and any(d.parent.parent == r.resolve() for r in DESLOP_ROOTS) and d.is_dir():
            return d
    raise KeyError(doc)


# ------------------------------------------------------------------ text

SENT = re.compile(r"(?:(?<=[.!?])|(?<=[.!?][”\"’)]))\s+(?=[A-Z(\"“‘])")
ABBREV = re.compile(r"(\b(?:al|e\.g|i\.e|cf|vs|etc|Fig|Sec|resp)\.)$")


def sentences(text: str) -> list[str]:
    """Sentences, as the annotators count them for a move's `s` (not split after "et al.", "e.g.")."""
    out: list[str] = []
    for piece in SENT.split(text.strip()):
        if out and ABBREV.search(out[-1]):
            out[-1] += " " + piece
        elif piece.strip():
            out.append(piece.strip())
    return out


def paragraphs(d: Path) -> tuple[list[dict], dict]:
    """Each paragraph's text with the heading that opens it (headings.json, or a paper's `heading` moves)."""
    heads = {}
    if (d / "headings.json").exists():
        try:
            heads = json.loads((d / "headings.json").read_text())
        except json.JSONDecodeError:
            heads = {}
    out = []
    for f in sorted((d / "paragraphs").glob("[0-9][0-9].txt")):
        h = heads.get(str(int(f.stem))) or heads.get(f.stem)
        aj = f.with_suffix("").with_suffix(".argument.json")
        if not h and not heads and aj.exists():
            try:
                secs = [m["sec"] for m in json.loads(aj.read_text()).get("moves", []) if m.get("move") == "heading"]
            except (json.JSONDecodeError, KeyError):
                secs = []
            if secs:
                h = f"§ {secs[-1]}" if secs[-1] else "Abstract"
        out.append({"name": f.stem, "text": f.read_text().strip(), **({"heading": h} if h else {})})
    return out, heads


def _title_of(d: Path, heads: dict) -> str:
    if heads.get("title"):
        return heads["title"]
    for f in (d / "story.json",):
        if f.exists():
            try:
                return json.loads(f.read_text()).get("title", d.name)
            except json.JSONDecodeError:
                pass
    return d.parent.name if d.name in ("original", "rewrite") else d.name


# ------------------------------------------------------------------ unclassified inferences

def _meta(d: Path) -> dict:
    """argument.json, or a paper's argument.py literals (LORE, LORE_RULES) read without running it."""
    if (d / "argument.json").exists():
        return json.loads((d / "argument.json").read_text())
    if (d / "argument.py").exists():
        lit = extras._literals(d / "argument.py", ("LORE",))
        return {"lore": lit.get("LORE", [])}
    return {}


TAG_OF_MOVE = {"cite": "citation", "example": "example", "hedge": "hedge", "promise": "promise",
               "contribute": "promise", "define": "fact", "evaluate": "fact"}


def unclassified(d: Path, paras: list[dict], have: list[dict]) -> list[dict]:
    """The infer moves that carry no `rule`, as rules of kind `unclassified`."""
    meta = _meta(d)
    lore, terms = set(meta.get("lore", [])), meta.get("terms", {})
    text = {p["name"]: p["text"] for p in paras}
    first: dict[str, tuple[str, str, int | None]] = {}
    out: list[dict] = []
    n = 0

    def quote_at(pn: str, s: int | None) -> str:
        ss = sentences(text.get(pn, ""))
        return ss[min(max(s, 1), len(ss)) - 1] if s and ss else ""

    def gloss(t: str) -> str:
        return (terms.get(t) or {}).get("gloss") or t.replace("_", " ")

    for f in sorted((d / "paragraphs").glob("[0-9][0-9].argument.json")):
        pn = f.name[:2]
        try:
            moves = json.loads(f.read_text()).get("moves", [])
        except json.JSONDecodeError:
            continue
        for m in moves:
            t = m.get("t", "")
            if m.get("move") == "infer" and "rule" not in m:
                n += 1
                prems = []
                for p in m.get("premises", []):
                    mv, ppn, ps = first.get(p, ("", "", None))
                    tag = "fact" if p in lore else TAG_OF_MOVE.get(mv) or ("fact" if (terms.get(p) or {}).get("kind") == "fact" else "authors")
                    q = quote_at(ppn, ps) if ppn else ""
                    prems.append({"t": p, "tag": tag, "quote": q, "gloss": gloss(p), "para": ppn if q else "", "sub": None})
                out.append({"id": f"I{n}", "concl": t, "quote": quote_at(pn, m.get("s")), "gloss": gloss(t), "para": pn,
                            "kind": "unclassified", "scheme": "inference (scheme not read yet)", "side": "text",
                            "premises": prems, "cqs": [], "label": "in", "sceptic": "in", "thin": [], "bare": False,
                            "note": "This infer move has no `rule` field yet: its kind, scheme and critical questions are unread."})
            if t and t not in first:
                first[t] = (m.get("move", ""), pn, m.get("s"))
    # premises concluded by any rule are sub-rules; labels follow the sub-rules
    concl = {r["concl"]: r["id"] for r in have + out}
    for r in out:
        for p in r["premises"]:
            p["sub"] = concl.get(p["t"])
    every = have + out
    for key in ("label", "sceptic"):
        rules_story.propagate(every, key)
    for r in out:
        leaves = [p for p in r["premises"] if not p["sub"]]
        r["bare"] = bool(leaves) and all(p["tag"] in ("authors", "hedge", "promise") for p in leaves) and \
            all(next((x for x in every if x["id"] == p["sub"]), {}).get("bare", True) for p in r["premises"] if p["sub"])
    return out


# ------------------------------------------------------------------ assembling

def _stamp(d: Path) -> float:
    fs = [d / "argument.json", d / "headings.json", *(d / "paragraphs").glob("[0-9][0-9].*")]
    return max((f.stat().st_mtime for f in fs if f.exists()), default=0.0)


def assemble(doc: str, d: Path, out: procs.Result | None) -> dict:
    paras, heads = paragraphs(d)
    if out is None:
        rules = {"root": _meta(d).get("root", ""), "rules": [], "attacks": [], "bare": [], "bareLeaves": [],
                 "thin": [], "ok": True, "errors": []}
    else:
        try:
            rules = json.loads(out.stdout)
        except json.JSONDecodeError:
            return {"id": doc, "title": _title_of(d, heads), "paragraphs": paras,
                    "error": (out.stderr or out.stdout or ("timed out" if out.timed_out else "no output"))[-2000:]}
    extra = unclassified(d, paras, rules["rules"])
    if extra:
        rules["rules"] += extra
        rules["bare"] = rules.get("bare", []) + [r["id"] for r in extra if r["bare"]]
    return {"id": doc, "title": _title_of(d, heads), "kind": doc.split(":")[0], "paragraphs": paras, "rules": rules,
            **({"note": f"{len(extra)} of the inferences have no rule reading yet (kind “unclassified”)."} if extra else {})}


def _argv(d: Path) -> list[str] | None:
    return procs.langlib_argv("rules", str(d)) if (d / "argument.json").exists() else None


async def aget(doc: str) -> dict:
    """A paper, essay, deslop side or Lean document (the Studio: procs.arun)."""
    if doc == "lean:deathnote":
        return rules_story.deathnote()
    d = doc_dir(doc)
    stamp = _stamp(d)
    if doc in _cache and _cache[doc][0] == stamp:
        return _cache[doc][1]
    argv = _argv(d)
    r = assemble(doc, d, await procs.arun(argv, timeout=120) if argv else None)
    if not r.get("error"):
        _cache[doc] = (stamp, r)
    return r


def get(doc: str) -> dict:
    """The same, synchronously (the deslop UI's threaded server: procs.run)."""
    if doc == "lean:deathnote":
        return rules_story.deathnote()
    d = doc_dir(doc)
    stamp = _stamp(d)
    if doc in _cache and _cache[doc][0] == stamp:
        return _cache[doc][1]
    argv = _argv(d)
    r = assemble(doc, d, procs.run(argv, timeout=120) if argv else None)
    if not r.get("error"):
        _cache[doc] = (stamp, r)
    return r


def markdown(doc: dict) -> str:
    """tools/house/rules_md.py's export of a document."""
    import rules_md
    paras = {p["name"]: p["text"] for p in doc.get("paragraphs", [])}
    heads = {"title": doc.get("title", "")}
    for p in doc.get("paragraphs", []):
        if p.get("heading"):
            heads[str(int(p["name"])) if p["name"].isdigit() else p["name"]] = p["heading"]
    return rules_md.to_markdown(doc["rules"], paras, heads)
