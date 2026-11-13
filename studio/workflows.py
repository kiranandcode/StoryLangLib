"""The Studio's three writing workflows, with the Lean checker in the loop.

    python3 studio/workflows.py incremental stories/roof [--paras 1-3]
    python3 studio/workflows.py topdown     stories/roof-topdown
    python3 studio/workflows.py posthoc     stories/roof-posthoc
    python3 studio/workflows.py compare     stories/roof stories/roof-topdown stories/roof-posthoc

All three leave the same artefacts per paragraph under `paragraphs/`: the
prose (NN.txt), its checked langlib annotation (NN.json), the events and
claims read off it (NN.events.json), and, top-down, its plan (NN.plan.json).
`langlib story <dir>` is the judge throughout; the Studio shows the result
live. Every model call and checker verdict is logged to runs/<workflow>.jsonl.

* incremental: write paragraph k from the outline; annotate it (until
  `langlib check` accepts); read its events and claims; check the story so far;
  if the checker objects, send its `why` back to the writer and rewrite.
* topdown: check the beats; plan each paragraph as events and check the plans
  (repairing plans the checker rejects); write each paragraph from its plan;
  re-extract its events and check that the prose realises the plan; prove the
  layers refine each other in Lean.
* posthoc: write the whole story in one call; then per paragraph annotate
  (parts of speech, references), extract the scene events, then the
  higher-level claims (beliefs, relationships, consent), and check that the
  events imply the claims.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "eval"))
from run_eval import call_model as _call, extract_json, feedback, unclosed  # noqa: E402

LANGLIB = ROOT / ".lake/build/bin/langlib"
ANNOTATE = (ROOT / "eval/prompt.md").read_text()
WRITER_SYSTEM = ("You are a literary fiction writer collaborating with the author, who is also the "
                 "main character. You output only the prose asked for, no commentary.")
JSON_SYSTEM = "You are an annotation engine. You output a single JSON document and nothing else."

EVENT_SYNTAX = """\
Events are one line each: a verb, then ids.
  move C P            take C O            drop C O            give C D O
  tell C D L          whisper C D L       lie C D L           (C says L to D; tell = C believes it)
  notice C L EV       realise C L         (C comes to believe L; EV = seen | sensed | assumed | inferred | rumour | told:X)
                                          (realise only for something C can conclude from what they already believe)
  flirt C D           confide C D         argue C D
  askAct C D ACT      agree C D ACT       withdraw C D ACT    act C D ACT
                      (ACT = holdHands | kiss | touch | undress | sex; agree C D ACT: C consents to ACT with D;
                       act C D ACT: C does ACT with D, which needs both to have agreed)
  ask C D F           answer C D L        hint C D L          sarcasm C D L
                      (sarcasm C D L: C says the opposite of L, meaning L)
  promise C D L       request C D L
  adopt C L           (C comes to want L: use when the text shows a decision or desire that explains a later move)
  intend C PLAN       (C sets out on one of the named plans)
A literal L is a fact id, `!id` for its negation, or at(C,P), holds(C,O), objAt(O,P), did(C,D,ACT).
"""

CLAIM_SYNTAX = """\
Claims about the state after the paragraph, one per line:
  thinks C L      knows C L      falseBelief C L      unaware C F      thinksThinks C D L
  true L          at C P         holds C O            consented C D ACT
  goal C L        bond C D DIM OP N   (DIM = trust | attraction | affection | tension; OP = >= <= == > <)
"""


class Run:
    """Logs every step of a workflow to runs/<name>.jsonl."""

    def __init__(self, story: Path, name: str):
        self.story, self.name = story, name
        (story / "runs").mkdir(exist_ok=True)
        self.path = story / "runs" / f"{name}.jsonl"
        self.path.write_text("")
        self.calls = 0
        self.secs = 0.0
        self.cost = 0.0
        self.objections: list[dict] = []
        self.rewrites = 0
        self.annotation_rounds = 0
        self.t0 = time.time()

    def log(self, **kw):
        kw.setdefault("t", round(time.time() - self.t0, 1))
        with self.path.open("a") as f:
            f.write(json.dumps(kw) + "\n")
        print(f"[{self.name}] " + " ".join(f"{k}={v}" for k, v in kw.items() if k not in ("text",))[:300], flush=True)

    def call(self, model: str, prompt: str, system: str, stage: str, para: str = "") -> str:
        t = time.time()
        raw, meta = call_model(model, prompt, system)
        self.calls += 1
        self.secs += time.time() - t
        self.cost += meta.get("cost") or 0
        self.log(para=para, stage=stage, model=model, secs=meta.get("secs"), note=meta.get("error", "")[:200])
        return raw

    def summary(self) -> dict:
        return {"model calls": self.calls, "model secs": round(self.secs), "wall secs": round(time.time() - self.t0),
                "cost usd": round(self.cost, 2), "checker objections": len(self.objections),
                "rewrites": self.rewrites, "annotation rounds": self.annotation_rounds}


def call_model(model: str, prompt: str, system: str) -> tuple[str, dict]:
    t0 = time.time()
    p = subprocess.run(
        ["claude", "-p", "--model", model, "--tools", "", "--setting-sources", "",
         "--strict-mcp-config", "--no-session-persistence", "--output-format", "json",
         "--system-prompt", system],
        input=prompt, capture_output=True, text=True, timeout=1800)
    meta = {"secs": round(time.time() - t0, 1)}
    try:
        out = json.loads(p.stdout)
    except json.JSONDecodeError:
        return "", meta | {"error": (p.stderr or p.stdout)[-500:]}
    meta["cost"] = out.get("total_cost_usd")
    if out.get("is_error"):
        meta["error"] = str(out.get("result", ""))[:500]
    return out.get("result", ""), meta


def langlib(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run([str(LANGLIB), *args], capture_output=True, text=True)


def report(story: Path) -> dict:
    return json.loads(langlib("story", str(story)).stdout)


def tokens(text_path: Path) -> list[str]:
    return langlib("tokenize", str(text_path)).stdout.splitlines()


class Story:
    def __init__(self, d: Path):
        self.d = d
        self.spec = json.loads((d / "story.json").read_text())
        self.meta = json.loads((d / "meta.json").read_text()) if (d / "meta.json").exists() else {}
        self.pdir = d / "paragraphs"
        self.pdir.mkdir(exist_ok=True)

    def world_text(self) -> str:
        s = self.spec
        lines = ["Characters:"]
        for c in s["characters"]:
            lines.append(f"  {c['id']}: {c['name']} ({c['pron']}); traits {', '.join(c['traits'])}; "
                         f"values, most important first: {' > '.join(c['values'])}")
        lines.append("Places: " + ", ".join(p["id"] for p in s["places"]))
        lines.append("Objects: " + ", ".join(o["id"] for o in s["objects"]))
        lines.append("Facts (ids):")
        for a in s["atoms"]:
            lines.append(f"  {a['id']}: {a['label']}")
        if s.get("plans"):
            lines.append("Plans:")
            for p in s["plans"]:
                lines.append(f"  {p['id']} (by {p['agent']}, for {p['goal']}): {'; '.join(p['steps'])}")
        return "\n".join(lines)

    def persona_text(self) -> str:
        s = self.spec
        out = []
        for c in s["characters"]:
            out.append(f"- {c['name']}: {', '.join(c['traits'])}; cares most about {', then '.join(c['values'])}.")
        bonds = s.get("start", {}).get("bonds", {})
        out.append("Starting feelings (0 none, 2 strong): " + "; ".join(
            f"{k.replace('>', ' toward ')}: " + ", ".join(f"{d} {n}" for d, n in v.items()) for k, v in bonds.items()))
        return "\n".join(out)

    def prose_so_far(self, upto: int) -> str:
        out = []
        for i in range(1, upto):
            f = self.pdir / f"{i:02}.txt"
            if f.exists():
                out.append(f.read_text().strip())
        return "\n\n".join(out)

    def events_so_far(self, upto: int) -> list[str]:
        evs = []
        for i in range(1, upto):
            f = self.pdir / f"{i:02}.events.json"
            if f.exists():
                evs += [e["e"] for e in json.loads(f.read_text()).get("events", [])]
            elif (self.pdir / f"{i:02}.plan.json").exists():
                evs += json.loads((self.pdir / f"{i:02}.plan.json").read_text()).get("events", [])
        return evs


CRAFT = """\
Craft: close third person, past tense, in Kiran's point of view (in scenes Kiran is not in, the
point of view of whoever is there). Interiority over choreography: what she notices, wants,
hesitates over. Specific sensory detail over adjectives; vary sentence rhythm; no cliches, no
euphemism stacks, no em-dash flourishes in every sentence. Dialogue in double quotes ("),
attributed. Keep the reader oriented in place and time. Consent is part of the scene, said
out loud, as character, not paperwork. Write ONE paragraph of 80 to 150 words."""


def write_prompt(st: Story, k: int, brief: str, plan: list[str] | None, objection: str = "", prev: str = "") -> str:
    p = [f"We are writing a short story, '{st.spec.get('title', '')}', one paragraph at a time.",
         "Kiran is the author herself (a self-insert); write her as Kiran.",
         "\n## The people\n" + st.persona_text(),
         f"\n## Explicitness\n{st.meta.get('explicitness', 'sensual but not graphic')}",
         "\n## " + CRAFT]
    so_far = st.prose_so_far(k)
    p.append("\n## The story so far\n" + (so_far or "(this is the first paragraph)"))
    p.append(f"\n## Paragraph {k}: what happens\n{brief}")
    if plan:
        p.append("\nThe paragraph must assert exactly these events, in this order, and nothing else of "
                 "consequence (no other moves, decisions, statements of fact between characters):\n" +
                 "\n".join(f"- {e}" for e in plan) + "\n\n" + st.world_text())
    if objection:
        p.append(f"\n## Your previous draft\n{prev}\n\n## The story checker objects\n{objection}\n\n"
                 "Rewrite the paragraph so the objection no longer applies: either do not assert the "
                 "move, or show on the page what justifies it (the checker's 'first establish' list says what would).")
    p.append("\nOutput only the paragraph.")
    return "\n".join(p)


def annotate(run: Run, st: Story, k: int, model: str, rounds: int = 3) -> bool:
    nm = f"{k:02}"
    text_path = st.pdir / f"{nm}.txt"
    doc_path = st.pdir / f"{nm}.json"
    text = text_path.read_text()
    toks = tokens(text_path)
    base = ANNOTATE + f"\n## Passage\n\n{text}\n\n## Tokens (the leaves must be exactly these, in order)\n\n" + \
        " ".join(f"{i}:{t}" for i, t in enumerate(toks)) + \
        "\n\nUse these entity ids for the story's people and places where they are mentioned: " + \
        ", ".join(c["id"] for c in st.spec["characters"]) + ", " + ", ".join(p["id"] for p in st.spec["places"]) + \
        ", " + ", ".join(o["id"] for o in st.spec["objects"]) + "."
    prompt = base
    for r in range(1, rounds + 1):
        run.annotation_rounds += 1
        doc = extract_json(run.call(model, prompt, JSON_SYSTEM, f"annotate r{r}", nm))
        tmp = st.pdir / f".{nm}.r{r}.json"
        tmp.write_text(doc)
        p = langlib("check", str(text_path), str(tmp))
        try:
            rep = json.loads(p.stdout)
        except json.JSONDecodeError:
            rep = {"ok": False, "parseError": p.stdout or p.stderr}
        run.log(para=nm, stage=f"check r{r}", ok=rep.get("ok", False),
                note="; ".join((rep.get("edits") or [])[:2] + (rep.get("refIssues") or [])[:2]) or rep.get("parseError", ""))
        if rep.get("ok"):
            doc_path.write_text(json.dumps(json.loads(doc), indent=None))
            tmp.unlink()
            return True
        tmp.unlink()
        prompt = base + "\n## Your previous answer\n\n" + doc + "\n\n## Checker report\n\n" + \
            feedback(rep, doc) + "\n\nOutput the corrected JSON document in full."
    return False


def extract(run: Run, st: Story, k: int, model: str, claims: bool = True,
            review: tuple[str, list[str]] | None = None) -> dict:
    """Read the events (and claims) a paragraph asserts, anchored to its tokens."""
    nm = f"{k:02}"
    text_path = st.pdir / f"{nm}.txt"
    toks = tokens(text_path)
    prompt = "\n".join([
        "Read one paragraph of a story and list the events it asserts, in the story world's event language.",
        "\n## The world\n" + st.world_text(),
        "\n## Event language\n" + EVENT_SYNTAX,
        "\n## Events of the earlier paragraphs (for context; do not repeat them)\n" +
        ("\n".join(st.events_so_far(k)) or "(none)"),
        "\n## Earlier prose\n" + (st.prose_so_far(k) or "(none)"),
        f"\n## Paragraph {k}\n{text_path.read_text()}",
        "\n## Its tokens\n" + " ".join(f"{i}:{t}" for i, t in enumerate(toks)),
        """
## Rules
- List what the paragraph says happens, as told, one event per clause that asserts one; not wishes,
  hypotheticals or things merely remembered.
- Use ids, never names. Use only the verbs and ids above.
- "at": the index of the token (verb or key word) that asserts the event.
- "phase": "main", or "meanwhile" when the text cuts to something happening at the same time, or
  "flashback" (with "gap": minutes) for something that happened earlier.
- Motives: every move, take, drop, give and act needs a reason among the events (an earlier
  `adopt`/`intend`, or one in this paragraph). When the prose gives or implies one ("came back for a
  cable", "saw your window lit", "went to make tea", "wanted to see"), encode it as `adopt C L` just
  before the action, where L is what the action brings about (`at(C,P)` for a move, `holds(C,O)` for a
  take, `did(C,D,ACT)` for an act), or `intend C PLAN` when it starts one of the named plans. If the
  prose gives no reason at all, do not invent one.
- Speech: `tell` for sincere statements of a fact in the list; `sarcasm` when someone says the opposite
  of what they mean; `hint` for implication; `ask`/`answer` for a question about a fact; `askAct`,
  `agree` for asking for and giving consent to an intimate act.
- A character jumping to a conclusion: `notice C L inferred` (`assumed` only for a guess they do not
  really believe).
- `tell`, `hint`, `answer` only for statements of the listed fact ids (or where someone is, when a
  character says so); small talk and feelings without a fact id are not events.
- Claims only about the listed fact ids, consent and bonds; do not claim nested beliefs unless the
  paragraph is explicitly about what one character thinks another believes.""",
        ("\n## Claims\n" + CLAIM_SYNTAX + "\nAlso list what the paragraph implies about minds and "
         "relationships right after it (who now believes what, false beliefs, consent given), 1-4 claims.") if claims else "",
        ("\n## Your previous reading\n" + review[0] + "\n\n## The story checker rejects it\n" +
         "\n".join(f"- {o}" for o in review[1]) +
         "\nRe-read the paragraph. Where your reading over-read the prose (an event or claim it does not "
         "assert) or missed a reason it does give (a motive), correct the reading. Where the prose really "
         "does assert it, keep it: the objection then stands against the prose.") if review else "",
        "\nOutput JSON only: {\"events\": [{\"e\": \"...\", \"at\": 12, \"phase\": \"main\"}], \"claims\": [\"...\"]}",
    ])
    raw = run.call(model, prompt, JSON_SYSTEM, "re-read" if review else "extract", nm)
    try:
        out = json.loads(extract_json(raw))
    except json.JSONDecodeError:
        out = {"events": [], "claims": []}
    out.setdefault("claims", [])
    for e in out.get("events", []):
        e["src"] = "text"
    (st.pdir / f"{nm}.events.json").write_text(json.dumps(out, indent=1))
    return out


def reread(run: Run, st: Story, k: int, model: str, obj: list[str], claims: bool = True) -> list[str]:
    """Before blaming the prose, let the extractor look again at what the checker rejected."""
    nm = f"{k:02}"
    cur = (st.pdir / f"{nm}.events.json").read_text()
    out = extract(run, st, k, model, claims=claims, review=(cur, obj))
    obj2 = objections(st, k, check_claims=claims)
    run.log(para=nm, stage="re-read", ok=not obj2, note=" | ".join(obj2))
    return obj2


def objections(st: Story, k: int, check_claims: bool = True) -> list[str]:
    """What the checker says is wrong with paragraph k, as the writer should hear it."""
    r = report(st.d)
    if "error" in r:
        return [f"the story file could not be read: {r['error']}"]
    p = next((p for p in r["paragraphs"] if p["name"] == f"{k:02}"), None)
    if p is None:
        return []
    out = [f"'{e['gloss']}' cannot happen: {e['why']}" for e in p["events"] if e["status"] == "no"]
    out += [f"'{e['gloss']}' has no reason in the story so far (nobody wants it; give the character a reason on the page or cut it)"
            for e in p["events"] if e["unmotivated"]]
    if check_claims:
        out += [f"the paragraph implies '{c['claim']}', but the events do not support it" for c in p["claims"] if not c["holds"]]
    out += p["errors"]
    return out


def brief(st: Story, k: int) -> str:
    return st.spec["outline"][k - 1]["brief"]


def paras_arg(s: str, n: int) -> list[int]:
    if not s:
        return list(range(1, n + 1))
    a, _, b = s.partition("-")
    return list(range(int(a), int(b or a) + 1))


# ---------------------------------------------------------------------------- workflow 2

def incremental(d: Path, paras: str, writer: str, annotator: str, max_rewrites: int = 2):
    st = Story(d)
    run = Run(d, "incremental")
    for k in paras_arg(paras, len(st.spec["outline"])):
        nm = f"{k:02}"
        draft, objection = "", ""
        for attempt in range(max_rewrites + 1):
            draft = run.call(writer, write_prompt(st, k, brief(st, k), None, objection, draft),
                             WRITER_SYSTEM, f"write a{attempt}", nm).strip()
            (st.pdir / f"{nm}.txt").write_text(draft + "\n")
            for f in [f"{nm}.json", f"{nm}.events.json"]:
                (st.pdir / f).unlink(missing_ok=True)
            if not annotate(run, st, k, annotator):
                run.log(para=nm, stage="annotation", ok=False, note="not accepted after 3 rounds")
            extract(run, st, k, writer)
            obj = objections(st, k)
            run.log(para=nm, stage="check", ok=not obj, note=" | ".join(obj))
            if obj:
                run.objections += [{"para": nm, "attempt": attempt, "stage": "reading", "why": o} for o in obj]
                obj = reread(run, st, k, writer, obj)
            if not obj:
                break
            run.objections += [{"para": nm, "attempt": attempt, "stage": "prose", "why": o} for o in obj]
            if attempt == max_rewrites:
                break
            run.rewrites += 1
            objection = "\n".join(f"- {o}" for o in obj)
    write_summary(d, "incremental", run.summary())


# ---------------------------------------------------------------------------- workflow 1

def plan_prompt(st: Story, k: int, previous: list[str], objection: str = "", prev: str = "") -> str:
    o = st.spec["outline"][k - 1]
    return "\n".join([
        "Plan one paragraph of a story as a list of events in the story world's event language.",
        "\n## The world\n" + st.world_text(), "\n## Event language\n" + EVENT_SYNTAX,
        "\n## The beats\n" + "\n".join(f"- {b['id']}: {b['label']} (key events: {', '.join(b.get('keys', []))})"
                                        for b in st.spec["beats"]["vocab"]),
        "\n## Events planned so far\n" + ("\n".join(previous) or "(none)"),
        f"\n## Paragraph {k} (beat: {o['beat']})\n{o['brief']}",
        "\nInclude the beat's key event if this paragraph realises the beat. Give characters reasons "
        "(adopt, intend) for the moves they make. Also list 1-3 claims (" + CLAIM_SYNTAX.splitlines()[0] +
        ") that should hold after the paragraph.\n" + CLAIM_SYNTAX,
        (f"\n## Your previous plan\n{prev}\n\n## The checker objects\n{objection}\nRepair the plan." if objection else ""),
        "\nOutput JSON only: {\"events\": [\"...\"], \"claims\": [\"...\"]}"])


def refinement_objections(st: Story, ks: list[int]) -> dict[int, str]:
    """Why the plans do not abstract to the beat story: each beat's key event
    must occur exactly once, in a paragraph of that beat."""
    keys = {e: b["id"] for b in st.spec["beats"]["vocab"] for e in b.get("keys", [])}
    beat_of = {k: st.spec["outline"][k - 1]["beat"] for k in ks}
    found: dict[str, list[int]] = {}
    out: dict[int, list[str]] = {}
    for k in ks:
        plan = json.loads((st.pdir / f"{k:02}.plan.json").read_text())
        for e in plan.get("events", []):
            if e in keys:
                found.setdefault(keys[e], []).append(k)
                if keys[e] != beat_of[k]:
                    out.setdefault(k, []).append(f"`{e}` is the key event of beat '{keys[e]}', which belongs to "
                                                 f"another paragraph; this paragraph is beat '{beat_of[k]}'. Express it differently or drop it.")
    for b in st.spec["beats"]["vocab"]:
        mine = [k for k in ks if beat_of[k] == b["id"]]
        got = [k for k in found.get(b["id"], []) if beat_of[k] == b["id"]]
        if mine and not got:
            out.setdefault(mine[-1], []).append(f"this paragraph must contain the key event of beat '{b['id']}': one of {', '.join(b['keys'])}")
        for k in got[:-1] if len(got) > 1 else []:
            out.setdefault(k, []).append(f"the key event of beat '{b['id']}' occurs again in a later paragraph ({got[-1]}); keep it only there")
    return {k: "\n".join(v) for k, v in out.items()}


def topdown(d: Path, paras: str, writer: str, annotator: str, max_rewrites: int = 2):
    st = Story(d)
    run = Run(d, "topdown")
    ks = paras_arg(paras, len(st.spec["outline"]))
    r = report(d)
    run.log(stage="beats", ok=bool(r.get("beats", {}).get("valid")), note=str(r.get("beats", {}).get("failure")))
    # layer 1 -> 2: plans, checked as a story before any prose
    for k in ks:
        nm = f"{k:02}"
        prev, objection = "", ""
        for attempt in range(max_rewrites + 1):
            raw = run.call(writer, plan_prompt(st, k, st.events_so_far(k), objection, prev), JSON_SYSTEM, f"plan a{attempt}", nm)
            try:
                plan = json.loads(extract_json(raw))
            except json.JSONDecodeError:
                plan = {"events": [], "claims": []}
            plan["beat"] = st.spec["outline"][k - 1]["beat"]
            (st.pdir / f"{nm}.plan.json").write_text(json.dumps(plan, indent=1))
            (st.pdir / f"{nm}.events.json").unlink(missing_ok=True)
            obj = objections(st, k)
            run.log(para=nm, stage="check plan", ok=not obj, note=" | ".join(obj))
            if not obj:
                break
            run.objections += [{"para": nm, "layer": "plan", "why": o} for o in obj]
            if attempt < max_rewrites:
                run.rewrites += 1
            prev, objection = json.dumps(plan), "\n".join(f"- {o}" for o in obj)
    for rnd in range(max_rewrites + 1):
        r = report(d)
        ok = bool(r.get("beats", {}).get("refines"))
        run.log(stage=f"plans refine beats r{rnd}", ok=ok, note=" ".join(r.get("beats", {}).get("abstracted", [])))
        if ok or rnd == max_rewrites:
            break
        for k, why in refinement_objections(st, ks).items():
            nm = f"{k:02}"
            run.objections.append({"para": nm, "layer": "refinement", "why": why})
            run.rewrites += 1
            prev = (st.pdir / f"{nm}.plan.json").read_text()
            raw = run.call(writer, plan_prompt(st, k, st.events_so_far(k), why, prev), JSON_SYSTEM, f"replan r{rnd}", nm)
            try:
                plan = json.loads(extract_json(raw))
            except json.JSONDecodeError:
                continue
            plan["beat"] = st.spec["outline"][k - 1]["beat"]
            (st.pdir / f"{nm}.plan.json").write_text(json.dumps(plan, indent=1))
            run.log(para=nm, stage="check plan", ok=not objections(st, k), note=" | ".join(objections(st, k)))
    # layer 2 -> 3: prose from plans, re-extracted and compared
    for k in ks:
        nm = f"{k:02}"
        plan = json.loads((st.pdir / f"{nm}.plan.json").read_text())
        draft, objection = "", ""
        for attempt in range(max_rewrites + 1):
            draft = run.call(writer, write_prompt(st, k, st.spec["outline"][k - 1]["brief"], plan["events"], objection, draft),
                             WRITER_SYSTEM, f"write a{attempt}", nm).strip()
            (st.pdir / f"{nm}.txt").write_text(draft + "\n")
            for f in [f"{nm}.json", f"{nm}.events.json"]:
                (st.pdir / f).unlink(missing_ok=True)
            annotate(run, st, k, annotator)
            extract(run, st, k, writer, claims=False)
            if objections(st, k, check_claims=False) or not (next(p for p in report(d)["paragraphs"] if p["name"] == nm).get("realisation") or {}).get("realises", True):
                reread(run, st, k, writer, objections(st, k, check_claims=False) or
                       ["the reading does not match the paragraph's plan; check each planned event is or is not asserted"], claims=False)
            rr = report(d)
            p = next(p for p in rr["paragraphs"] if p["name"] == nm)
            real = p.get("realisation") or {}
            obj = objections(st, k)
            if real and not real.get("realises"):
                obj.append("the paragraph does not realise its plan exactly: " +
                           (f"missing {', '.join(real['missing'])}; " if real.get("missing") else "") +
                           (f"it also asserts {', '.join(real['extra'])}" if real.get("extra") else ""))
            run.log(para=nm, stage="check prose", ok=not obj, note=" | ".join(obj))
            if not obj:
                break
            run.objections += [{"para": nm, "layer": "prose", "why": o} for o in obj]
            if attempt == max_rewrites:
                break
            run.rewrites += 1
            objection = "\n".join(f"- {o}" for o in obj)
    write_summary(d, "topdown", run.summary())


# ---------------------------------------------------------------------------- workflow 3

def posthoc(d: Path, paras: str, writer: str, annotator: str):
    st = Story(d)
    run = Run(d, "posthoc")
    n = len(st.spec["outline"])
    prompt = "\n".join([
        f"Write the short story '{st.spec.get('title', '')}' in {n} paragraphs, one per item of the outline below.",
        "Kiran is the author herself (a self-insert); write her as Kiran.",
        "\n## The people\n" + st.persona_text(),
        f"\n## Explicitness\n{st.meta.get('explicitness', 'sensual but not graphic')}",
        "\n## " + CRAFT.replace("Write ONE paragraph of 80 to 150 words.", "Each paragraph 80 to 150 words."),
        "\n## Outline\n" + "\n".join(f"{i + 1}. {o['brief']}" for i, o in enumerate(st.spec["outline"])),
        f"\nOutput exactly {n} paragraphs separated by blank lines, nothing else."])
    raw = run.call(writer, prompt, WRITER_SYSTEM, "write all")
    ps = [p.strip() for p in re.split(r"\n\s*\n", raw.strip()) if p.strip()]
    run.log(stage="split", ok=len(ps) == n, note=f"{len(ps)} paragraphs")
    for f in st.pdir.glob("*"):
        f.unlink()
    for i, p in enumerate(ps[:n], 1):
        (st.pdir / f"{i:02}.txt").write_text(p + "\n")
    for k in range(1, min(n, len(ps)) + 1):
        nm = f"{k:02}"
        annotate(run, st, k, annotator)                       # layer 1: the parts-of-speech tree
        out = extract(run, st, k, writer, claims=False)       # layer 2: scene events
        claims = run.call(writer, "\n".join([                 # layer 3: beliefs, relationships, consent
            "Read this paragraph of a story and state what it implies about the characters' minds and "
            "relationships right after it.", "\n## The world\n" + st.world_text(), "\n## Claim language\n" + CLAIM_SYNTAX,
            "\n## Story so far\n" + st.prose_so_far(k), f"\n## Paragraph {k}\n" + (st.pdir / f"{nm}.txt").read_text(),
            "\nList 1-4 claims that the paragraph makes true (new beliefs, false beliefs, consent, bonds). "
            "Output JSON only: {\"claims\": [\"...\"]}"]), JSON_SYSTEM, "claims", nm)
        try:
            out["claims"] = json.loads(extract_json(claims)).get("claims", [])
        except json.JSONDecodeError:
            out["claims"] = []
        (st.pdir / f"{nm}.events.json").write_text(json.dumps(out, indent=1))
        obj = objections(st, k)                               # layer 4: the implications between layers
        run.log(para=nm, stage="check", ok=not obj, note=" | ".join(obj))
        run.objections += [{"para": nm, "why": o} for o in obj]
    write_summary(d, "posthoc", run.summary())


def write_summary(d: Path, name: str, s: dict):
    r = report(d)
    if "paragraphs" in r:
        s["paragraphs"] = len(r["paragraphs"])
        s["valid paragraphs"] = sum(p["verdict"] == "valid" for p in r["paragraphs"])
        s["failing paragraphs"] = sum(p["verdict"] == "failing" for p in r["paragraphs"])
        s["claims failing"] = sum(not c["holds"] for p in r["paragraphs"] for c in p["claims"])
        s["annotations accepted"] = sum(bool(p["doc"] and p["doc"]["check"]["ok"]) for p in r["paragraphs"])
        s["story"] = "valid" if r["verdict"]["valid"] else "plausible" if r["verdict"]["plausible"] else "failing"
    f = d / "runs" / "summary.json"
    allsum = json.loads(f.read_text()) if f.exists() else {}
    allsum[name] = s
    f.write_text(json.dumps(allsum, indent=1))
    print(json.dumps(s, indent=1))


def compare(dirs: list[Path]):
    merged = {}
    for d in dirs:
        f = d / "runs" / "summary.json"
        if f.exists():
            merged.update(json.loads(f.read_text()))
    for d in dirs:
        (d / "runs").mkdir(exist_ok=True)
        (d / "runs" / "summary.json").write_text(json.dumps(merged, indent=1))
    print(json.dumps(merged, indent=1))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("workflow", choices=["incremental", "topdown", "posthoc", "compare"])
    ap.add_argument("dirs", nargs="+")
    ap.add_argument("--paras", default="")
    ap.add_argument("--writer", default="opus")
    ap.add_argument("--annotator", default="opus")
    a = ap.parse_args()
    dirs = [Path(x).resolve() for x in a.dirs]
    if a.workflow == "compare":
        return compare(dirs)
    fn = {"incremental": incremental, "topdown": topdown, "posthoc": posthoc}[a.workflow]
    fn(dirs[0], a.paras, a.writer, a.annotator)


if __name__ == "__main__":
    main()
