"""The Studio's checking CLI. It makes no model calls: an interactive agent
(a Claude session Kiran can see) writes the prose, the annotation and the
event readings, and drives these checks; the Studio shows the results live.

    python3 studio/workflows.py status          <story>
    python3 studio/workflows.py brief           <story> <n>   what the writer needs for paragraph n
    python3 studio/workflows.py tokens          <story> <n>   the tokens the annotation's leaves must be
    python3 studio/workflows.py extract         <story> <n>   the event language, world and rules for reading n
    python3 studio/workflows.py paragraph-check <story> <n>   annotation (langlib check), events, claims, plan
    python3 studio/workflows.py plan-check      <story> [n]   beats valid; paragraph plans (NN.plan.json) valid
    python3 studio/workflows.py refine-check    <story>       plans and prose refine the beats
    python3 studio/workflows.py prove           <story>       Proofs.lean regenerated and checked
    python3 studio/workflows.py log             <story> <workflow> <stage> [--para NN] [--ok|--fail] [--note ...]
    python3 studio/workflows.py summary         <story> <workflow>
    python3 studio/workflows.py compare         <story> <story> ...

Checks print what is wrong as the writer should hear it and exit 1 when
something is; with `--log <workflow>` they also append their verdict to
runs/<workflow>.jsonl, which the Studio's run panel shows.

The workflows (docs/ui-spec.md), as the agent runs them:

* incremental: per paragraph k: `brief`, write NN.txt; `tokens`, write the
  annotation NN.json (eval/prompt.md); `extract`, write NN.events.json;
  `paragraph-check` until it passes (re-read before blaming the prose, then
  rewrite the prose with the checker's `why`); `prove`; next paragraph.
* topdown: `plan-check` the beats; write NN.plan.json per paragraph and
  `plan-check` them; `refine-check`; then write prose per plan and
  `paragraph-check` (which also compares the prose's events with its plan).
* posthoc: write all of NN.txt; then per paragraph annotate, extract events,
  then claims, `paragraph-check`.

Every langlib/lake child goes through studio/procs.py: own process group,
nice -n 10, a timeout, one Lean job at a time machine-wide.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
import urllib.request
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import procs  # noqa: E402
import proofs  # noqa: E402
from procs import ROOT  # noqa: E402

SERVER = "http://127.0.0.1:8765"

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

READING_RULES = """\
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
- Claims (1-4) only about the listed fact ids, consent and bonds: who now believes what, false
  beliefs, consent given. No nested beliefs unless the paragraph is about what one character thinks
  another believes.
- Before blaming the prose for a checker objection, re-read: where the reading over-read the prose (an
  event or claim it does not assert) or missed a reason it does give, correct the reading; where the
  prose really asserts it, keep it, and the objection stands against the prose.
Write paragraphs/NN.events.json as
  {"events": [{"e": "...", "at": 12, "phase": "main", "src": "text"}], "claims": ["..."]}
"""

CRAFT = """\
Close third person, past tense, in Kiran's point of view (in scenes Kiran is not in, the point of view
of whoever is there). Interiority over choreography: what she notices, wants, hesitates over. Specific
sensory detail over adjectives; vary sentence rhythm; no cliches, no euphemism stacks. Dialogue in
double quotes ("), attributed. Keep the reader oriented in place and time. Consent is part of the
scene, said out loud, as character, not paperwork. One paragraph of 80 to 150 words."""


# ---------------------------------------------------------------------------- the story on disk

def langlib(*args: str, timeout: float = 120) -> procs.Result:
    for _ in range(60):  # the binary is briefly missing while `lake build` relinks it
        if procs.LANGLIB.exists():
            return procs.run(procs.langlib_argv(*args), timeout=timeout)
        time.sleep(2)
    raise FileNotFoundError(procs.LANGLIB)


def report(d: Path) -> dict:
    res = langlib("story", str(d))
    try:
        return json.loads(res.stdout)
    except json.JSONDecodeError:
        return {"error": (res.stderr or res.stdout)[-2000:]}


class Story:
    def __init__(self, d: Path):
        self.d = d
        self.spec = json.loads((d / "story.json").read_text())
        self.meta = json.loads((d / "meta.json").read_text()) if (d / "meta.json").exists() else {}
        self.pdir = d / "paragraphs"
        self.pdir.mkdir(exist_ok=True)

    def f(self, k: int, ext: str) -> Path:
        return self.pdir / f"{k:02}.{ext}"

    def outline(self, k: int) -> dict:
        o = self.spec.get("outline", [])
        return o[k - 1] if 0 < k <= len(o) else {}

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
        out = [f"- {c['name']} ({c['pron']}): {', '.join(c['traits'])}; cares most about {', then '.join(c['values'])}."
               for c in s["characters"]]
        bonds = s.get("start", {}).get("bonds", {})
        out.append("Starting feelings (0 none, 2 strong): " + "; ".join(
            f"{k.replace('>', ' toward ')}: " + ", ".join(f"{d} {n}" for d, n in v.items()) for k, v in bonds.items()))
        return "\n".join(out)

    def prose_so_far(self, upto: int) -> str:
        return "\n\n".join(self.f(i, "txt").read_text().strip() for i in range(1, upto) if self.f(i, "txt").exists())

    def events_so_far(self, upto: int) -> list[str]:
        evs = []
        for i in range(1, upto):
            if self.f(i, "events.json").exists():
                evs += [e["e"] for e in json.loads(self.f(i, "events.json").read_text()).get("events", [])]
            elif self.f(i, "plan.json").exists():
                evs += json.loads(self.f(i, "plan.json").read_text()).get("events", [])
        return evs

    def written(self) -> list[int]:
        return sorted(int(p.stem) for p in self.pdir.glob("[0-9][0-9].txt"))


def para(r: dict, k: int) -> dict | None:
    return next((p for p in r.get("paragraphs", []) if p["name"] == f"{k:02}"), None)


def objections(r: dict, k: int, check_claims: bool = True) -> list[str]:
    """What the checker says is wrong with paragraph k, as the writer should hear it."""
    if "error" in r:
        return [f"the story file could not be read: {r['error']}"]
    p = para(r, k)
    if p is None:
        return []
    out = [f"'{e['gloss']}' cannot happen: {e['why']}" for e in p["events"] if e["status"] == "no"]
    out += [f"'{e['gloss']}' has no reason in the story so far (nobody wants it; give the character a reason "
            "on the page or cut it)" for e in p["events"] if e["unmotivated"]]
    if check_claims:
        out += [f"the paragraph implies '{c['claim']}', but the events do not support it" for c in p["claims"] if not c["holds"]]
    out += p["errors"]
    real = p.get("realisation") or {}
    if real and not real.get("realises", True):
        out.append("the paragraph does not realise its plan exactly: " +
                   (f"missing {', '.join(real['missing'])}; " if real.get("missing") else "") +
                   (f"it also asserts {', '.join(real['extra'])}" if real.get("extra") else ""))
    return out


def annotation_feedback(rep: dict) -> list[str]:
    if "parseError" in rep:
        return [f"the annotation JSON was rejected: {rep['parseError']}"]
    out = []
    if not rep.get("tokensMatch", True):
        out.append(f"the leaves do not match the passage: {rep['srcTokens']} tokens in the text, "
                   f"{rep['treeTokens']} in the tree, {rep['editCount']} differences:")
        out += [f"  {e}" for e in rep["edits"]]
    if rep.get("badLeaves"):
        out.append("these leaves are not single tokens (split them): " + ", ".join(rep["badLeaves"]))
    out += [f"reference: {i}" for i in rep.get("refIssues", [])[:15]]
    return out


def check_annotation(st: Story, k: int) -> list[str]:
    doc = st.f(k, "json")
    if not doc.exists():
        return [f"no annotation yet: write {doc.relative_to(ROOT)} (eval/prompt.md; leaves = `tokens` output)"]
    res = langlib("check", str(st.f(k, "txt")), str(doc))
    try:
        rep = json.loads(res.stdout)
    except json.JSONDecodeError:
        rep = {"ok": False, "parseError": (res.stdout or res.stderr)[-1000:]}
    return [] if rep.get("ok") else annotation_feedback(rep) or ["langlib check rejected the annotation"]


# ---------------------------------------------------------------------------- run log

def log(d: Path, workflow: str | None, **kw) -> None:
    if not workflow:
        return
    (d / "runs").mkdir(exist_ok=True)
    kw.setdefault("t", round(time.time(), 1))
    with (d / "runs" / f"{workflow}.jsonl").open("a") as f:
        f.write(json.dumps(kw) + "\n")


def verdict_out(problems: list[str], ok_msg: str) -> int:
    if problems:
        print("\n".join(f"- {p}" for p in problems))
        return 1
    print(ok_msg)
    return 0


# ---------------------------------------------------------------------------- subcommands

def cmd_status(a) -> int:
    st = Story(a.story)
    r = report(a.story)
    if "error" in r:
        print(r["error"])
        return 1
    print(f"{st.spec.get('title', a.story.name)}: story {'valid' if r['verdict']['valid'] else 'plausible' if r['verdict']['plausible'] else 'failing'}")
    for p in r["paragraphs"]:
        doc = "annotated" if p["doc"] and p["doc"]["check"]["ok"] else "annotation missing/rejected"
        print(f"  {p['name']}: {p['verdict']}, {len(p['events'])} events, {doc}")
    pf = a.story / "proofs.json"
    if pf.exists():
        pr = json.loads(pf.read_text())
        bad = [k for k, v in pr.get("theorems", {}).items() if not v.get("ok")]
        print(f"proofs: {pr.get('status')} ({len(pr.get('theorems', {})) - len(bad)}/{len(pr.get('theorems', {}))} proved)")
    n = len(st.spec.get("outline", []))
    nxt = next((k for k in range(1, n + 1) if not st.f(k, "txt").exists()), None)
    if nxt:
        print(f"next: paragraph {nxt}: {st.outline(nxt).get('brief', '')}")
    print(f"meta: {json.dumps(st.meta)}")
    return 0


def cmd_brief(a) -> int:
    st, k = Story(a.story), a.n
    o = st.outline(k)
    print("\n".join([
        f"# Paragraph {k} of '{st.spec.get('title', '')}'" + (f" (beat: {o['beat']})" if o.get("beat") else ""),
        "Kiran is the author herself (a self-insert); write her as Kiran.",
        "\n## The people\n" + st.persona_text(),
        "\n## Point of view\n" + st.meta.get("pov", "close third, past tense, Kiran's"),
        "\n## Explicitness\n" + st.meta.get("explicitness", "sensual but not graphic"),
        "\n## Craft\n" + CRAFT,
        "\n## The story so far\n" + (st.prose_so_far(k) or "(this is the first paragraph)"),
        "\n## What happens\n" + o.get("brief", "(no outline entry)"),
    ]))
    if st.f(k, "plan.json").exists():
        plan = json.loads(st.f(k, "plan.json").read_text())
        print("\n## Its plan: assert exactly these events, in order, and nothing else of consequence\n" +
              "\n".join(f"- {e}" for e in plan.get("events", [])))
    print(f"\nWrite it to {st.f(k, 'txt').relative_to(ROOT)}.")
    return 0


def cmd_tokens(a) -> int:
    st = Story(a.story)
    res = langlib("tokenize", str(st.f(a.n, "txt")))
    toks = res.stdout.splitlines()
    print(" ".join(f"{i}:{t}" for i, t in enumerate(toks)))
    print(f"\n{len(toks)} tokens. Entity ids: " + ", ".join(
        [c["id"] for c in st.spec["characters"]] + [p["id"] for p in st.spec["places"]] + [o["id"] for o in st.spec["objects"]]))
    return 0


def cmd_extract(a) -> int:
    st, k = Story(a.story), a.n
    toks = langlib("tokenize", str(st.f(k, "txt"))).stdout.splitlines()
    print("\n".join([
        f"# Reading paragraph {k}: the events it asserts, in the story world's event language",
        "\n## The world\n" + st.world_text(),
        "\n## Event language\n" + EVENT_SYNTAX,
        "\n## Claim language\n" + CLAIM_SYNTAX,
        "\n## Events of the earlier paragraphs (do not repeat them)\n" + ("\n".join(st.events_so_far(k)) or "(none)"),
        f"\n## Paragraph {k}\n" + st.f(k, "txt").read_text().strip(),
        "\n## Its tokens\n" + " ".join(f"{i}:{t}" for i, t in enumerate(toks)),
        "\n## Rules\n" + READING_RULES,
    ]))
    return 0


def cmd_paragraph_check(a) -> int:
    st, k = Story(a.story), a.n
    if not st.f(k, "txt").exists():
        return verdict_out([f"no prose: {st.f(k, 'txt').relative_to(ROOT)}"], "")
    ann = check_annotation(st, k)
    r = report(a.story)
    obj = [] if st.f(k, "events.json").exists() or st.f(k, "plan.json").exists() else \
        [f"no reading yet: write {st.f(k, 'events.json').relative_to(ROOT)} (`extract` prints the rules)"]
    obj += objections(r, k)
    p = para(r, k)
    log(a.story, a.log, para=f"{k:02}", stage="paragraph-check", ok=not (ann or obj),
        annotation=not ann, verdict=p and p["verdict"], note=" | ".join(ann[:3] + obj)[:1000])
    if p:
        print(f"paragraph {k:02}: {p['verdict']}; " + "; ".join(e["gloss"] + ("" if e["status"] == "yes" else f" [{e['status']}]")
                                                         for e in p["events"]))
        if p.get("assumptions"):
            print("assumptions: " + "; ".join(map(str, p["assumptions"])))
    return verdict_out([f"annotation: {x}" for x in ann] + obj, "ok: annotation accepted, events possible and motivated, claims hold")


def cmd_plan_check(a) -> int:
    st = Story(a.story)
    r = report(a.story)
    if "error" in r:
        return verdict_out([r["error"]], "")
    b = r.get("beats") or {}
    out = [] if b.get("valid", True) else [f"the beat story is not valid: {b.get('failure')}"]
    ks = [a.n] if a.n else [k for k in range(1, len(st.spec.get("outline", [])) + 1) if st.f(k, "plan.json").exists()]
    for k in ks:
        out += [f"{k:02} plan: {o}" for o in objections(r, k)]
    log(a.story, a.log, stage="plan-check", para=f"{a.n:02}" if a.n else "", ok=not out, note=" | ".join(out)[:1000])
    return verdict_out(out, f"ok: beats valid; plans {', '.join(f'{k:02}' for k in ks) or '(none)'} valid")


def refinement_objections(st: Story, ks: list[int]) -> dict[int, list[str]]:
    """Why the plans do not abstract to the beat story: each beat's key event
    must occur exactly once, in a paragraph of that beat."""
    vocab = st.spec.get("beats", {}).get("vocab", [])
    keys = {e: b["id"] for b in vocab for e in b.get("keys", [])}
    beat_of = {k: st.outline(k).get("beat") for k in ks}
    found: dict[str, list[int]] = {}
    out: dict[int, list[str]] = {}
    for k in ks:
        src = st.f(k, "events.json") if st.f(k, "events.json").exists() else st.f(k, "plan.json")
        evs = [e["e"] if isinstance(e, dict) else e for e in json.loads(src.read_text()).get("events", [])]
        for e in evs:
            if e in keys:
                found.setdefault(keys[e], []).append(k)
                if keys[e] != beat_of[k]:
                    out.setdefault(k, []).append(f"`{e}` is the key event of beat '{keys[e]}', which belongs to another "
                                                 f"paragraph; this paragraph is beat '{beat_of[k]}'")
    for b in vocab:
        mine = [k for k in ks if beat_of[k] == b["id"]]
        got = [k for k in found.get(b["id"], []) if beat_of[k] == b["id"]]
        if mine and not got and max(mine) <= max(ks):
            out.setdefault(mine[-1], []).append(f"the beat '{b['id']}' needs its key event in its paragraphs: one of {', '.join(b['keys'])}")
        for k in got[:-1] if len(got) > 1 else []:
            out.setdefault(k, []).append(f"the key event of beat '{b['id']}' occurs again later ({got[-1]}); keep it only there")
    return out


def cmd_refine_check(a) -> int:
    st = Story(a.story)
    r = report(a.story)
    if "error" in r:
        return verdict_out([r["error"]], "")
    b = r.get("beats") or {}
    ks = [k for k in st.written() or range(1, len(st.spec.get("outline", [])) + 1)
          if st.f(k, "events.json").exists() or st.f(k, "plan.json").exists()]
    done = [k for k in ks if all(st.outline(j).get("beat") != st.outline(k).get("beat") or j in ks
                                 for j in range(1, len(st.spec.get("outline", [])) + 1))]
    abstracted, story = b.get("abstracted", []), b.get("story", [])
    out = []
    complete = len(ks) == len(st.spec.get("outline", []))
    if complete and not b.get("refines"):
        out.append(f"the paragraphs abstract to {abstracted}, not the beat story {story}")
    elif not complete and abstracted != story[:len(abstracted)]:
        out.append(f"so far the paragraphs abstract to {abstracted}, which is not a prefix of the beat story {story}")
    for k, why in sorted(refinement_objections(st, done if not complete else ks).items()):
        out += [f"{k:02}: {w}" for w in why]
    print(f"beats: {'valid' if b.get('valid') else 'invalid'}; abstracted so far: {' '.join(abstracted) or '(none)'}")
    log(a.story, a.log, stage="refine-check", ok=not out, note=" | ".join(out)[:1000])
    return verdict_out(out, "ok: the layers refine " + ("the beat story" if complete else "a prefix of the beat story"))


def server_prove(d: Path, timeout: float) -> dict | None:
    """Ask the running Studio to prove (so its UI shows it) and wait for proofs.json."""
    pf = d / "proofs.json"
    before = json.loads(pf.read_text()).get("at", 0) if pf.exists() else 0
    try:
        urllib.request.urlopen(urllib.request.Request(f"{SERVER}/api/story/{d.name}/prove", method="POST"), timeout=3)
    except OSError:
        return None
    t0 = time.time()
    while time.time() - t0 < timeout:
        time.sleep(2)
        try:
            pr = json.loads(pf.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        if pr.get("at", 0) > max(before, t0):
            return pr
    return {"status": "timeout", "theorems": {}, "errors": [f"no result from the Studio after {timeout}s"]}


def cmd_prove(a) -> int:
    pr = None if a.local else server_prove(a.story, proofs.LEAN_TIMEOUT + 60)
    if pr is None:
        pr = proofs.prove(a.story)
    thms = pr.get("theorems", {})
    bad = {k: v for k, v in thms.items() if not v.get("ok")}
    print(f"proofs: {pr['status']} in {pr.get('secs', '?')}s: {len(thms) - len(bad)}/{len(thms)} theorems proved")
    log(a.story, a.log, stage="prove", ok=pr["status"] == "ok", note=f"{len(thms) - len(bad)}/{len(thms)}; " +
        " | ".join(f"{k}: {v.get('error', '')[:150]}" for k, v in bad.items())[:1000])
    problems = [f"{k} ({v['statement'][:120]}): {v.get('error', 'failed')[:300]}" for k, v in bad.items()]
    problems += [e for e in pr.get("errors", []) if not bad] + ([pr["error"]] if pr.get("error") else [])
    return verdict_out(problems if pr["status"] != "ok" else [], "ok: every theorem proved")


def cmd_log(a) -> int:
    log(a.story, a.workflow, stage=a.stage, para=a.para or "", ok=a.ok, note=a.note or "")
    return 0


def cmd_summary(a) -> int:
    f = a.story / "runs" / f"{a.workflow}.jsonl"
    steps = [json.loads(l) for l in f.read_text().splitlines() if l.strip()] if f.exists() else []
    checks = [s for s in steps if s.get("stage") in ("paragraph-check", "plan-check", "refine-check")]
    s = {"checks run": len(checks), "checks failed": sum(not c.get("ok") for c in checks),
         "rewrites": sum(s.get("stage") == "rewrite" for s in steps),
         "re-reads": sum(s.get("stage") == "re-read" for s in steps),
         "annotation rounds": sum(s.get("stage") == "annotate" for s in steps) or None,
         "model calls": 0, "writer": "interactive agent"}
    if len(steps) > 1:
        s["wall secs"] = round(steps[-1]["t"] - steps[0]["t"])
    r = report(a.story)
    if "paragraphs" in r:
        s["paragraphs"] = len(r["paragraphs"])
        s["valid paragraphs"] = sum(p["verdict"] == "valid" for p in r["paragraphs"])
        s["failing paragraphs"] = sum(p["verdict"] == "failing" for p in r["paragraphs"])
        s["claims failing"] = sum(not c["holds"] for p in r["paragraphs"] for c in p["claims"])
        s["annotations accepted"] = sum(bool(p["doc"] and p["doc"]["check"]["ok"]) for p in r["paragraphs"])
        s["story"] = "valid" if r["verdict"]["valid"] else "plausible" if r["verdict"]["plausible"] else "failing"
    sf = a.story / "runs" / "summary.json"
    allsum = json.loads(sf.read_text()) if sf.exists() else {}
    allsum[a.workflow] = s
    sf.write_text(json.dumps(allsum, indent=1))
    print(json.dumps(s, indent=1))
    return 0


def cmd_compare(a) -> int:
    merged = {}
    for d in a.stories:
        f = d / "runs" / "summary.json"
        if f.exists():
            merged.update(json.loads(f.read_text()))
    for d in a.stories:
        (d / "runs").mkdir(exist_ok=True)
        (d / "runs" / "summary.json").write_text(json.dumps(merged, indent=1))
    print(json.dumps(merged, indent=1))
    return 0


def main() -> int:
    procs.install_signal_handlers()
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)

    def story_cmd(name, fn, n=None, help=""):
        p = sub.add_parser(name, help=help)
        p.add_argument("story", type=lambda s: Path(s).resolve())
        if n == "required":
            p.add_argument("n", type=int)
        elif n == "optional":
            p.add_argument("n", type=int, nargs="?", default=0)
        p.add_argument("--log", metavar="WORKFLOW", help="append the verdict to runs/WORKFLOW.jsonl")
        p.set_defaults(fn=fn)
        return p

    story_cmd("status", cmd_status, help="paragraphs, verdicts, proofs, what is next")
    story_cmd("brief", cmd_brief, "required", "what the writer needs for paragraph n")
    story_cmd("tokens", cmd_tokens, "required", "paragraph n's tokens, numbered")
    story_cmd("extract", cmd_extract, "required", "event language, world and rules for reading paragraph n")
    story_cmd("paragraph-check", cmd_paragraph_check, "required", "annotation, events, claims, plan of paragraph n")
    story_cmd("plan-check", cmd_plan_check, "optional", "beats and paragraph plans valid")
    story_cmd("refine-check", cmd_refine_check, help="paragraphs refine the beat story")
    story_cmd("prove", cmd_prove, help="regenerate and check Proofs.lean").add_argument(
        "--local", action="store_true", help="prove here even if the Studio is running")
    story_cmd("summary", cmd_summary, help="summarise a workflow's run log").add_argument("workflow")
    lp = story_cmd("log", cmd_log, help="append a step to runs/WORKFLOW.jsonl")
    lp.add_argument("workflow")
    lp.add_argument("stage")
    lp.add_argument("--para")
    lp.add_argument("--note")
    g = lp.add_mutually_exclusive_group()
    g.add_argument("--ok", dest="ok", action="store_true", default=None)
    g.add_argument("--fail", dest="ok", action="store_false")
    cp = sub.add_parser("compare", help="merge the workflows' summaries")
    cp.add_argument("stories", nargs="+", type=lambda s: Path(s).resolve())
    cp.set_defaults(fn=cmd_compare)
    a = ap.parse_args()
    return a.fn(a)


if __name__ == "__main__":
    sys.exit(main())
