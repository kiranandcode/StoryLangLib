"""Stories' inferences in the shape of `langlib rules` (LangLib/Studio/RulesView.lean),
so the Rules view draws a story's reasoning the way it draws a paper's.

Sources, each already computed elsewhere:

- `langlib story <dir>`: the story's argument graph (Complete.lean
  `argumentGraph`). A belief supported by what a character saw is a rule of
  perception, by what someone said a rule of testimony, by a connective in the
  prose (‘so’, ‘because’) a connective inference, by the story's lore
  (story.json `lore`) a strict lore rule. A belief the reading marks as the
  character's own inference (Minds: `src: inferred`) is the lore rule that
  concludes it when there is one, else an inference with no recorded grounds.
  "The world says otherwise" and "revised in ¶ n" are rebuttals.
- `langlib power <dir>` (studio/power-schema.md): a move of a rule-based
  power system (Nen) is a strict rule from its checked preconditions to the
  move; a counterfactual is the opposing position, out, at the check that fails.
- LangLib/World/Examples/DeathNoteArc.lean: the arc is not exported to JSON
  yet (docs/gaps/death-note.md, step 4), so `deathnote()` reads its
  `Deduction` rules and its `clue` / `conclude` / `suspect` / `reveal` moves
  from the Lean source. The arc has no prose; its paragraphs are the moves in
  words.
- `from_dl`: a ground defeasible theory (LangLib/Story/DL.lean: facts, strict,
  defeasible and defeater rules, superiority) for whichever module exports one.
  A defeater undercuts the rules for the opposite head; superiority decides
  which way a rebuttal goes.

Each rule may carry fields the paper rules do not: `gloss` (words for the
conclusion when no quote is verbatim), `who`, `group`, `note`; a premise may
carry `gloss`, `tagLabel` and `fail` (a precondition that does not hold).

Every rule has a typed scheme (World/Rules `Scheme.spec`) and every premise a
`role` (a slot id, RulesView.lean `slotS`): lore and power-system checks are
rule applications (condition), what a character saw perception (perceived),
what someone said witness testimony (said), a connective cause to effect
(cause), a character's own inference and the arc's detective deductions
abduction (observed; rival where the source eliminates alternatives, else the
rival is an enthymeme), a fair-play reveal deduction (premise). Rules over
`MAX_FAN_IN` premises are regrouped (`fan_in`). The server and the CLI then
check the document with `langlib rules-json` (rules_docs.check / acheck).
"""
from __future__ import annotations

import re
from pathlib import Path

from procs import ROOT

DN_SOURCE = ROOT / "LangLib/World/Examples/DeathNoteArc.lean"


# ------------------------------------------------------------------ shared

def grounded(ids: list[str], attacks: list[tuple[str, str]]) -> dict[str, str]:
    """The grounded labelling (Caminada 2006) of `ids` under (src, tgt) attacks."""
    att = {i: [s for s, t in attacks if t == i] for i in ids}
    lab: dict[str, str] = {}
    changed = True
    while changed:
        changed = False
        for i in ids:
            if i in lab:
                continue
            if all(lab.get(a) == "out" for a in att[i]):
                lab[i] = "in"
                changed = True
            elif any(lab.get(a) == "in" for a in att[i]):
                lab[i] = "out"
                changed = True
    return {i: lab.get(i, "undec") for i in ids}


def reached(rules: list[dict], tgt: str) -> list[str]:
    """`tgt` and every rule built on it (an attack on a sub-argument reaches the argument)."""
    out, todo = [], [tgt]
    while todo:
        x = todo.pop()
        if x in out:
            continue
        out.append(x)
        todo += [r["id"] for r in rules if any(p.get("sub") == x for p in r["premises"])]
    return out


def propagate(rules: list[dict], key: str = "label") -> None:
    """A rule on an OUT (UNDEC) sub-rule is itself OUT (UNDEC), whatever it was given."""
    by = {r["id"]: r for r in rules}
    for _ in range(len(rules)):
        for r in rules:
            subs = [by[p["sub"]][key] for p in r["premises"] if p.get("sub") in by]
            if "out" in subs and r[key] != "out":
                r[key] = "out"
            elif "undec" in subs and r[key] == "in":
                r[key] = "undec"


def package(rules: list[dict], attacks: list[dict], root: str = "", groups: list[dict] | None = None) -> dict:
    for a in attacks:
        a.setdefault("on", None)
        a.setdefault("ok", True)
        a.setdefault("quote", "")
        a["reaches"] = reached(rules, a["tgt"]) if a["ok"] else []
    for r in rules:
        r.setdefault("cqs", [])
        r.setdefault("thin", [])
        r.setdefault("bare", False)
        r.setdefault("sceptic", r["label"])
    return {"root": root, "rules": rules, "attacks": attacks,
            "bare": [r["id"] for r in rules if r["bare"]], "bareLeaves": [],
            "thin": [{"id": r["id"], "why": r["thin"]} for r in rules if r["thin"]],
            "ok": True, "errors": [], "groups": groups or []}


def _offsets(text: str, toks: list[dict]) -> list[tuple[int, int]]:
    """Character offsets of each token (tokens are substrings, in order; Prose.tsx `align`)."""
    out, at = [], 0
    for t in toks:
        i = text.find(t.get("w", ""), at)
        if i < 0:
            out.append((at, at))
            continue
        out.append((i, i + len(t["w"])))
        at = i + len(t["w"])
    return out


def segment(text: str, pos: int) -> str:
    """The clause-sized stretch of `text` around `pos`: its sentence, cut at , ; : and dashes."""
    starts = [0] + [m.end() for m in re.finditer(r"[.!?][”\"’)]?\s+|[,;:—]\s*|\s+–\s+", text)]
    ends = [m.start() for m in re.finditer(r"[.!?][”\"’)]?(\s|$)|[,;:—]|\s+–\s+", text)] + [len(text)]
    a = max([s for s in starts if s <= pos] or [0])
    b = min([e for e in ends if e >= pos] or [len(text)])
    s = text[a:b].strip().strip("“”\"")
    if len(s.split()) < 3:   # too short to recognise: take the sentence
        a = max([m.end() for m in re.finditer(r"[.!?][”\"’)]?\s+", text[:pos])] or [0])
        m = re.search(r"[.!?]", text[pos:])
        s = text[a:pos + (m.end() if m else len(text))].strip()
    return s


# ------------------------------------------------------------------ fan-in

MAX_FAN_IN = 6   # World/Rules.lean `maxFanIn`
PARALLEL = {"perception", "witness testimony", "abduction (best explanation)", "sign"}


def fan_in(rules: list[dict]) -> list[dict]:
    """Rules with more than MAX_FAN_IN premises, regrouped (World/Rules `faults`:
    fanIn). Independent support (what several saw or said) splits into parallel
    rules for the same conclusion; a conjunction (a rule's conditions) nests:
    each run of premises becomes a sub-rule concluding that they hold, and the
    rule rests on the sub-rules."""
    out = []
    for r in rules:
        ps = r["premises"]
        if len(ps) <= MAX_FAN_IN:
            out.append(r)
            continue
        chunks = [ps[i:i + MAX_FAN_IN] for i in range(0, len(ps), MAX_FAN_IN)]
        if r["scheme"] in PARALLEL:
            for k, ch in enumerate(chunks):
                out.append({**r, "id": r["id"] + ("" if k == 0 else "abcdefghij"[k]), "premises": ch})
            continue
        top = []
        for k, ch in enumerate(chunks):
            sid = f"{r['id']}.{k + 1}"
            words = "; ".join(p.get("gloss") or p["t"] for p in ch)
            sub = {**r, "id": sid, "concl": f"{r['concl']}#{k + 1}", "quote": "", "gloss": words, "premises": ch,
                   "note": f"A group of {r['id']}'s premises (a rule takes at most {MAX_FAN_IN})."}
            out.append(sub)
            top.append({"t": sub["concl"], "tag": ch[0]["tag"], "tagLabel": None, "quote": "", "gloss": words,
                        "para": r.get("para", ""), "sub": sid, "role": ch[0].get("role", "condition"),
                        **({"fail": "; ".join(p["fail"] for p in ch if p.get("fail"))} if any(p.get("fail") for p in ch) else {})})
        out.append({**r, "premises": top})
    return out


# ------------------------------------------------------------------ a story's argument graph

def _story_rules(report: dict, spec: dict) -> tuple[list[dict], list[dict]]:
    """Each support of the argument graph as a rule under a typed scheme
    (World/Rules `Scheme.spec`), every premise in a slot:

    - lore (story.json `lore`): rule application, a condition per premise;
    - a connective in the prose ('so', 'because') without lore: cause to effect;
    - what a character saw: perception (perceived);
    - what someone said: witness testimony (said);
    - a character's own inference (Minds `src: inferred`): abduction, from what
      they came to hold earlier in the same paragraph (observed). The reading
      records no alternatives, so the rival is left unstated: an enthymeme.
    """
    g = report.get("argument") or {"nodes": [], "edges": []}
    nodes = {n["id"]: n for n in g["nodes"]}
    names = {c["id"]: c["name"] for c in report.get("characters", [])}
    paras = {p["name"]: p for p in report.get("paragraphs", [])}
    offs: dict[str, list[tuple[int, int]]] = {}

    def quote(n: dict) -> tuple[str, str]:
        for at in n.get("ats") or []:
            _, pn, k = at.split(":")
            p = paras.get(pn)
            if not p:
                continue
            if pn not in offs:
                offs[pn] = _offsets(p["text"], (p.get("doc") or {}).get("tokens", []))
            k = int(k)
            if k < len(offs[pn]):
                return segment(p["text"], offs[pn][k][0]), pn
        return "", n.get("para", "")

    def tok(n: dict) -> tuple[str, int]:
        for at in n.get("ats") or []:
            _, pn, k = at.split(":")
            return pn, int(k)
        return n.get("para", ""), 10 ** 6

    rules: list[dict] = []
    concl_of: dict[str, str] = {}      # node id → the rule concluding it
    counters: dict[str, int] = {}

    def new_id(prefix: str) -> str:
        counters[prefix] = counters.get(prefix, 0) + 1
        return f"{prefix}{counters[prefix]}"

    def premise(nid: str, tag: str, role: str, label: str = "") -> dict:
        n = nodes.get(nid, {"gloss": nid, "para": ""})
        q, pn = quote(n)
        return {"t": nid, "tag": tag, "tagLabel": label or None, "quote": q, "gloss": n.get("gloss", nid),
                "para": pn, "sub": None, "role": role}

    def rule(prefix: str, tgt: str, kind: str, scheme: str, prems: list[dict], note: str = "") -> dict:
        n = nodes[tgt]
        q, pn = quote(n)
        who = names.get(n.get("who", ""), "")
        r = {"id": new_id(prefix), "concl": tgt, "quote": q, "gloss": (f"{who}: " if n["kind"] == "belief" and who else "") + n["gloss"],
             "para": pn or n.get("para", ""), "kind": kind, "scheme": scheme, "side": "text", "premises": prems,
             "label": n.get("status", "in"), "who": who, "note": note,
             "group": f"belief:{n.get('who')}" if n["kind"] == "belief" else "world"}
        rules.append(r)
        concl_of.setdefault(tgt, r["id"])
        return r

    sup: dict[str, list[dict]] = {}
    for e in g["edges"]:
        if e["kind"] == "support":
            sup.setdefault(e["tgt"], []).append(e)
    for tgt, es in sup.items():
        if tgt not in nodes:
            continue
        lore = [e for e in es if e["why"] == "lore"]
        conn = [e for e in es if e["why"].startswith("‘")]
        if lore:
            words = ", ".join(sorted({e["why"].split(" ")[0] for e in conn}))
            rule("L", tgt, "strict", "rule application",
                 [premise(e["src"], "fact", "condition") for e in lore],
                 note="By the story's lore." + (f" The text says it with {words}." if words else ""))
        elif conn:
            rule("C", tgt, "defeasible", "cause to effect",
                 [premise(e["src"], "fact" if e["src"].startswith("F:") else "belief", "cause") for e in conn],
                 note=f"Read from the connective {conn[0]['why'].split(' ')[0]} in the text.")
        seen = [e for e in es if e["why"] == "seen"]
        if seen:
            rule("V", tgt, "defeasible", "perception", [premise(e["src"], "seen", "perceived") for e in seen])
        told = [e for e in es if e["why"] == "told"]
        if told:
            rule("T", tgt, "defeasible", "witness testimony",
                 [premise(e["src"], "told", "said", f"said by {names.get(nodes.get(e['src'], {}).get('who', ''), '?')}") for e in told])

    # what each character came to hold, by paragraph and from what (seen, told)
    gained: dict[tuple[str, str], list[tuple[str, str]]] = {}
    for p in report.get("paragraphs", []):
        for b in p.get("delta", {}).get("beliefs", []):
            src = next((x.get("src", "") for x in b.get("explain", []) if x.get("lit") == b["lit"]), "")
            if b.get("change") == "gained":
                gained.setdefault((b["who"], p["name"]), []).append((b["lit"], src))

    def grounds(who: str, tgt: str, pn: str) -> list[dict]:
        """What `who` came to hold from seeing or being told earlier in paragraph `pn`."""
        _, at = tok(nodes[tgt])
        out = []
        for lit, src in gained.get((who, pn), []):
            nid = f"B:{who}:{lit}"
            if nid == tgt or nid not in nodes or not (src == "seen" or src.startswith("told")):
                continue
            if tok(nodes[nid]) [1] < at:
                out.append(premise(nid, "belief", "observed", "held then"))
        return out

    # the character's own inferences (Minds: src inferred), by lore when the lore concludes them
    lore_rules = spec.get("lore", [])
    for p in report.get("paragraphs", []):
        for b in p.get("delta", {}).get("beliefs", []):
            if b.get("change") != "gained" or not any(x.get("src") == "inferred" and x.get("lit") == b["lit"] for x in b.get("explain", [])):
                continue
            tgt = f"B:{b['who']}:{b['lit']}"
            if tgt not in nodes or tgt in concl_of:
                continue
            who = names.get(b["who"], b["who"])
            lr = next((x for x in lore_rules if x.get("then") == b["lit"]), None)
            if lr:
                prems = []
                for lit in lr.get("if", []):
                    nid = f"B:{b['who']}:{lit}" if f"B:{b['who']}:{lit}" in nodes else f"F:{lit}"
                    prems.append(premise(nid, "belief" if nid.startswith("B:") else "fact", "condition"))
                rule("L", tgt, "strict", "rule application", prems, note=f"{who} draws it from the story's lore.")
                continue
            prems = grounds(b["who"], tgt, p["name"])
            if prems:
                note = (f"The reading records that {who} infers it, not from what: its grounds here are what {who} "
                        "came to hold earlier in the paragraph. No alternative is recorded, so the rival "
                        "explanation is unstated.")
            else:
                prems = [{"t": f"G:{tgt}", "tag": "authors", "tagLabel": "no grounds recorded", "quote": "",
                          "gloss": f"what {who} has to go on in ¶{p['name']}", "para": p["name"], "sub": None, "role": "observed"}]
                note = (f"The reading records that {who} infers it but nothing it is drawn from. "
                        "No alternative is recorded, so the rival explanation is unstated.")
            rule("I", tgt, "defeasible", "abduction (best explanation)", prems, note=note)
    for r in rules:
        for p in r["premises"]:
            p["sub"] = concl_of.get(p["t"]) if p["t"] != r["concl"] else None

    attacks = []
    for e in g["edges"]:
        if e["kind"] != "attack" or e["src"] not in nodes or e["tgt"] not in nodes:
            continue
        for end in (e["src"], e["tgt"]):
            if end not in concl_of:
                n = nodes[end]
                if n["kind"] == "fact":
                    rule("W", end, "strict", "deduction", [], note="The story asserts it.")
                else:
                    r = rule("A", end, "defeasible", "abduction (best explanation)",
                             [{"t": f"G:{end}", "tag": "authors", "tagLabel": "no grounds recorded", "quote": "",
                               "gloss": f"what {names.get(n.get('who', ''), 'they')} has to go on", "para": n.get("para", ""),
                               "sub": None, "role": "observed"}],
                             note="A belief the reading gives no grounds for.")
        attacks.append({"src": concl_of[e["src"]], "tgt": concl_of[e["tgt"]], "how": "rebut", "on": None,
                        "quote": e["why"], "ok": True})
    return fan_in(rules), attacks


# ------------------------------------------------------------------ a power system's moves

def _power_rules(power: dict, min_checks: int = 3) -> tuple[list[dict], list[dict]]:
    """Moves with at least `min_checks` preconditions (the rest are bookkeeping:
    one check, e.g. the book is open) and every counterfactual, each a rule
    application with its checks as conditions. A move with more than
    MAX_FAN_IN checks rests on one sub-rule per kind of check (status,
    possession, ...). A check that fails is undermined by the module's reason
    it fails, so the move or counterfactual is OUT."""
    sysname = {"nen": "Nen", "magic": "Magic", "deathnote": "the Death Note"}.get(power.get("system", ""), power.get("system", "power"))
    rules: list[dict] = []
    attacks: list[dict] = []
    # a move's checks, grouped by what they are about (each group a sub-rule when there are too many)
    CLUSTER = {"status": "user", "possession": "user", "support": "user", "body": "means", "resource": "means"}
    WORDS = {"user": "the user can work the ability (alive, not in Zetsu, has it, has what it needs)",
             "means": "the hands and the aura it needs are free", "target": "the target is in reach and the ability's limits allow it"}

    def prem(c: dict, para: str, owner: str) -> dict:
        p = {"t": f"{owner}:{c['id']}", "tag": "check" if c["pass"] else "hedge",
             "tagLabel": c.get("kind", "rule") if c["pass"] else f"{c.get('kind', 'rule')}, supposed",
             "quote": "", "gloss": c["label"], "para": para, "sub": None, "role": "condition"}
        return p if c["pass"] else {**p, "fail": c["why"]}

    def build(rid: str, concl: str, gloss: str, para: str, checks: list[dict], **kw) -> None:
        ps = [prem(c, para, rid) for c in checks]
        top = ps
        if len(ps) > MAX_FAN_IN:
            by: dict[str, list[dict]] = {}
            for c, p in zip(checks, ps):
                by.setdefault(CLUSTER.get(c.get("kind", "rule"), "target"), []).append(p)
            top = []
            for k, (cl, group) in enumerate(by.items()):
                if len(group) == 1:
                    top.append(group[0])
                    continue
                sid = f"{rid}.{k + 1}"
                rules.append({"id": sid, "concl": f"{concl}#{cl}", "quote": "", "gloss": WORDS[cl],
                              "para": para, "kind": "strict", "scheme": "rule application", "side": kw["side"],
                              "premises": group, "label": "in", "group": kw["group"],
                              "note": f"Checks of {rid}, grouped (a rule takes at most {MAX_FAN_IN} premises)."})
                fails = [p["fail"] for p in group if p.get("fail")]
                top.append({"t": f"{concl}#{cl}", "tag": "check", "tagLabel": cl, "quote": "",
                            "gloss": WORDS[cl], "para": para, "sub": sid, "role": "condition",
                            **({"fail": "; ".join(fails)} if fails else {})})
        rules.append({"id": rid, "concl": concl, "quote": "", "gloss": gloss, "para": para, "kind": "strict",
                      "scheme": "rule application", "premises": top, **kw})
        for c, p in zip(checks, ps):
            if c["pass"]:
                continue
            fid = f"{rid}-not-{c['id']}"
            rules.append({"id": fid, "concl": f"!{p['t']}", "quote": "", "gloss": f"not: {c['label']}", "para": para,
                          "kind": "strict", "scheme": "rule application", "side": "text", "label": "in", "group": kw["group"],
                          "premises": [{"t": f"why:{p['t']}", "tag": "check", "tagLabel": "the module", "quote": "",
                                        "gloss": c["why"], "para": para, "sub": None, "role": "condition"}],
                          "note": f"The {sysname} module's check {c['id']} fails."})
            owner = next(r["id"] for r in rules if any(q is p for q in r["premises"]))
            attacks.append({"src": fid, "tgt": owner, "how": "undermine", "on": p["t"], "quote": c["why"]})

    for m in power.get("moves", []):
        if len(m.get("checks", [])) < min_checks:
            continue
        build(f"N{m['i'] + 1}", f"move:{m['i']}", m["text"], m.get("para", ""), m["checks"], side="text",
              label="in" if m["ok"] else "out", group="power", note=(f"{sysname}: {m['kind']}." + ("" if m["ok"] else f" Refused: {m.get('why', '')}")))
    for k, cf in enumerate(power.get("counterfactuals", [])):
        build(f"X{k + 1}", f"cf:{cf['id']}", cf["label"], cf.get("para", ""), cf.get("checks", []), side="opponent",
              label="out", group="counterfactual",
              note=f"{sysname}: counterfactual. {cf.get('change', '')}. Proved: {cf.get('theorem', '')}".strip(". "))
    return fan_in(rules), attacks


def story_doc(name: str, report: dict, spec: dict, power: dict | None) -> dict:
    """The Rules view's document for a story: its paragraphs and its rules."""
    if report.get("error"):
        return {"id": f"story:{name}", "title": name, "error": report["error"], "paragraphs": [], "rules": package([], [])}
    rules, attacks = _story_rules(report, spec)
    groups = [{"id": f"belief:{c['id']}", "title": f"{c['name']}'s beliefs"} for c in report.get("characters", [])]
    groups.append({"id": "world", "title": "The story's facts and lore"})
    if power and not power.get("error"):
        prs, pas = _power_rules(power)
        rules += prs
        attacks += pas
        groups += [{"id": "power", "title": f"{power.get('title', 'The power system')}: moves and their preconditions"},
                   {"id": "counterfactual", "title": "Counterfactuals: runs the module proves fail"}]
    return {"id": f"story:{name}", "title": report.get("title", name), "kind": "story",
            "paragraphs": [{"name": p["name"], "text": p["text"]} for p in report.get("paragraphs", [])],
            "rules": package(rules, attacks, groups=groups)}


# ------------------------------------------------------------------ Death Note (from the Lean source)

CK = {
    "kira": "{0} is Kira", "isL": "{0} is L",
    "kantoOnly": "the Tailor broadcast went out in the Kanto region only",
    "kiraInKanto": "Kira is in the Kanto region",
    "onlyShownFaces": "only criminals whose faces were shown have died",
    "needsFace": "Kira needs a face to kill",
    "misnamedLive": "criminals reported under a wrong name, or none, have lived",
    "needsName": "Kira needs a name to kill",
    "schoolHours": "the deaths fall in a student's free hours",
    "kiraStudent": "Kira is a student",
    "toldOnlyPolice": "L told the student theory to the task force and nobody else",
    "patternChanged": "the pattern of the killings changed after the briefing",
    "policeLeak": "Kira has access to the police investigation",
    "prisonersActed": "prisoners did what they could not have meant to before they died",
    "controlsActions": "Kira can control the victims' actions before death",
    "rayeTailedYagami": "Raye Penber's assignments included the Yagami household",
    "agentsAllDied": "all the FBI agents in Japan died",
    "nearTailedFamily": "Kira is close to a family the FBI tailed",
    "noOtherSuspect": "nobody but Light could fit",
    "cleanOnCamera": "Light is clean on the cameras",
    "watched": "Light is watched",
    "pagesOrdinary": "the pages are ordinary paper",
    "rayeWillLive": "Raye will live",
    "lightHelpsL": "Light is helping L",
    "hijackerSawSomething": "the hijacker saw something nobody else could",
    "rayeShowedId": "Raye showed Light his FBI badge",
    "kiraOnBus": "Kira was on the bus",
    "makiNoDeath": "writing “Shoko Maki” killed nobody",
    "lSpokeAfter": "L spoke on air after the man on air died",
    "ryugaIsIdol": "Hideki Ryuga is an idol's name",
    "lRevealed": "L has told Light who he is",
    "lDeathPointsToLight": "if L dies now, it points to Light",
}
CH = {"light": "Light", "l": "L", "ryuk": "Ryuk", "raye": "Raye Penber", "naomi": "Naomi Misora",
      "soichiro": "Soichiro Yagami", "tailor": "the man on air", "osoreda": "Kiichiro Osoreda",
      "agents": "the FBI agents", "ryuga": "the idol Hideki Ryuga", "reader": "the reader"}
NM = {"maki": "Shoko Maki", "ryugaN": "Hideki Ryuga", "lAlias": "L", "ryuzaki": "Ryuzaki"}
FALSE_CK = {"noOtherSuspect", "pagesOrdinary", "rayeWillLive", "lightHelpsL"}
# body literals that eliminate the alternatives (an abduction's rival slot)
RIVAL = {"noOtherSuspect"}


def _lit_words_neg(words: str) -> str:
    return words[5:] if words.startswith("not: ") else f"not: {words}"


def _groups(s: str) -> list[str]:
    """Split `s` into top-level tokens and parenthesised groups."""
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch == "(":
            if depth == 0 and cur.strip():
                out += cur.split()
                cur = ""
            depth += 1
            cur += ch
        elif ch == ")":
            depth -= 1
            cur += ch
            if depth == 0:
                out.append(cur.strip())
                cur = ""
        elif ch == "," and depth == 0:
            cur += " "
        else:
            cur += ch
    if cur.strip():
        out += cur.split()
    return out


def _items(s: str) -> list[str]:
    """Split a Lean list body at its top-level commas."""
    out, depth, cur = [], 0, ""
    for ch in s:
        depth += ch == "("
        depth -= ch == ")"
        if ch == "," and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    return out + ([cur.strip()] if cur.strip() else [])


def _inner(g: str) -> str:
    return g[1:-1].strip() if g.startswith("(") and g.endswith(")") else g


def _lit(g: str) -> tuple[str, bool, str]:
    """A literal (`yes .x`, `no (.isL tailor)`, `(nf (.dead tailor), true)`): its key, sign, and words."""
    parts = _groups(_inner(g))
    if parts[0] in ("yes", "no"):
        pos, body = parts[0] == "yes", _inner(parts[1])
        bits = body.lstrip(".").split()
        words = CK.get(bits[0], bits[0]).format(*[CH.get(b, b) for b in bits[1:]])
        truth = (bits[0] == "kira" and bits[1:] == ["light"]) or (bits[0] == "isL" and bits[1:] == ["l"]) \
            or (bits[0] not in ("kira", "isL") and bits[0] not in FALSE_CK)
        return f"{'' if pos else '!'}{body}", truth == pos, words if pos else f"not: {words}"
    if parts[0] == "nf":
        fact = _inner(parts[1]).lstrip(".").split()
        pos = parts[2] == "true" if len(parts) > 2 else True
        if fact[0] == "dead":
            words = f"{CH.get(fact[1], fact[1])} is dead"
        elif fact[0] == "nameOf":
            words = f"{NM.get(fact[2], fact[2])} is {CH.get(fact[1], fact[1])}'s real name"
        else:
            words = " ".join(fact)
        return f"{'' if pos else '!'}nf {' '.join(fact)}", True, words if pos else f"not: {words}"
    return g, True, g


def _calls(src: str, head: str) -> list[str]:
    """The balanced argument of every `head (` in `src`."""
    out, i = [], 0
    while (i := src.find(head + " (", i)) >= 0:
        j, depth = i + len(head) + 1, 0
        for k in range(j, len(src)):
            depth += src[k] == "("
            depth -= src[k] == ")"
            if depth == 0:
                out.append(src[j + 1:k])
                break
        i = j
    return out


def deathnote(path: Path = DN_SOURCE) -> dict:
    """The Death Note arc's deductions as rules: one rule per `conclude` (and per
    reader `reveal`, the reader's own derivation), its premises the deduction
    rule's body, each held as a clue (seen, told, or known) or concluded before."""
    src = path.read_text()
    m = re.search(r"instance : Deduction Fact where\s+rules :=\s*\[(.*?)\]\s*\n\s*\n", src, re.S)
    ded = []
    for body in re.findall(r"\{ name := \"(\w+)\", body := \[(.*?)\], head := (.*?) \}", m.group(1) if m else "", re.S):
        name, b, h = body
        ded.append({"name": name, "body": [_lit(x) for x in _items(b)], "head": _lit(h.strip())})
    paras, rules, attacks = [], [], []
    held: dict[str, dict[str, tuple[str, str]]] = {}   # who → lit key → (how, rule id or "")
    concl_of: dict[tuple[str, str], str] = {}
    n = 0
    for pm in re.finditer(r"def p(\d\d) : List E :=\n(.*?)(?=\n\ndef |\n/-)", src, re.S):
        pn, block = pm.group(1), pm.group(2)
        sents = []
        for call in _calls(block, "my"):
            parts = _groups(call)
            ev, who = parts[0].lstrip("."), parts[1]
            key, true, words = _lit(parts[2])
            w = CH.get(who, who)
            if ev == "clue":
                how = parts[3].lstrip(".") if len(parts) > 3 else "seen"
                how = "told" if how.startswith("(") else how
                verb = {"seen": "sees that", "self": "knows that", "told": "is told that"}.get(how, "learns that")
                s = f"{w[0].upper() + w[1:]} {verb} {words}."
                held.setdefault(who, {})[key] = (how, "", s, pn)
            elif ev in ("conclude", "reveal", "suspect"):
                cands = [d for d in ded if d["head"][0] == key]
                have = held.get(who, {})
                d = next((d for d in cands if all(b[0] in have for b in d["body"])), None) \
                    or next((d for d in cands if any(b[0] in have for b in d["body"])), cands[0] if cands else None)
                verb = {"conclude": "concludes that", "reveal": "is shown that", "suspect": f"suspects ({parts[3] if len(parts) > 3 else '?'}%) that"}[ev]
                s = f"{w[0].upper() + w[1:]} {verb} {words}."
                n += 1
                rid = f"D{n}"
                abd = ev != "reveal"
                prems = []
                for b in (d["body"] if d else []):
                    h = have.get(b[0])
                    role = ("rival" if b[0].lstrip("!.").split(" ")[0] in RIVAL else "observed") if abd else "premise"
                    if h is None:
                        prems.append({"t": f"{who}:{b[0]}", "tag": "authors", "tagLabel": "never established", "quote": "",
                                      "gloss": b[2], "para": "", "sub": None, "role": role,
                                      "fail": "nothing in the arc establishes it"})
                    else:
                        tag = {"seen": "seen", "self": "fact", "told": "told", "concluded": "belief"}.get(h[0], "fact")
                        prems.append({"t": f"{who}:{b[0]}", "tag": tag, "tagLabel": {"self": "known", "concluded": "concluded"}.get(h[0]),
                                      "quote": h[2], "para": h[3], "sub": h[1] or None, "role": role})
                missing = [p for p in prems if p.get("fail")]
                rival = any(p["role"] == "rival" for p in prems)
                rules.append({"id": rid, "concl": f"{who}:{key}", "quote": s, "para": pn,
                              "kind": "strict" if ev == "reveal" else "defeasible",
                              "scheme": "abduction (best explanation)" if abd else "deduction",
                              "side": "text", "premises": prems, "who": w,
                              "label": "undec" if missing or ev == "suspect" else "in" if true else "out",
                              "group": "reader" if who == "reader" else f"who:{who}",
                              "thin": [f"premise never established: {p['gloss']}" for p in missing],
                              "note": f"Deduction rule “{d['name'] if d else 'none'}”. " + {
                                  "conclude": "Mystery.conclude: allowed only if derivable from what they hold now; "
                                              "read as an inference to the best explanation of the clues"
                                              + (", the alternatives eliminated." if rival else ", with no alternative eliminated: the rival is unstated."),
                                  "reveal": "Mystery.reveal: fair only if the reader can derive it from what the page has shown.",
                                  "suspect": "Mystery.suspect: a credence below certainty; needs a lead (one premise held)"
                                             + ("." if rival else "; no alternative is eliminated, so the rival is unstated.")}[ev]})
                if ev != "suspect":
                    held.setdefault(who, {})[key] = ("concluded", rid, s, pn)
                    concl_of[(who, key)] = rid
                if not true:
                    n_w = sum(1 for r in rules if r["id"].startswith("W")) + 1
                    rules.append({"id": f"W{n_w}", "concl": f"world:!{key}", "quote": "", "para": pn,
                                  "gloss": f"In the world: {_lit_words_neg(words)}", "kind": "strict", "scheme": "deduction",
                                  "side": "text", "premises": [], "label": "in", "group": "world",
                                  "note": "What the arc's world state says (DeathNoteArc.lean)."})
                    attacks.append({"src": f"W{n_w}", "tgt": rid, "how": "rebut", "quote": "the world says otherwise"})
            else:
                continue
            sents.append(s)
        if sents:
            paras.append({"name": pn, "text": " ".join(sents)})
    who_order = ["l", "naomi", "light", "reader"]
    groups = [{"id": f"who:{w}", "title": f"{CH[w]}'s deductions"} for w in who_order[:3]]
    groups.append({"id": "reader", "title": "The reader's derivations (fair play)"})
    groups.append({"id": "world", "title": "The world, where a deduction is wrong"})
    doc = package(rules, attacks, groups=groups)
    return {"id": "lean:deathnote", "title": "Death Note: Light against L (the arc's deductions)", "kind": "lean",
            "note": "Read from LangLib/World/Examples/DeathNoteArc.lean: the arc has no prose yet, so each paragraph "
                    "is its Mystery moves in words, and the quotes are those words.",
            "paragraphs": paras, "rules": doc}


# ------------------------------------------------------------------ a defeasible theory

def from_dl(theory: dict) -> dict:
    """A ground DL theory {facts: [lit], rules: [{label, kind, body: [lit], head: lit}],
    sup: [[t, s]]} (lit: "a" or "!a") as rules. A defeater for ¬q undercuts each
    rule for q; a rule for q and one for ¬q rebut each other, except where one
    is superior, which then attacks alone."""
    neg = lambda l: l[1:] if l.startswith("!") else "!" + l  # noqa: E731
    rs = theory.get("rules", [])
    sup = {(t, s) for t, s in theory.get("sup", [])}
    concl = {r["head"]: r["label"] for r in rs if r["kind"] != "defeater"}
    facts = set(theory.get("facts", []))
    rules = []
    for r in rs:
        rules.append({"id": r["label"], "concl": r["head"], "quote": "", "gloss": r["head"], "para": "",
                      "kind": "strict" if r["kind"] == "strict" else "defeasible",
                      "scheme": "rule application", "side": "text", "label": "in",
                      "note": {"strict": "A strict rule of the theory.", "defeasible": "A defeasible rule of the theory.",
                               "defeater": "A defeater: it only blocks the rules for the opposite head."}[r["kind"]],
                      "premises": [{"t": b, "tag": "fact" if b in facts else "authors", "quote": "", "gloss": b,
                                    "para": "", "sub": concl.get(b), "role": "condition"} for b in r.get("body", [])]})
    attacks = []
    for a in rs:
        for b in rs:
            if b["kind"] == "defeater" or a["head"] != neg(b["head"]) or b["kind"] == "strict":
                continue
            if (b["label"], a["label"]) in sup:
                continue                      # b is superior: a's attack on b fails
            how = "undercut" if a["kind"] == "defeater" else "rebut"
            attacks.append({"src": a["label"], "tgt": b["label"], "how": how, "quote": ""})
    lab = grounded([r["id"] for r in rules], [(a["src"], a["tgt"]) for a in attacks])
    for r in rules:
        r["label"] = lab[r["id"]]
    propagate(rules)
    return package(fan_in(rules), attacks)
