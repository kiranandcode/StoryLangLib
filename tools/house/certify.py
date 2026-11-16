"""Certify a text against Kiran's house style with langlib.

    certify.py <dir> [--paper] [--title T]

<dir>/paragraphs/NN.txt holds paragraph NN; NN.sx (tools/house/sx.py notation)
or NN.json its annotation. <dir>/lexicon.local.json adds the text's own word
classes (nominal, animate, registers) to tools/house/base-lexicon.json; the
merged file is written to <dir>/lexicon.json. <dir>/contrasts.json may list
not-X-but-Y candidates that deny something the text put forward, as
{"P:I": "what was put forward, and where"}.

Runs `langlib check` on every paragraph, then `langlib house` and `langlib
academic`, and writes <dir>/report.md and report.json. The text is certified
when every paragraph checks, every word class the audit asks about is
decided, every house rule holds, there are no em-dashes,
dramatic colons or rhetorical questions, every not-X-but-Y candidate is
justified in contrasts.json, and (with --paper) the academic `kiran` and
`annotated` styles hold. Exit status 0 when certified.

The audit lists words whose class the rules need and nobody decided: nouns
that look like nominalisations, verbs (animate or not), spellings that look
American. Give each an entry in lexicon.local.json ({"cls": ["nominal"]},
{"cls": ["animate"]}, or {"reg": "neutral"} for "decided, no class").
"""
import json, os, re, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
LANGLIB = ROOT / ".lake/build/bin/langlib"
sys.path.insert(0, str(HERE))
from sx import compile_sx  # noqa: E402

HOUSE_FLAG = {  # rule name -> key in house "flagged"
    "characters: few agentless passives": "agentless",
    "actions: few hidden in nouns": "hiddenAction",
    "no inanimate actors": "inanimate",
    "few noun stacks": "nounStacks",
    "point first": "buried",
    "no stacked asides": "stacked",
    "no non-sequitur stacks": "nonSequiturs",
    "no slop emphasis": "slopEmphasis",
    "no throat-clearing": "throat",
    "no understated inflation": "inflation",
    "no tricolon with semicolons": "tricolons",
    "no deferred assertion": "pseudoClefts",
    "no emphatic cleft": "itClefts",
    "few observation-and-response joins": "andJoins",
    "no mechanical tetracolon": "tetracola",
    "no sentence-initial conjunctions": "initialConj",
    "no buzz words": "buzz",
    "no empty intensifiers": "intensifiers",
    "British spelling": "usSpelling",
    "no appositive-trailing cadence": "trailingCadence",
    "no dramatic terminal sentences": "dramaticTerminal",
    "no summarising pivots": "summarisingPivots",
    "no summary closers": "summaryClosers",
    "no bare pivot bridges": "barePivots",
    "no spurious contrasts": "spuriousContrasts",
    "no bare relative clauses": "bareRelatives",
    "no not-X-dash-Y": "negDashes",
    "no abstract significance": "abstractSig",
}
NOMINAL = re.compile(r"(tion|sion|ment|ance|ence|ancy|ency|ity|ure|al|ing|sis|age)s?$")
# -ize/-yze forms; -or, -er and -og spellings are listed in the base lexicon's `us` class
AMERICAN = re.compile(r"(iz(e|es|ed|ing|ation|ations)|yz(e|es|ed|ing))$")
NOT_AMERICAN = {"size", "sizes", "sized", "prize", "prizes", "seize", "seized", "citizen", "capsize"}


def run(argv):
    p = subprocess.run(["nice", "-n", "10", str(LANGLIB)] + argv, capture_output=True, text=True, timeout=300)
    return p.returncode, p.stdout, p.stderr


def leaves(t):
    return [t] if "w" in t else [x for k in t["k"] for x in leaves(k)]


def text_of(t):
    out = ""
    for l in leaves(t):
        w = l["w"]
        if out and not (w in ",.;:!?)'’”" or out.endswith(("(", "“", "‘"))):
            out += " "
        out += w
    return out


def merge_lexicon(d, words):
    base = json.load(open(HERE / "base-lexicon.json"))
    lex = {}
    for c, ks in base["cls"].items():
        for k in ks:
            lex.setdefault(k, {}).setdefault("cls", []).append(c)
    for r, ks in base["rel"].items():
        for k in ks:
            lex.setdefault(k, {})["rel"] = r
    for w in words:  # -ing forms are never passive participles
        if w.endswith("ing") and len(w) > 4:
            e = lex.setdefault(w, {})
            if "ing" not in e.get("cls", []):
                e.setdefault("cls", []).append("ing")
    local = {}
    lp = d / "lexicon.local.json"
    if lp.exists():
        local = json.load(open(lp))
    overrides = []
    for k, v in local.items():
        if k.startswith("_"):
            continue
        v = {"reg": v} if isinstance(v, str) else v
        e = lex.setdefault(k, {})
        if "cls" in v:
            dropped = [c for c in e.get("cls", []) if c not in v["cls"] and c != "ing"]
            if dropped:
                overrides.append(f"{k}: drops {', '.join(dropped)}")
            e["cls"] = sorted(set(v["cls"]) | ({"ing"} & set(e.get("cls", []))))
        for f in ("reg", "rel"):
            if f in v:
                e[f] = v[f]
    json.dump(lex, open(d / "lexicon.json", "w"), indent=1, sort_keys=True, ensure_ascii=False)
    return lex, local, overrides


def audit(docs, lex, local):
    def known(w):
        return w in lex or w in local
    nom, verbs, us, noform = set(), set(), set(), []
    for n, doc in docs:
        for si, s in enumerate(doc["sentences"], 1):
            for l in leaves(s):
                w, lem = l["w"].lower(), (l.get("l") or l["w"]).lower()
                if l["p"] == "NOUN" and NOMINAL.search(w) and not (known(w) or known(lem)):
                    nom.add(w)
                if l["p"] == "VERB":
                    if not (known(w) or known(lem)):
                        verbs.add(lem)
                    if "VerbForm" not in l.get("f", {}):
                        noform.append(f"{n}:{si} {l['w']}")
                if l["p"] not in ("PROPN", "PUNCT") and AMERICAN.search(w) and w not in NOT_AMERICAN and not known(w):
                    us.add(w)
    return {"nouns that may hide an action (nominal?)": sorted(nom),
            "verbs (animate: only a person does it?)": sorted(verbs),
            "spellings to confirm British": sorted(us),
            "verbs without VerbForm": noform}


def main():
    args = sys.argv[1:]
    if not args:
        sys.exit(__doc__)
    d = Path(args[0]).resolve()
    paper = "--paper" in args
    title = args[args.index("--title") + 1] if "--title" in args else d.name
    pdir = d / "paragraphs"
    nums = sorted({p.name[:2] for p in pdir.iterdir() if re.match(r"\d\d\.txt$", p.name)})

    docs, problems = [], []
    for n in nums:
        sxp, jp = pdir / f"{n}.sx", pdir / f"{n}.json"
        if sxp.exists():
            json.dump(compile_sx(sxp.read_text(), str(sxp)), open(jp, "w"), ensure_ascii=False)
        if not jp.exists():
            problems.append(f"paragraph {n}: no annotation")
            continue
        rc, out, err = run(["check", str(pdir / f"{n}.txt"), str(jp)])
        try:
            r = json.loads(out)
        except json.JSONDecodeError:
            r = {"ok": False, "error": (out + err)[:2000]}
        if not r.get("ok"):
            keep = {k: r[k] for k in ("parseError", "error", "edits", "badLeaves", "refIssues") if r.get(k)}
            problems.append(f"paragraph {n}: langlib check fails: {json.dumps(keep)[:1500]}")
        docs.append((int(n), json.load(open(jp))))

    words = {l["w"].lower() for _, doc in docs for s in doc["sentences"] for l in leaves(s)}
    lex, local, overrides = merge_lexicon(d, words)
    sent = {}
    for n, doc in docs:
        src, pos = (pdir / f"{n:02d}.txt").read_text(), 0
        for i, s in enumerate(doc["sentences"], 1):
            ws = [l["w"] for l in leaves(s)]
            start = src.find(ws[0], pos) if ws else -1
            for w in ws:
                k = src.find(w, pos)
                if k < 0:
                    break
                pos = k + len(w)
            sent[(n, i)] = src[start:pos].strip() if start >= 0 else text_of(s)

    report = {"title": title, "paragraphs": len(nums), "sentences": len(sent),
              "annotation": problems, "lexiconOverrides": overrides, "rules": [], "audit": audit(docs, lex, local)}
    lines = [f"# Certification: {title}", ""]
    if problems:
        lines += ["## Annotation fails `langlib check`", ""] + [f"- {p}" for p in problems]
        report["certified"] = False
        write(d, report, lines)
        sys.exit(1)

    rc, hout, herr = run(["house", str(d)])
    house = json.loads(hout) if rc == 0 else None
    rc, aout, aerr = run(["academic", str(d)])
    acad = json.loads(aout) if rc == 0 else None
    if house is None or acad is None:
        sys.exit(f"langlib failed:\n{herr}\n{aerr}")

    contrasts = {}
    if (d / "contrasts.json").exists():
        contrasts = json.load(open(d / "contrasts.json"))

    def where(ps):
        return [{"at": f"{p}:{i}", "sentence": sent.get((p, i), "?")} for p, i in ps]

    rules = []
    for st in house["styles"]:
        for r in st["rules"]:
            key = HOUSE_FLAG.get(r["name"])
            rules.append({"style": st["name"], "name": r["name"], "rule": r["rule"], "holds": r["holds"],
                          "at": where(house["flagged"].get(key, []) if key else [])})
    af, afl = acad["features"], acad["flagged"]
    sty = {s["name"]: s for s in acad["styles"]}
    dashes = af.get("dashes", 0)
    rules.append({"style": "llmisms", "name": "no em-dashes", "rule": "dashes ≤ 0", "holds": dashes == 0,
                  "at": where(afl.get("dramaticDashes", []) + afl.get("definingDashes", []))})
    for nm, key in (("no dramatic colons", "dramaticColons"),):
        rules.append({"style": "llmisms", "name": nm, "rule": f"{key} ≤ 0", "holds": not afl.get(key),
                      "at": where(afl.get(key, []))})
    rhet = af.get("rhetorical", 0)
    rules.append({"style": "llmisms", "name": "no rhetorical questions", "rule": "rhetorical ≤ 0",
                  "holds": rhet == 0, "at": where(afl.get("questions", [])) if rhet else []})
    turns = afl.get("negTurns", [])
    unjust = [(p, i) for p, i in turns if f"{p}:{i}" not in contrasts]
    rules.append({"style": "llmisms", "name": "no not-X-but-Y (unless it denies what the text put forward)",
                  "rule": "negTurns not in contrasts.json ≤ 0", "holds": not unjust, "at": where(unjust),
                  "justified": {k: v for k, v in contrasts.items()}})
    if paper:
        for nm in ("kiran", "annotated"):
            for r in next((s for s in acad["styles"] if s["name"] == nm), {"rules": []})["rules"]:
                rules.append({"style": f"academic/{nm}", "name": r["name"], "rule": r["rule"], "holds": r["holds"],
                              "at": []})
    undecided = [f"{k}: {', '.join(v)}" for k, v in report["audit"].items() if v]
    rules.append({"style": "annotation", "name": "every word class the rules read is decided",
                  "rule": "audit items ≤ 0", "holds": not undecided,
                  "at": [{"at": "lexicon", "sentence": u} for u in undecided]})
    report["rules"] = rules
    report["certified"] = all(r["holds"] for r in rules)
    report["counts"] = {k: house["features"][k] for k in ("sents", "clauses", "agentless", "bareAsides")}
    report["counts"]["words"] = sum(len([l for l in leaves(s) if l["p"] not in ("PUNCT", "SYM")])
                                    for _, doc in docs for s in doc["sentences"])

    passed = [r for r in rules if r["holds"]]
    failed = [r for r in rules if not r["holds"]]
    lines += [f"{len(nums)} paragraphs, {len(sent)} sentences, {report['counts']['words']} words. "
              f"Every paragraph's annotation passes `langlib check`.", "",
              f"**{'CERTIFIED' if report['certified'] else 'NOT CERTIFIED'}**: "
              f"{len(passed)}/{len(rules)} rules hold.", ""]
    if failed:
        lines += ["## Failing", ""]
        for r in failed:
            lines.append(f"- **{r['name']}** ({r['style']}, `{r['rule']}`)")
            for a in r["at"]:
                lines.append(f"  - {a['at']}: {a['sentence']}")
        lines.append("")
    within = [r for r in passed if r["at"]]
    if within:
        lines += ["## Within limits, still flagged", ""]
        for r in within:
            lines.append(f"- {r['name']} (`{r['rule']}`): {len(r['at'])} at " + ", ".join(a["at"] for a in r["at"]))
        lines.append("")
    lines += ["## Passing", "", ", ".join(r["name"] for r in passed), ""]
    if contrasts:
        lines += ["## Contrasts kept (deny what the text put forward)", ""] + \
                 [f"- {k}: {sent.get(tuple(map(int, k.split(':'))), '?')} ({v})" for k, v in contrasts.items()] + [""]
    if overrides:
        lines += ["## Base lexicon overridden", ""] + [f"- {o}" for o in overrides] + [""]
    write(d, report, lines)
    print("\n".join(lines))
    sys.exit(0 if report["certified"] else 1)


def write(d, report, lines):
    json.dump(report, open(d / "report.json", "w"), indent=1, ensure_ascii=False)
    (d / "report.md").write_text("\n".join(lines) + "\n")
    if not report.get("rules"):
        print("\n".join(lines))


if __name__ == "__main__":
    main()
