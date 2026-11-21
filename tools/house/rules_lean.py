"""An argument's rules (`langlib rules <dir>`) as a Lean file the kernel re-checks.

    rules_lean.py <dir | rules.json> <Namespace> [-o out.lean]

Reads the rules JSON from `langlib rules <dir>`, or checks a rules document
built elsewhere (a story adapter's) with `langlib rules-json <file>` (both
through studio/procs.py),
names every term and rule as a constructor of one inductive, and states as
theorems, each proved by `decide +kernel` over World/Rules:

- `ok`: every attack is well formed (ASPIC+'s restrictions) and every pressed
  critical question is open;
- `grounded`: the grounded labelling under the text's own attacks;
- `sceptic`: the labelling with every pressed critical question as an attacker;
- `bare`: the rules resting on the authors' word alone;
- `bareLeaves`: the premises nothing in the text supports;
- `thin`: the defeasible links with thin support, and why;
- `shaped`: every premise fills a slot its scheme allows, and no rule has
  too many premises;
- `enthymemes`: the required slots no premise fills (what the text leaves
  unstated).

The values stated are the CLI's; the kernel proving them is the check that
the CLI and World/Rules agree. Run the file with `lake env lean` (via
studio/procs.py).
"""
import json, re, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "studio"))
import procs  # noqa: E402

SCHEME = {"deduction": "deductive", "definition": "definitional", "example to generalisation": "exampleToGen",
          "practical reasoning": "practical", "abduction (best explanation)": "abduction",
          "track record → capability": "trackRecord", "expert opinion": "expertOpinion",
          "cause to effect": "causeToEffect", "analogy": "analogy",
          "requirement matches capability": "requirement", "counterexample": "counterexample",
          "perception": "perception", "witness testimony": "testimony", "sign": "sign",
          "rule application": "ruleApp", "unread": "unread"}
STORY_TAG = {"seen": "fact", "check": "fact", "told": "citation", "belief": "hedge"}
TAG = {"example": "«example»"}
THIN = [(re.compile(r"a generalisation from (\d+) example"), lambda m: f".fewExamples {m[1]}"),
        (re.compile(r"rests on a promise"), lambda m: ".onPromise"),
        (re.compile(r"authors' word"), lambda m: ".authorsWord")]


def tag(t):
    """A premise's tag as a `Tag` constructor (story tags as RulesView's `storyTag`)."""
    t = STORY_TAG.get(t, t)
    t = t if t in ("fact", "example", "citation", "authors", "hedge", "promise") else "authors"
    return TAG.get(t, t)


def ident(s):
    s = re.sub(r"\W", "_", s)
    return s if s[:1].isalpha() else "t" + s


def lean(rules, ns):
    rs = rules["rules"]
    names = []
    for r in rs:
        names += [r["id"], r["concl"]] + [p["t"] for p in r["premises"]]
    for a in rules["attacks"]:
        if a.get("on"):
            names.append(a["on"])
    names = list(dict.fromkeys(ident(n) for n in names))
    c = lambda n: f".{ident(n)}"
    lst = lambda xs: "[" + ", ".join(xs) + "]"
    out = ["import LangLib.World.Rules", "", f"namespace {ns}", "open LangLib.World.Argument", "",
           "inductive Tm", *[f"  | {n}" for n in names], "  deriving DecidableEq, Repr", "", "def rs : List (Rule Tm) := ["]
    body = []
    for r in rs:
        prem = lst(f"({c(p['t'])}, .{tag(p['tag'])})" for p in r["premises"])
        slots = lst(f"({c(p['t'])}, .{p['role']})" for p in r["premises"] if p.get("role"))
        ans = [str(q["i"]) for q in r["cqs"] if q["status"] == "answered"]
        pr = [str(q["i"]) for q in r["cqs"] if q["status"] == "pressed"]
        body.append(f"  {{ id := {c(r['id'])}, concl := {c(r['concl'])}, premises := {prem},\n"
                    f"    kind := .{'strict' if r['kind'] == 'strict' else 'defeasible'}, scheme := .{SCHEME.get(r['scheme'], 'unread')}, side := .{r['side']},\n"
                    f"    answered := {lst(ans)}, pressed := {lst(pr)}, slots := {slots} }}")
    out += [",\n".join(body), "]", ""]
    out.append("def as : List (RAttack Tm) := " + lst(
        f"{{ src := {c(a['src'])}, tgt := {c(a['tgt'])}, how := .{a['how']}"
        + (f", on := some {c(a['on'])}" if a.get("on") else "") + " }" for a in rules["attacks"]))
    labs = lambda k: lst(f"({c(r['id'])}, .«{r[k]}»)" for r in rs)

    def thin(ws):
        out = []
        for w in ws:
            for rx, f in THIN:
                m = rx.search(w)
                if m:
                    out.append(f(m))
        return lst(out)

    out += ["", "theorem ok : RulesOk rs as := by decide +kernel",
            f"theorem grounded : labels rs as = {labs('label')} := by decide +kernel",
            f"theorem sceptic : scepticLabels rs as = {labs('sceptic')} := by decide +kernel",
            f"theorem bare : bareRules rs = {lst(c(i) for i in rules['bare'])} := by decide +kernel",
            f"theorem bareLeaves' : bareLeaves rs = {lst(c(i) for i in rules['bareLeaves'])} := by decide +kernel",
            f"theorem thin' : thinRules rs = {lst(f'({c(t['id'])}, {thin(t['why'])})' for t in rules['thin'])} := by decide +kernel",
            f"theorem shaped : {'' if rules.get('shaped') else '¬ '}Shaped rs := by decide +kernel",
            f"theorem enthymemes : enthymemeRules rs = {lst(f'({c(e['id'])}, {lst('.' + x for x in e['slots'])})' for e in rules.get('enthymemes', []))} := by decide +kernel",
            "", f"end {ns}", ""]
    return "\n".join(out)


if __name__ == "__main__":
    d, ns = sys.argv[1], sys.argv[2]
    r = procs.run(procs.langlib_argv("rules-json" if d.endswith(".json") else "rules", d))
    if r.returncode:
        sys.exit(r.stderr)
    src = lean(json.loads(r.stdout), ns)
    if "-o" in sys.argv:
        Path(sys.argv[sys.argv.index("-o") + 1]).write_text(src)
    else:
        print(src)
