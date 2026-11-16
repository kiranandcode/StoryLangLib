"""An essay's argument and style, proved by decide +kernel (docs/essay-analysis.md).

    python3 tools/essay/prove.py stories/<essay> <Namespace>

1. argument_gen.py writes paragraphs/NN.argument.json and Argument.lean from argument.py;
   Lean evaluates it (validity, gaps, antitheses, contrasts, deferred obligations) and the
   verdict is written to argument-verdict.json; Argument.lean is regenerated with theorems
   for exactly what was found.
2. `langlib academic`, `house` and `style` (records and verdicts) are folded into Paper.lean
   beside the argument, so the LLM-ism verdict takes its antithesis count from the argument
   world; style-report.json keeps the JSON.

Every langlib and Lean call goes through studio/procs.py (its lock, nice and timeout).
A public, procs-only version of stories/private-papers/tools/{argument_prove,style_prove}.py.
"""
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "studio"))
import procs  # noqa: E402

d, ns = Path(sys.argv[1]), sys.argv[2]
GEN = ROOT / "tools/essay/argument_gen.py"


def lean(path: Path) -> procs.Result:
    return procs.run(["lake", "env", "lean", str(path.resolve())], timeout=3000)


def cli(*a: str) -> str:
    r = procs.run(procs.langlib_argv(*a), timeout=600)
    if r.returncode:
        raise SystemExit(f"langlib {' '.join(a)} failed: {r.stderr[-2000:]}")
    return r.stdout


# ---- 1. the argument
subprocess.run(["python3", str(GEN), str(d), ns], check=True)
r = lean(d / "Argument.lean")
out = r.stdout
probes = []
while out.startswith("some"):
    line, out = out.split("\n", 1)
    probes.append(line)
print("lore probes:", probes)
line, out = out.split("\n", 1)
anti = re.findall(r'"(\w+)"', line.split("], [")[0])
contr = re.findall(r'"(\w+)"', line.split("], [")[1]) if "], [" in line else []
if not out.startswith("none"):
    raise SystemExit("the argument is not valid; first failure:\n" + out[:1500])
gaps = json.loads(out[out.index("["):out.index("]") + 1])
rest = out[out.index("]") + 1:]
deferred = re.findall(r'\("(\w+)", (\d+)\)', rest)
verdict = {"gaps": gaps, "deferred": deferred, "antitheses": anti, "contrasts": contr}
json.dump(verdict, open(d / "argument-verdict.json", "w"), indent=1)
subprocess.run(["python3", str(GEN), str(d), ns, "--theorems", str(d / "argument-verdict.json")], check=True)
r = lean(d / "Argument.lean")
ok = r.returncode == 0 and not r.stdout.strip()
print(ns, "argument", "proved" if ok else "FAILED", r.stdout[-2000:], r.stderr[-800:])
if not ok:
    raise SystemExit(1)

# ---- 2. style, folded in beside the argument
acad = json.loads(cli("academic", str(d)))
core = json.loads(cli("style", str(d)))
house = json.loads(cli("house", str(d)))
arecs = cli("academic", str(d), "--lean", "asents")
crecs = cli("style", str(d), "--lean", "sents")
hrecs = cli("house", str(d), "--lean", "hsents")
hf = house["features"]
hfails = {s["name"]: s["failing"] for s in house["styles"]}
af = dict(acad["features"])
af["antithesis"] = len(anti)
fails = {s["name"]: s["failing"] for s in acad["styles"] + core["styles"]}
if af["antithesis"] and "no not-X-but-Y" not in fails["llmism-free"]:
    order = ["no dramatic dashes", "no dramatic colons", "no not-X-but-Y", "no rhetorical questions"]
    fails["llmism-free"] = [x for x in order if x in fails["llmism-free"] or x == "no not-X-but-Y"]
skip = {"dashes", "unanswered", "contentWords"}
afields = [k for k in af if k not in skip]
hfields = [k for k in hf if k not in skip]


def L(xs):
    return "[" + ", ".join(json.dumps(x, ensure_ascii=False) for x in xs) + "]"


arg = (d / "Argument.lean").read_text()
arg = arg.replace("import LangLib.World.Argument",
                  "import LangLib.World.Argument\nimport LangLib.Style.Pratchett\nimport LangLib.Style.Roof\n"
                  "import LangLib.Style.Ao3\nimport LangLib.Style.House")
arg = arg[:arg.rindex(f"end Essays.{ns}")]
src = arg + f'''
/-! ## Style: records printed by `langlib academic`/`style`/`house --lean` from the checked annotations -/
namespace Style
open LangLib.Style LangLib.Style.Academic

{arecs}
{crecs}
/-- The trees' features, with the antitheses the argument world finds. -/
def af : AFeatures := {{ AFeatures.ofSents asentsLore asents with antithesis := (antitheses (run w0 moves)).length }}
def cf : Features := Features.ofSents sents

theorem academic_features : af = {{ {", ".join(f"{k} := {af[k]}" for k in afields)} }} := by decide +kernel
theorem kiran_verdict : kiran.failing af = {L(fails["kiran"])} := by decide +kernel
theorem llmism_verdict : llmismFree.failing af = {L(fails["llmism-free"])} := by decide +kernel
theorem dashes_verdict : noDashes.failing af = {L(fails["no-em-dashes"])} := by decide +kernel
theorem annotated_verdict : annotated.failing af = {L(fails["annotated"])} := by decide +kernel
theorem grounded_verdict : grounded.failing af = {L(fails["grounded"])} := by decide +kernel
theorem pratchett_verdict : pratchett.failing cf = {L(fails["pratchett"])} := by decide +kernel
theorem roof_verdict : roofStyle.failing cf = {L(fails["roof"])} := by decide +kernel
theorem ao3_verdict : ao3.failing cf = {L(fails["ao3"])} := by decide +kernel

/-! ## House style: `/writelikeme` and the clarity check -/
open LangLib.Style.House
{hrecs}
def hf : HFeatures := HFeatures.ofSents asentsLore asents hsents
theorem house_features : hf = {{ {", ".join(f"{k} := {hf[k]}" for k in hfields)} }} := by decide +kernel
theorem clarity_verdict : clarity.failing hf = {L(hfails["clarity"])} := by decide +kernel
theorem writelikeme_verdict : writeLikeMe.failing hf = {L(hfails["writelikeme"])} := by decide +kernel
end Style
end Essays.{ns}
'''
(d / "Paper.lean").write_text(src)
json.dump({"house": house, "academic": acad, "core": core, "antithesis": anti, "fails": fails},
          open(d / "style-report.json", "w"), indent=1)
r = lean(d / "Paper.lean")
print(ns, "style", "proved" if r.returncode == 0 else "FAILED", r.stdout[-3000:], r.stderr[-1000:])
sys.exit(r.returncode)
