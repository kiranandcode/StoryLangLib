"""Before and after: two certified directories side by side.

    compare.py <before-dir> <after-dir> [--title T]

Reads each directory's paragraphs/NN.txt and report.json (run certify.py on
both first) and prints Markdown: the two texts, then every rule that fails on
either side with the sentences it flags.
"""
import json, sys
from pathlib import Path


def text(d):
    ps = sorted((d / "paragraphs").glob("[0-9][0-9].txt"))
    return "\n\n".join(p.read_text().strip() for p in ps)


def main():
    a, b = Path(sys.argv[1]), Path(sys.argv[2])
    title = sys.argv[sys.argv.index("--title") + 1] if "--title" in sys.argv else b.parent.name
    ra, rb = json.load(open(a / "report.json")), json.load(open(b / "report.json"))
    rules_b = {r["name"]: r for r in rb["rules"]}
    out = [f"## {title}", "",
           f"Before: {sum(r['holds'] for r in ra['rules'])}/{len(ra['rules'])} rules hold "
           f"({'certified' if ra['certified'] else 'not certified'}). "
           f"After: {sum(r['holds'] for r in rb['rules'])}/{len(rb['rules'])} "
           f"({'certified' if rb['certified'] else 'not certified'}).", "",
           "**Before**", ""] + ["> " + l if l else ">" for l in text(a).split("\n")] + \
          ["", "**After**", ""] + ["> " + l if l else ">" for l in text(b).split("\n")] + \
          ["", "| rule | before | after |", "|:--|:--|:--|"]
    for r in ra["rules"]:
        rb_ = rules_b.get(r["name"], {"holds": None, "at": []})
        if r["holds"] and rb_["holds"]:
            continue
        def cell(x):
            if x["holds"] is None:
                return "n/a"
            mark = "holds" if x["holds"] else "**fails**"
            if x["at"] and x["at"][0]["at"] != "lexicon":
                mark += " (" + ", ".join(y["at"] for y in x["at"]) + ")"
            return mark
        out.append(f"| {r['name']} | {cell(r)} | {cell(rb_)} |")
    flagged = [(r["name"], y) for r in ra["rules"] if not r["holds"] for y in r["at"] if y["at"] != "lexicon"]
    if flagged:
        out += ["", "Sentences flagged before:", ""]
        seen = {}
        for name, y in flagged:
            seen.setdefault((y["at"], y["sentence"]), []).append(name)
        for (at, s), names in sorted(seen.items(), key=lambda kv: [int(x) for x in kv[0][0].split(":")]):
            out.append(f"- {at} ({'; '.join(names)}): {s}")
    print("\n".join(out))


if __name__ == "__main__":
    main()
