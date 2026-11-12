"""Summarise runs/results.jsonl: pass rates per model and condition, by round and
by source, and agreement between models' trees on passages both encoded
faithfully. Writes runs/summary.json and prints markdown tables."""
import itertools, json, pathlib, statistics
from collections import defaultdict

HERE = pathlib.Path(__file__).parent
RUNS = HERE / "runs"
MODELS = ["haiku", "sonnet", "opus", "fable"]


def load_results():
    rows = {}
    for line in (RUNS / "results.jsonl").read_text().splitlines():
        r = json.loads(line)
        rows[(r["model"], r["cond"], r["passage"])] = r  # last run wins
    return list(rows.values())


def final_doc(r):
    n = len(r["rounds"])
    p = RUNS / r["model"] / r["cond"] / f"{r['passage']}.r{n}.json"
    try:
        return json.loads(p.read_text())
    except Exception:
        return None


def walk(tree, start, out):
    """Collect (cat, i, j, ref) spans for nodes and (pos, role, ref) per leaf."""
    if "w" in tree:
        out["leaves"].append((tree.get("p"), tree.get("r"), tree.get("ref")))
        if tree.get("ref"):
            out["mentions"].append(((start, start + 1), tree["ref"]))
        return start + 1
    i = start
    for k in tree.get("k", []):
        i = walk(k, i, out)
    out["spans"].append((tree.get("c"), start, i))
    if tree.get("ref"):
        out["mentions"].append(((start, i), tree["ref"]))
    return i


def analyse(doc):
    out = {"leaves": [], "spans": [], "mentions": []}
    i = 0
    for s in doc.get("sentences", []):
        i = walk(s, i, out)
    return out


def f1(a, b):
    a, b = set(a), set(b)
    if not a and not b:
        return 1.0
    p = len(a & b) / len(b) if b else 0
    r = len(a & b) / len(a) if a else 0
    return 2 * p * r / (p + r) if p + r else 0.0


def coref_pairs(mentions):
    by = defaultdict(list)
    for span, e in mentions:
        by[e].append(span)
    return {tuple(sorted(p)) for spans in by.values() for p in itertools.combinations(set(spans), 2)}


def agreement(da, db):
    a, b = analyse(da), analyse(db)
    n = len(a["leaves"])
    if n != len(b["leaves"]) or n == 0:
        return None
    multi = lambda ss: [s for s in ss if s[2] - s[1] > 1]
    return {
        "upos": sum(x[0] == y[0] for x, y in zip(a["leaves"], b["leaves"])) / n,
        "role": sum(x[1] == y[1] for x, y in zip(a["leaves"], b["leaves"])) / n,
        "brackets_labeled": f1(multi(a["spans"]), multi(b["spans"])),
        "brackets_unlabeled": f1([s[1:] for s in multi(a["spans"])], [s[1:] for s in multi(b["spans"])]),
        "mentions": f1([m[0] for m in a["mentions"]], [m[0] for m in b["mentions"]]),
        "coref_links": f1(coref_pairs(a["mentions"]), coref_pairs(b["mentions"])),
    }


def mean(xs):
    xs = [x for x in xs if x is not None]
    return round(statistics.mean(xs), 3) if xs else None


def main():
    rows = load_results()
    conds = sorted({r["cond"] for r in rows})
    summary = {"pass": [], "by_source": {}, "agreement": [], "escape": []}

    print("## Faithfulness (token match + reference checks)\n")
    print("| model | cond | n | tokens ok r1 | pass r1 | pass ≤r2 | pass ≤r3 | mean edits r1 | mean ref issues r1 | mean secs/call | cost $ |")
    print("|---|---|---|---|---|---|---|---|---|---|---|")
    for m in MODELS:
        for c in conds:
            rs = [r for r in rows if r["model"] == m and r["cond"] == c]
            if not rs:
                continue
            n = len(rs)
            first = [r["rounds"][0] for r in rs]
            pr = lambda k: sum(1 for r in rs if r["passed_round"] and r["passed_round"] <= k) / n
            row = {"model": m, "cond": c, "n": n,
                   "tokens_r1": sum(1 for f in first if f["tokensMatch"]) / n,
                   "pass_r1": pr(1), "pass_r2": pr(2), "pass_r3": pr(3),
                   "edits_r1": mean([f["editCount"] for f in first]),
                   "refs_r1": mean([f["refIssues"] for f in first]),
                   "secs": mean([x["secs"] for r in rs for x in r["rounds"]]),
                   "cost": round(sum(x.get("cost") or 0 for r in rs for x in r["rounds"]), 2)}
            summary["pass"].append(row)
            print(f"| {m} | {c} | {n} | {row['tokens_r1']:.0%} | {row['pass_r1']:.0%} | {row['pass_r2']:.0%} | "
                  f"{row['pass_r3']:.0%} | {row['edits_r1']} | {row['refs_r1']} | {row['secs']} | {row['cost']} |")

    print("\n## Final pass rate by source (all models, both conditions)\n")
    by = defaultdict(list)
    for r in rows:
        by[r["passage"].rsplit("-", 1)[0]].append(r["passed"])
    print("| source | pass |\n|---|---|")
    for s, xs in sorted(by.items()):
        summary["by_source"][s] = sum(xs) / len(xs)
        print(f"| {s} | {sum(xs)}/{len(xs)} |")

    print("\n## Tree agreement between models (final docs, raw+tokens pooled, passages where both match tokens)\n")
    docs = {}
    for r in rows:
        if r["rounds"][-1]["tokensMatch"]:
            d = final_doc(r)
            if d:
                docs[(r["model"], r["cond"], r["passage"])] = d
    print("| pair | n | UPOS | leaf role | brackets (labeled F1) | brackets (unlabeled F1) | mention spans F1 | coref links F1 |")
    print("|---|---|---|---|---|---|---|---|")
    for a, b in itertools.combinations(MODELS, 2):
        ags = []
        for (m, c, p), d in docs.items():
            if m == a and (b, c, p) in docs:
                g = agreement(d, docs[(b, c, p)])
                if g:
                    ags.append(g)
        if not ags:
            continue
        row = {"pair": f"{a}~{b}", "n": len(ags), **{k: mean([g[k] for g in ags]) for k in ags[0]}}
        summary["agreement"].append(row)
        print(f"| {row['pair']} | {row['n']} | {row['upos']} | {row['role']} | {row['brackets_labeled']} | "
              f"{row['brackets_unlabeled']} | {row['mentions']} | {row['coref_links']} |")

    # self-consistency: same model, raw vs tokens
    print("\n## Same model, raw vs tokens condition\n")
    print("| model | n | UPOS | brackets (labeled F1) | coref links F1 |\n|---|---|---|---|---|")
    for m in MODELS:
        ags = [agreement(d, docs[(m, "tokens", p)]) for (mm, c, p), d in docs.items()
               if mm == m and c == "raw" and (m, "tokens", p) in docs]
        ags = [g for g in ags if g]
        if ags:
            print(f"| {m} | {len(ags)} | {mean([g['upos'] for g in ags])} | "
                  f"{mean([g['brackets_labeled'] for g in ags])} | {mean([g['coref_links'] for g in ags])} |")

    print("\n## Escape hatches (share of nodes FRAG, leaves X, roles dep)\n")
    print("| model | FRAG nodes | X leaves | dep roles | categories used |\n|---|---|---|---|---|")
    for m in MODELS:
        spans, leaves = [], []
        for (mm, c, p), d in docs.items():
            if mm == m:
                a = analyse(d)
                spans += a["spans"]; leaves += a["leaves"]
        if not spans:
            continue
        cats = sorted({s[0] for s in spans})
        row = {"model": m, "frag": sum(s[0] == "FRAG" for s in spans) / len(spans),
               "x": sum(l[0] == "X" for l in leaves) / len(leaves),
               "dep": sum(l[1] == "dep" for l in leaves) / len(leaves)}
        summary["escape"].append(row)
        print(f"| {m} | {row['frag']:.1%} | {row['x']:.1%} | {row['dep']:.1%} | {' '.join(cats)} |")

    (RUNS / "summary.json").write_text(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
