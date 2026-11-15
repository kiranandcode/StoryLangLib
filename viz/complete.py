"""One paragraph, judged: its parse trees, and under every clause the judgements
that tie it to the world (events, claims, content, goals, ...), with the
connectives the checker reads as arcs between clauses. Each sentence is a row.
Words with a sense are marked; anything the checker objects to is red.

    python3 viz/complete.py stories/hxh-chrollo-hisoka 7
"""
import json, pathlib, subprocess, sys
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "viz" / "out"
LANGLIB = ROOT / ".lake/build/bin/langlib"
MONO, SANS = "DejaVu Sans Mono", "DejaVu Sans"
INK, MUTED, FAINT, BAD = "#1f2328", "#6e7781", "#d0d7de", "#cf222e"
KIND_C = {"event": "#1a7f37", "claim": "#8250df", "content": "#0969da", "goal": "#bc4c00",
          "act": "#57606a", "speech": "#57606a", "hypothetical": "#57606a", "external": "#9a6700"}
LINK_C = {"cause": "#cf222e", "effect": "#cf222e", "purpose": "#bc4c00", "after": "#0969da",
          "before": "#0969da", "during": "#0969da", "concession": "#57606a", "condition": "#57606a"}
FS = 11
CW, LH = 0.602 * FS, 2.0 * FS

story = pathlib.Path(sys.argv[1]).resolve()
k = int(sys.argv[2])
nn = f"{k:02}"
doc = json.loads((story / "paragraphs" / f"{nn}.json").read_text())
reading = json.loads((story / "paragraphs" / f"{nn}.events.json").read_text())
report = json.loads(subprocess.run([str(LANGLIB), "story", str(story)], capture_output=True, text=True).stdout)
comp = next(c for c in report["completeness"] if c["name"] == nn)
names = {c["id"]: c["name"] for c in report["characters"]}

# judgements by the token they are anchored at
judged: dict[int, list[tuple[str, str]]] = {}
for e in reading["events"]:
    judged.setdefault(e["at"], []).append(("event", e["e"]))
for c in reading.get("claims", []):
    if isinstance(c, dict):
        judged.setdefault(c["at"], []).append(("claim", c["c"]))
for j in reading.get("judge", []):
    text = {"content": f"content: {j.get('lit', '')}", "goal": f"goal: {j.get('lit', '')}",
            "external": f"Nen: {j.get('e', '')}"}.get(j["kind"], j["kind"])
    judged.setdefault(j["at"], []).append((j["kind"], text))
issues = comp["issues"]
bad_tok = {int(t) for i in issues for t in [i.split("(token ")[1].split(")")[0]] if "(token " in i}
clauses = {c["at"]: c for c in comp["clauses"]}

# ── layout: one row per sentence, words at the bottom of the tree ────────────
def level(t):
    return 0 if "w" in t else 1 + max(level(k) for k in t["k"])

rows = []     # per sentence: toks [(x, word, upos, ref, sense, i)], nodes [(x, y, label, kids)]
tok_i = 0
for s in doc["sentences"]:
    toks, nodes = [], []
    state = {"x": 2.0}
    def lay(t):
        global tok_i
        if "w" in t:
            w = max(len(t["w"]) * 1.15, 4.5) + 1.4
            cx = state["x"] + w / 2
            state["x"] += w
            toks.append((cx, t["w"], t["p"], t.get("ref"), t.get("sense"), tok_i))
            tok_i += 1
            return (cx, 1.1)
        kid_xy = [lay(c) for c in t["k"]]
        cx = sum(p[0] for p in kid_xy) / len(kid_xy)
        cy = 1.1 + 0.85 * level(t)
        label = t["c"] + (f"→{t['ref']}" if t.get("ref") else "")
        nodes.append((cx, cy, label, kid_xy))
        return (cx, cy)
    lay(s)
    rows.append((toks, nodes, state["x"] + 2, max(n[1] for n in nodes) + 0.6))

W = max(r[2] for r in rows) + 2
# per row: tree height, then the judgement band (stacked boxes) and arcs
def jdepth(toks):
    return max([len(judged.get(t[5], [])) for t in toks] + [0])
def arcdepth(toks):
    ids = {t[5] for t in toks}
    xs = {t[5]: t[0] for t in toks}
    spans = [abs(xs[l["b"]] - xs[l["a"]]) for l in comp["links"]
             if l["a"] != l["b"] and l["a"] in ids and l["b"] in ids]
    return (0.18 * max(spans) * CW / 2 / LH + 1.6) if spans else 0.6
row_h = [r[3] + 2.2 + 1.35 * (jdepth(r[0]) + 1) + arcdepth(r[0]) + 1.0 for r in rows]
H = sum(row_h) + 3.5 + 1.1 * len(issues)
fig = plt.figure(figsize=(W * CW / 72, H * LH / 72))
ax = fig.add_axes([0, 0, 1, 1])
ax.set_xlim(0, W); ax.set_ylim(0, H); ax.axis("off")

def bw(text):
    return len(text) * 0.84 + 1.8

def box(cx, cy, text, colour, fill="white", fs=FS * 0.8):
    w = bw(text)
    ax.add_patch(FancyBboxPatch((cx - w / 2, cy - 0.5), w, 1.0, boxstyle="round,pad=0.04,rounding_size=0.3",
                                edgecolor=colour, facecolor=fill, lw=1.2))
    ax.text(cx, cy, text, ha="center", va="center", family=MONO, fontsize=fs, color=colour)

story_title = json.loads((story / "story.json").read_text()).get("title", story.name)
title = f"{story_title} · paragraph {nn}: every clause judged"
ax.text(1, H - 1.2, title, family=SANS, fontsize=FS * 1.2, color=INK, fontweight="bold", va="center")
ax.text(1, H - 2.3, ("complete: no objections" if not issues else f"{len(issues)} objection(s), in red"),
        family=SANS, fontsize=FS * 0.9, color=(KIND_C["event"] if not issues else BAD), va="center")
legend = "   ".join(f"■ {k}" for k in ["event", "claim", "content", "goal", "external", "act/speech/hypothetical"])
x0 = 30
for k, c in [("event", KIND_C["event"]), ("claim", KIND_C["claim"]), ("content", KIND_C["content"]),
             ("goal", KIND_C["goal"]), ("Nen move", KIND_C["external"]), ("act · speech · hypothetical", KIND_C["act"])]:
    ax.text(x0, H - 2.3, "■ " + k, family=SANS, fontsize=FS * 0.85, color=c, va="center")
    x0 += len(k) * 0.75 + 5

tok_xy = {}
top = H - 3.5
for (toks, nodes, _, th), rh in zip(rows, row_h):
    base = top - th          # word baseline of this row
    def Y(y): return base + y - 1.1
    for (cx, cy, label, kids) in nodes:
        for (kx, ky) in kids:
            ax.plot([cx, kx], [Y(cy) - 0.3, Y(ky) + 0.3], color=FAINT, lw=0.8)
        ax.text(cx, Y(cy), label, ha="center", va="center", family=MONO, fontsize=FS * 0.62, color=MUTED)
    for (cx, w, p, ref, sense, i) in toks:
        is_clause = i in clauses
        colour = BAD if i in bad_tok else (INK if not is_clause else KIND_C["event"] if any(
            k == "event" for k, _ in judged.get(i, [])) else INK)
        ax.text(cx, Y(0.55), w, ha="center", va="center", family=SANS, fontsize=FS,
                color=colour, fontweight="bold" if is_clause else "normal")
        sub = p + (f"·{sense}" if sense and p in ("ADV", "ADJ") else "")
        ax.text(cx, Y(-0.05), sub, ha="center", va="center", family=MONO, fontsize=FS * 0.55,
                color=(KIND_C["goal"] if sense and p in ("ADV", "ADJ") else MUTED))
        tok_xy[i] = (cx, Y(-0.5))
    # judgements under their clause heads, stacked; a box that would overlap one
    # already placed on its level goes a level down
    jy0 = Y(-1.7)
    levels: list[list[tuple[float, float]]] = []
    placed_depth = 0
    for (cx, w, p, ref, sense, i) in toks:
        items = judged.get(i, []) or ([("missing", "no judgement")] if i in clauses else [])
        d = 0
        for n, (kind, text) in enumerate(items):
            lo, hi = cx - bw(text) / 2 - 0.4, cx + bw(text) / 2 + 0.4
            while d < len(levels) and any(not (hi < a or lo > b) for a, b in levels[d]):
                d += 1
            if d == len(levels):
                levels.append([])
            levels[d].append((lo, hi))
            yy = jy0 - 1.35 * d
            colour = BAD if kind == "missing" else KIND_C.get(kind, MUTED)
            box(cx, yy, text, colour, fill=("#ffebe9" if i in bad_tok else "white"))
            if n == 0:
                ax.plot([cx, cx], [Y(-0.4), yy + 0.5], ls="--", color=colour, lw=0.9)
            d += 1
            placed_depth = max(placed_depth, d)
    # connective arcs within the row, below the judgements; the label sits under the arc's lowest point
    ay = jy0 - 1.35 * max(placed_depth - 1, 0) - 1.1
    row_tokens = {t[5] for t in toks}
    RAD = 0.18
    for l in comp["links"]:
        if l["a"] == l["b"] or l["a"] not in row_tokens or l["b"] not in row_tokens:
            continue
        xa, xb = tok_xy[l["a"]][0], tok_xy[l["b"]][0]
        colour = BAD if l["at"] in bad_tok else LINK_C.get(l["rel"], MUTED)
        # bulge downward whichever way the arc runs
        rad = RAD if xb > xa else -RAD
        ax.add_patch(FancyArrowPatch((xa, ay), (xb, ay), connectionstyle=f"arc3,rad={rad}",
                                     arrowstyle="-|>", mutation_scale=10, color=colour, lw=1.3))
        sag = RAD * abs(xb - xa) * CW / 2 / LH       # depth of the arc, in row units
        ok = "✗" if l["at"] in bad_tok else "✓"
        ax.text((xa + xb) / 2, ay - sag - 0.55, f"'{l['word']}': {l['rel']} {ok}",
                ha="center", va="center", family=SANS, fontsize=FS * 0.8, color=colour)
    top -= rh

for n, i in enumerate(issues):
    ax.text(1, 2.0 + 1.1 * (len(issues) - 1 - n), "✗ " + i, family=SANS, fontsize=FS * 0.8, color=BAD, va="center")
ax.text(1, 0.8, "dashed: the word a judgement is anchored at · arcs: connectives, from the clause they introduce "
        "to the clause they attach to, checked against the model (time order, cause, purpose, …)",
        family=SANS, fontsize=FS * 0.75, color=MUTED, va="center")
out = OUT / f"complete-{story.name}-{nn}.png"
fig.savefig(out, dpi=150, facecolor="white", bbox_inches="tight")
print(out)
