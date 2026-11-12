"""Render langlib figures to viz/out/: a parse tree with references, the gate
scene and its variants, the defeasible argument behind Kiran's shout, and the
model evaluation."""
import html, json, pathlib, subprocess
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "viz" / "out"
OUT.mkdir(parents=True, exist_ok=True)
LANGLIB = ROOT / ".lake/build/bin/langlib"

INK, MUTED, LINE, BG = "#1f2328", "#6e7781", "#d0d7de", "#ffffff"
GREEN, RED, AMBER, BLUE = "#1a7f37", "#cf222e", "#9a6700", "#0969da"
ENT_COLOURS = ["#0969da", "#8250df", "#bf3989", "#1a7f37", "#9a6700"]
FONT = "Helvetica"


def dot(src: str, name: str):
    out = OUT / f"{name}.png"
    subprocess.run(["dot", "-Tpng", "-Gdpi=170", "-o", str(out)], input=src.encode(), check=True)
    return out


def q(s: str) -> str:
    return s.replace("\\", "\\\\").replace('"', '\\"')


# 1 ── parse tree with references ────────────────────────────────────────────
def parse_tree():
    text = ROOT / "examples/cata.txt"
    doc = json.loads((ROOT / "examples/cata.json").read_text())
    rep = json.loads(subprocess.run([str(LANGLIB), "check", str(text), str(ROOT / "examples/cata.json")],
                                    capture_output=True, text=True).stdout)
    ents = {e["id"]: (e["name"], ENT_COLOURS[i % len(ENT_COLOURS)]) for i, e in enumerate(doc["entities"])}
    phora = {p["pos"]: p["phora"] for p in rep["pronouns"]}
    lines = [f'digraph G {{ bgcolor="{BG}"; rankdir=TB; nodesep=0.12; ranksep=0.32;',
             f'node [fontname="{FONT}", fontsize=11, color="{LINE}", fontcolor="{INK}"];',
             f'edge [color="{LINE}", fontname="{FONT}", fontsize=8, fontcolor="{MUTED}", arrowhead=none];']
    leaves, refs, n = [], [], [0]

    def go(t, parent, pos):
        n[0] += 1
        me = f"n{n[0]}"
        if "w" in t:
            colour = ents[t["ref"]][1] if t.get("ref") else INK
            lines.append(f'{me} [shape=plaintext, label=<<b>{html.escape(t["w"])}</b><br/>'
                         f'<font point-size="8" color="{MUTED}">{t["p"]}</font>>, fontcolor="{colour}"];')
            leaves.append(me)
            if t.get("ref"):
                refs.append((me, t["ref"], pos))
            pos += 1
        else:
            label = t["c"]
            style = f'shape=box, style="rounded", fontsize=10'
            if t.get("ref"):
                colour = ents[t["ref"]][1]
                style += f', color="{colour}", fontcolor="{colour}", penwidth=1.6'
                refs.append((me, t["ref"], pos))
            if t.get("spk"):
                label += f"  ({ents[t['spk']][0]} speaks)"
            lines.append(f'{me} [{style}, label="{q(label)}"];')
            for k in t["k"]:
                pos = go(k, me, pos)
        if parent:
            lines.append(f'{parent} -> {me} [label="{t.get("r", "")}"];')
        return pos

    pos = 0
    for i, s in enumerate(doc["sentences"]):
        pos = go(s, None, pos)
    lines.append("{ rank=same; " + " -> ".join(leaves) + " [style=invis]; }")
    lines.append("{ rank=sink; " + " ".join(f'e_{k} [shape=box, style="filled,rounded", fillcolor="{c}", '
                                              f'fontcolor="white", color="{c}", label="{q(nm)}"];'
                                              for k, (nm, c) in ents.items()) + " }")
    for me, eid, p in refs:
        ph = phora.get(p, "")
        style = "dashed" if ph == "cataphoric" else "solid"
        lab = {"cataphoric": "forward", "anaphoric": "back"}.get(ph, "")
        lines.append(f'{me} -> e_{eid} [color="{ents[eid][1]}", style={style}, arrowhead=normal, '
                     f'arrowsize=0.5, constraint=false, label="{lab}", fontcolor="{ents[eid][1]}"];')
    lines.append("}")
    return dot("\n".join(lines), "1-parse-tree")


# 2 ── the gate scene and its variants ───────────────────────────────────────
def gate_scene():
    setup = ["Mara goes to\nthe cellar", "Mara hides\nthe key", "Mara goes to\nthe gate", "guard grabs\nMara"]
    rows = [
        ("story", setup + ["Kiran shouts\nat the guard", "Mara tells Kiran\nkey is in cellar",
                           "Kiran goes to\nthe cellar", "Kiran takes\nthe key"],
         {4: ("ok", "plausible: protect a threatened ally [loyalty]\noverrides timid people keep quiet [safety]")}),
        ("leak", setup + ["Kiran shouts\nat the guard", "Kiran tells guard\nkey is in cellar"],
         {4: ("ok", ""), 5: ("hole", "PLOT HOLE: Kiran never learned\nthat the key is in the cellar")}),
        ("unprovoked", ["Kiran shouts\nat the guard"],
         {0: ("ooc", "OUT OF CHARACTER: timid people keep quiet [safety].\nTo justify it, first establish: the guard threatens Mara")}),
        ("tipsy", ["Kiran drinks", "Kiran shouts\nat the guard"],
         {1: ("weak", "in character (drink lifts the default)\nbut unmotivated")}),
        ("gagged", ["guard gags\nKiran", "Kiran shouts\nat the guard"],
         {1: ("hole", "PLOT HOLE: Kiran is gagged")}),
    ]
    status = {"ok": (GREEN, "#dafbe1"), "hole": (RED, "#ffebe9"), "ooc": (RED, "#ffebe9"),
              "weak": (AMBER, "#fff8c5"), None: (LINE, "#f6f8fa")}
    proof = {"story": "theorem story_valid", "leak": "theorem leak_invalid", "unprovoked": "theorem unprovoked_invalid",
             "tipsy": "theorem tipsy_valid", "gagged": "theorem gagged_invalid"}
    W, H, GX, GY = 1.55, 0.62, 0.25, 1.45
    fig, ax = plt.subplots(figsize=(17, 9.6))
    ax.set_xlim(-2.7, 8 * (W + GX) + 0.2)
    ax.set_ylim(-len(rows) * GY + 0.2, 1.0)
    ax.axis("off")
    ax.text(-2.7, 0.75, "The gate: timid Kiran (loyalty > safety > pride), her ally Mara, a guard, a key",
            fontsize=15, color=INK, fontweight="bold", family=FONT)
    for r, (name, evs, marks) in enumerate(rows):
        y = -r * GY
        ax.text(-2.65, y - H / 2 + 0.12, name, fontsize=13, color=INK, fontweight="bold", family=FONT)
        ax.text(-2.65, y - H / 2 - 0.13, proof[name], fontsize=8.5, color=MUTED, family="Menlo")
        for i, e in enumerate(evs):
            x = i * (W + GX)
            st = marks.get(i, (None, ""))[0] if i in marks else "ok"
            if i not in marks:
                st = None
            edge, fill = status[st]
            ax.add_patch(FancyBboxPatch((x, y - H), W, H, boxstyle="round,pad=0.02,rounding_size=0.08",
                                        linewidth=1.8 if st else 1, edgecolor=edge, facecolor=fill))
            ax.text(x + W / 2, y - H / 2, e, ha="center", va="center", fontsize=9.5, color=INK, family=FONT)
            if i + 1 < len(evs):
                ax.annotate("", xy=(x + W + GX - 0.02, y - H / 2), xytext=(x + W + 0.02, y - H / 2),
                            arrowprops=dict(arrowstyle="-|>", color=MUTED, lw=1))
            if i in marks and marks[i][1]:
                ax.text(x, y - H - 0.1, marks[i][1], fontsize=9, va="top", color=edge, family=FONT)
    fig.savefig(OUT / "2-gate-scene.png", dpi=150, bbox_inches="tight", facecolor=BG)
    plt.close(fig)
    return OUT / "2-gate-scene.png"


# 3 ── the argument behind the shout ─────────────────────────────────────────
def argument():
    def cluster(name, title, facts, rules, conclusion, verdict_colour, overrides):
        L = [f'subgraph cluster_{name} {{ label=<<b>{title}</b>>; fontname="{FONT}"; fontsize=13; '
             f'color="{LINE}"; style="rounded"; margin=14;']
        for fid, txt in facts:
            L.append(f'{name}_{fid} [shape=box, style="rounded,filled", fillcolor="#f6f8fa", label="{q(txt)}"];')
        for rid, txt, kind, active, head, body in rules:
            colour = (GREEN if head == "pos" else RED) if active else LINE
            fc = INK if active else MUTED
            shape = {"strict": "box", "defeasible": "box", "defeater": "box"}[kind]
            style = {"strict": "bold", "defeasible": "rounded", "defeater": "dashed,rounded"}[kind]
            L.append(f'{name}_{rid} [shape={shape}, style="{style}", color="{colour}", fontcolor="{fc}", label="{q(txt)}"];')
            for b in body:
                L.append(f'{name}_{b} -> {name}_{rid} [color="{INK if active else LINE}"];')
            L.append(f'{name}_{rid} -> {name}_{head} [color="{colour}", style="{"solid" if active else "dotted"}"];')
        L.append(f'{name}_pos [shape=box, style="rounded,filled", fillcolor="{"#dafbe1" if conclusion == "pos" else "#f6f8fa"}", '
                 f'color="{GREEN if conclusion == "pos" else LINE}", label="Kiran shouts at the guard"];')
        L.append(f'{name}_neg [shape=box, style="rounded,filled", fillcolor="{"#ffebe9" if conclusion == "neg" else "#f6f8fa"}", '
                 f'color="{RED if conclusion == "neg" else LINE}", label="Kiran stays quiet"];')
        L.append(f'{{ rank=same; {name}_pos; {name}_neg; }}')
        for a, b, lab in overrides:
            L.append(f'{name}_{a} -> {name}_{b} [color="{BLUE}", penwidth=1.8, constraint=false, label="{q(lab)}", fontcolor="{BLUE}"];')
        L.append(f'{name}_verdict [shape=plaintext, fontcolor="{verdict_colour}", fontsize=12, label=<<b>{verdict_colour and ""}</b>>];')
        L.append("}")
        return L

    base_rules = lambda threat: [
        ("timid", "timid people keep quiet\n[safety]", "defeasible", True, "neg", ["f_timid"]),
        ("protect", "protect a threatened ally\n[loyalty]", "defeasible", threat, "pos",
         ["f_ally", "f_near"] + (["f_threat"] if threat else [])),
        ("brash", "brash people speak up\n[pride]  (needs: Kiran is brash)", "defeasible", False, "pos", []),
        ("gag", "the gagged cannot shout\n(strict; needs: Kiran is gagged)", "strict", False, "neg", []),
    ]
    facts = [("f_timid", "Kiran is timid"), ("f_ally", "Mara is Kiran's ally"), ("f_near", "Kiran is near Mara")]
    L = [f'digraph G {{ bgcolor="{BG}"; rankdir=TB; nodesep=0.3; ranksep=0.45; compound=true;',
         f'node [fontname="{FONT}", fontsize=11, color="{LINE}", fontcolor="{INK}"];',
         f'edge [color="{MUTED}", fontname="{FONT}", fontsize=9, arrowsize=0.6];']
    L += cluster("gate", "At the gate, after the guard grabs Mara: plausible (Def)",
                 facts + [("f_threat", "the guard threatens Mara")], base_rules(True), "pos", GREEN,
                 [("protect", "timid", "overrides: Kiran ranks\nloyalty > safety")])
    L += cluster("calm", "Unprovoked: out of character (Def of 'stays quiet')",
                 facts, base_rules(False), "neg", RED, [])
    L.append(f'calm_hint [shape=note, color="{AMBER}", fontcolor="{AMBER}", '
             f'label="justification debt:\\nestablish \\"the guard threatens Mara\\"\\nto enable the protect rule"];')
    L.append("calm_protect -> calm_hint [style=dotted, color=\"#9a6700\", arrowhead=none];")
    L.append("}")
    src = "\n".join(l for l in L if "_verdict" not in l)
    return dot(src, "3-argument")


# 4 ── the evaluation ────────────────────────────────────────────────────────
def evaluation():
    data = {  # model: (nested r1, nested final, flat r1, flat final) — raw condition
        "Haiku": (35, 55, 15, 50), "Sonnet": (80, 100, 95, 100),
        "Opus": (90, 100, None, None), "Fable": (90, 100, 95, 100)}
    fig, ax = plt.subplots(figsize=(10, 5.2))
    xs = range(len(data))
    w = 0.19
    series = [("nested, 1st try", 0, "#9ecbff"), ("nested, ≤3 tries", 1, BLUE),
              ("flat, 1st try", 2, "#c4b5fd"), ("flat, ≤3 tries", 3, "#8250df")]
    for j, (lab, idx, col) in enumerate(series):
        vals = [v[idx] for v in data.values()]
        for i, v in enumerate(vals):
            x = i + (j - 1.5) * w
            if v is None:
                ax.text(x, 3, "not\nrun", ha="center", fontsize=7.5, color=MUTED, family=FONT)
                continue
            ax.bar(x, v, w * 0.92, color=col, label=lab if i == 0 else None)
            ax.text(x, v + 1.5, f"{v}", ha="center", fontsize=8.5, color=INK, family=FONT)
    ax.set_xticks(list(xs), list(data.keys()), fontsize=12, family=FONT)
    ax.set_ylim(0, 112)
    ax.set_ylabel("passages passing the check (%)", color=MUTED, family=FONT)
    ax.set_title("Encoding 20 passages faithfully (raw text, checker feedback between tries)",
                 loc="left", fontsize=12.5, color=INK, family=FONT, fontweight="bold")
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)
    ax.spines["left"].set_color(LINE); ax.spines["bottom"].set_color(LINE)
    ax.tick_params(colors=MUTED)
    ax.legend(frameon=False, ncol=4, loc="upper left", bbox_to_anchor=(0, -0.08), fontsize=9.5)
    fig.savefig(OUT / "4-eval.png", dpi=160, bbox_inches="tight", facecolor=BG)
    plt.close(fig)
    return OUT / "4-eval.png"


if __name__ == "__main__":
    for f in (parse_tree(), gate_scene(), argument(), evaluation()):
        print(f)
