"""Proof figures: the defeasible-logic rules beside their Lean constructors, a
derivation tree for Kiran's shout at the gate, and the bridge from text to the
derivation's leaves."""
import html, json, pathlib, subprocess
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "viz" / "out"
LANGLIB = ROOT / ".lake/build/bin/langlib"
MONO = "DejaVu Sans Mono"
INK, MUTED, LINE = "#1f2328", "#6e7781", "#8c959f"
TEXT_C, SHEET_C, GOAL_C, LEAN_C = "#1a7f37", "#8250df", "#0969da", "#953800"
FS = 11
CW = 0.602 * FS          # char width in points
LH = 2.1 * FS            # row height in points


# ── a tiny proof-tree layout in character units ──────────────────────────────
class N:
    def __init__(self, concl, label="", kids=(), colour=INK, bar=True):
        self.concl, self.label, self.kids, self.colour = concl, label, list(kids), colour
        self.bar = bar and (bool(self.kids) or bool(label))

GAP = 3

def kids_w(n): return sum(width(k) for k in n.kids) + GAP * max(0, len(n.kids) - 1)
def body_w(n): return max(len(n.concl), kids_w(n))
def width(n): return body_w(n) + (len(n.label) + 2 if n.bar and n.label else 0)
def height(n): return 1 + (max(height(k) for k in n.kids) + 0.25 if n.kids else (0.7 if n.bar else 0))

def draw(ax, n, x, y):
    bw = body_w(n)
    ax.text(x + bw / 2, y + 0.35, n.concl, ha="center", va="center", family=MONO, fontsize=FS, color=n.colour)
    if n.bar:
        ax.plot([x, x + bw], [y + 0.8, y + 0.8], color=INK, lw=0.9)
        if n.label:
            ax.text(x + bw + 0.6, y + 0.8, n.label, va="center", family=MONO, fontsize=FS * 0.82, color=MUTED)
    kx = x + (bw - kids_w(n)) / 2
    for k in n.kids:
        draw(ax, k, kx, y + 1.25)
        kx += width(k) + GAP

def figure(w_chars, h_rows):
    fig = plt.figure(figsize=(w_chars * CW / 72, h_rows * LH / 72))
    ax = fig.add_axes([0, 0, 1, 1])
    ax.set_xlim(0, w_chars); ax.set_ylim(0, h_rows); ax.axis("off")
    return fig, ax


# ── R: rules beside their Lean constructors ──────────────────────────────────
RULES = [
    ("Strict.fact", "| fact : q ∈ T.facts → Strict T q", N("+Δ q", "fact", [N("q ∈ F", bar=False)])),
    ("Strict.rule", "| rule (r) : r ∈ T.rules → r.kind = .strict → r.head = q →\n    (∀ a ∈ r.body, Strict T a) → Strict T q",
     N("+Δ q", "strict", [N(s, bar=False) for s in ["r ∈ R", "r strict", "head r = q", "∀a ∈ body r. +Δ a"]])),
    ("Def.strict", "| strict : Strict T q → Def T q", N("+∂ q", "Def.strict", [N("+Δ q", bar=False)])),
    ("Def.rule", "| rule (r) : r ∈ T.rules → r.kind ≠ .defeater → r.head = q →\n    (∀ a ∈ r.body, Def T a) → ¬ Strict T q.neg →\n    (∀ s ∈ T.rules, s.head = q.neg → Rebutted T q s) → Def T q",
     N("+∂ q", "Def.rule", [N(s, bar=False) for s in ["r ∈ R", "r ≠ defeater", "head r = q", "∀a ∈ body r. +∂ a", "¬ +Δ ~q", "∀s with head ~q. Reb q s"]])),
    ("Rebutted.discarded", "| discarded : Discarded T s → Rebutted T q s", N("Reb q s", "discarded", [N("Disc s", bar=False)])),
    ("Rebutted.beaten", "| beaten (t) : t ∈ T.rules → t.kind ≠ .defeater → t.head = q →\n    (∀ a ∈ t.body, Def T a) → T.sup t s = true → Rebutted T q s",
     N("Reb q s", "beaten", [N(s, bar=False) for s in ["t ∈ R", "t ≠ defeater", "head t = q", "∀a ∈ body t. +∂ a", "t > s"]])),
    ("Discarded.mk", "| mk (a) : a ∈ r.body → NotDef T a → Discarded T r", N("Disc r", "mk", [N("a ∈ body r", bar=False), N("−∂ a", bar=False)])),
    ("NotDef.unsupported", "| unsupported : ¬ Strict T q →\n    (∀ r ∈ T.rules, r.kind ≠ .defeater → r.head = q → Discarded T r) → NotDef T q",
     N("−∂ q", "unsupported", [N("¬ +Δ q", bar=False), N("∀r ≠ defeater with head q. Disc r", bar=False)])),
    ("NotDef.contradicted", "| contradicted : ¬ Strict T q → Strict T q.neg → NotDef T q",
     N("−∂ q", "contradicted", [N("¬ +Δ q", bar=False), N("+Δ ~q", bar=False)])),
    ("NotDef.defeated", "| defeated (s) : ¬ Strict T q → s ∈ T.rules → s.head = q.neg →\n    (∀ a ∈ s.body, Def T a) →\n    (∀ t ∈ T.rules, t.kind ≠ .defeater → t.head = q → Unbeaten T t s) → NotDef T q",
     N("−∂ q", "defeated", [N(s, bar=False) for s in ["¬ +Δ q", "s ∈ R", "head s = ~q", "∀a ∈ body s. +∂ a", "∀t ≠ defeater with head q. Unb t s"]])),
    ("Unbeaten.discarded", "| discarded : Discarded T t → Unbeaten T t s", N("Unb t s", "discarded", [N("Disc t", bar=False)])),
    ("Unbeaten.notSup", "| notSup : T.sup t s = false → Unbeaten T t s", N("Unb t s", "notSup", [N("¬ (t > s)", bar=False)])),
]

def rules_figure():
    lean_w = max(len(l) for _, src, _ in RULES for l in src.split("\n")) + 4
    rule_w = max(width(r) for *_, r in RULES) + 2
    rows = [max(len(src.split("\n")) + 1.2, height(r) + 0.9) for _, src, r in RULES]
    W, H = lean_w + rule_w + 2, sum(rows) + 3
    fig, ax = figure(W, H)
    ax.text(0.5, H - 1, "Lean constructor", family=MONO, fontsize=FS * 1.1, color=MUTED, va="center")
    ax.text(lean_w + 1, H - 1, "the same rule on paper   (F facts, R rules, ~q the opposite of q, t > s: t overrides s)",
            family=MONO, fontsize=FS * 1.1, color=MUTED, va="center")
    y = H - 2.2
    for (name, src, r), h in zip(RULES, rows):
        y -= h
        ax.plot([0.3, W - 0.3], [y + h - 0.1, y + h - 0.1], color="#eaeef2", lw=0.8)
        ax.text(0.5, y + h - 0.65, name, family=MONO, fontsize=FS * 0.85, color=LEAN_C, va="center", fontweight="bold")
        for i, line in enumerate(src.split("\n")):
            ax.text(0.5, y + h - 1.55 - i * 0.85, line, family=MONO, fontsize=FS * 0.9, color=INK, va="center")
        draw(ax, r, lean_w + 1, y + (h - height(r)) / 2)
    fig.savefig(OUT / "5-rules.png", dpi=170, facecolor="white")
    plt.close(fig)
    return OUT / "5-rules.png"


# ── D: the derivation of Kiran's shout ───────────────────────────────────────
def fact(concl, colour):
    return N(f"+∂ {concl}", "Def.strict", [N(f"+Δ {concl}", "fact", [N(f"{concl} ∈ F", colour=colour, bar=False)])])

def derivation():
    q = "shouts(k,g)"
    tree = N(f"+∂ {q}", "Def.rule protect", [
        N("protect ∈ R, defeasible, head = shouts(k,g)", colour=MUTED, bar=False),
        fact("threatens(g,m)", TEXT_C),
        fact("ally(k,m)", SHEET_C),
        fact("near(k,m)", TEXT_C),
        N("¬ +Δ ¬shouts(k,g)", "strict closure", [N("gagged(k) ∉ F", colour=TEXT_C, bar=False)]),
        N("Reb q timid-quiet", "beaten by protect", [
            N("protect applicable (left)", colour=MUTED, bar=False),
            N("protect > timid-quiet", "sup", [N("Kiran: loyalty ≻ safety", colour=SHEET_C, bar=False)])]),
        N("Reb q gagged-silent", "discarded", [
            N("Disc gagged-silent", "mk", [
                N("gagged(k) ∈ body", colour=MUTED, bar=False),
                N("−∂ gagged(k)", "unsupported", [N("¬ +Δ gagged(k)", bar=False), N("no rule for gagged(k)", bar=False)])])]),
    ], colour=GOAL_C)
    W, H = width(tree) + 4, height(tree) + 4.2
    fig, ax = figure(W, H)
    draw(ax, tree, 2, 2.4)
    ax.text(2, 1.2, "q = shouts(k,g)   k = Kiran, m = Mara, g = the guard.   Theory: shoutTheory (state after the text's first four events) kiran guard",
            family=MONO, fontsize=FS * 0.85, color=MUTED)
    ax.text(2, 0.45, "green: facts from the text    purple: facts from the character sheet    blue: the action the text asserts",
            family=MONO, fontsize=FS * 0.85, color=MUTED)
    fig.savefig(OUT / "6-derivation.png", dpi=170, facecolor="white")
    plt.close(fig)
    return OUT / "6-derivation.png"


# ── B: text → tree → clauses → events → state → theory facts → derivation ────
def bridge():
    doc = json.loads((ROOT / "examples/gate.json").read_text())
    clauses = json.loads(subprocess.run([str(LANGLIB), "gate-events", str(ROOT / "examples/gate.json")],
                                        capture_output=True, text=True).stdout)
    names = {e["id"]: e["name"] for e in doc["entities"]}
    leaves = []
    def walk(t):
        if "w" in t: leaves.append(t)
        else:
            for k in t["k"]: walk(k)
    for s in doc["sentences"]: walk(s)
    ent_c = {"kiran": GOAL_C, "mara": "#bf3989", "guard": "#9a6700", "gate": MUTED, "cellar": MUTED, "key": MUTED}

    cells = []
    for i, w in enumerate(leaves):
        c = ent_c.get(w.get("ref"), INK)
        ref = f'<br/><font point-size="8" color="{c}">→{html.escape(names[w["ref"]])}</font>' if w.get("ref") else ""
        cells.append(f'<td port="t{i}" border="0" cellpadding="3"><font color="{c}"><b>{html.escape(w["w"])}</b></font>'
                     f'<br/><font point-size="8" color="{MUTED}">{w["p"]}</font>{ref}</td>')
    L = ['digraph B { rankdir=BT; bgcolor="white"; nodesep=0.25; ranksep=0.55; newrank=true;',
         f'node [fontname="Helvetica", fontsize=11, shape=box, style="rounded", color="#d0d7de", fontcolor="{INK}"];',
         f'edge [color="#afb8c1", arrowsize=0.6, fontname="Helvetica", fontsize=9, fontcolor="{MUTED}"];',
         f'text [shape=plaintext, label=<<table border="0" cellspacing="0"><tr><td colspan="{len(leaves)}" align="left">'
         f'<font point-size="10" color="{MUTED}">1 · the passage, annotated and checked (langlib Doc; pronoun refs shown under the words)</font></td></tr>'
         f'<tr>{"".join(cells)}</tr></table>>];']
    # clauses and events
    ev_label = {}
    for j, c in enumerate(clauses):
        args = [f"nsubj {names.get(c['subj'], c['subj'])}"]
        if c["obj"]: args.append(f"obj {names[c['obj']]}")
        args += [f"obl {p} {names[e]}" for p, e in c["obls"]]
        L.append(f'c{j} [label="clause: {c["verb"]}\\n{", ".join(args)}", fontsize=10];')
        L.append(f'text:t{c["at"]}:n -> c{j} [color="{INK}"];')
        ev = c["event"].replace("LangLib.Scene.Event.", "").replace("LangLib.Scene.Gate.", "")
        for k in ("Ch.", "Pl.", "Ob."): ev = ev.replace(k, "")
        ev = ev.replace("(", "").replace(")", "")
        parts = ev.split()
        pretty = f"{parts[0]}({', '.join(parts[1:])})"
        ev_label[j] = pretty
        colour = GOAL_C if parts[0] == "shout" else TEXT_C
        L.append(f'e{j} [label="Event.{pretty}", color="{colour}", fontcolor="{colour}"];')
        L.append(f'c{j} -> e{j} [label="lexicon"];')
    # pronoun links into clauses
    for i, w in enumerate(leaves):
        if w["p"] == "PRON" and w.get("ref"):
            j = min(range(len(clauses)), key=lambda j: abs(clauses[j]["at"] - i))
            L.append(f'text:t{i}:n -> c{j} [style=dashed, color="{ent_c[w["ref"]]}", label="ref"];')
    L.append("{ rank=same; " + " ".join(f"c{j};" for j in range(len(clauses))) + " }")
    L.append("{ rank=same; " + " ".join(f"e{j};" for j in range(len(clauses))) + " }")
    # state after the first four events
    L += [f'start [label="start state\\neveryone at the gate; Mara holds the key", color="#d0d7de", fontcolor="{MUTED}"];',
          f'sNear [label="state: loc Kiran = gate = loc Mara", color="{TEXT_C}"];',
          f'sThreat [label="state: threats ∋ (guard, Mara)", color="{TEXT_C}"];',
          f'sKey [label="state: key in the cellar (Mara saw it)", color="#d0d7de", fontcolor="{MUTED}"];',
          'start -> sNear; e2 -> sNear [label="step"]; e3 -> sThreat [label="step"]; e1 -> sKey [label="step"];',
          '{ rank=same; start; sNear; sThreat; sKey; }',
          f'sheet [label="character sheet (persona)\\nKiran: timid; loyalty ≻ safety ≻ pride; ally Mara", color="{SHEET_C}", fontcolor="{SHEET_C}"];',
          # theory facts
          f'fNear [label="near(k,m) ∈ F", color="{TEXT_C}", fontcolor="{TEXT_C}"];',
          f'fThreat [label="threatens(g,m) ∈ F", color="{TEXT_C}", fontcolor="{TEXT_C}"];',
          f'fAlly [label="ally(k,m) ∈ F", color="{SHEET_C}", fontcolor="{SHEET_C}"];',
          f'fTimid [label="trait(k,timid) ∈ F\\nsup from values", color="{SHEET_C}", fontcolor="{SHEET_C}"];',
          f'goal [label="goal: shouts(k,g)", color="{GOAL_C}", fontcolor="{GOAL_C}"];',
          'sNear -> fNear [label="shoutFacts"]; sThreat -> fThreat [label="shoutFacts"]; sheet -> fAlly; sheet -> fTimid;',
          'e4 -> goal [label="InCharacter s (shout k g)"];',
          '{ rank=same; sheet; fNear; fThreat; fAlly; fTimid; goal; }',
          f'deriv [shape=box, style="rounded,bold", color="{GOAL_C}", fontcolor="{INK}", '
          f'label="+∂ shouts(k,g)   (derivation tree, figure 6)\\n⇒ Motivated, InCharacter;   theorem fromText_valid : Valid start fromText"];',
          'fNear -> deriv; fThreat -> deriv; fAlly -> deriv; fTimid -> deriv [label="attacker, beaten"]; goal -> deriv;',
          "}"]
    out = OUT / "7-bridge.png"
    subprocess.run(["dot", "-Tpng", "-Gdpi=160", "-o", str(out)], input="\n".join(L).encode(), check=True)
    return out


if __name__ == "__main__":
    for f in (rules_figure(), derivation(), bridge()):
        print(f)
