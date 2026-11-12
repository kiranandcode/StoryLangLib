"""One figure: the gate passage's parse trees, the events read off them, the
scene facts they produce, and the defeasible derivation those facts feed, with
dashed lines for each step. Uses `langlib gate-events` for the clauses."""
import json, pathlib, subprocess
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch

ROOT = pathlib.Path(__file__).resolve().parent.parent
OUT = ROOT / "viz" / "out"
LANGLIB = ROOT / ".lake/build/bin/langlib"
MONO, SANS = "DejaVu Sans Mono", "DejaVu Sans"
INK, MUTED, FAINT = "#1f2328", "#6e7781", "#d0d7de"
TEXT_C, SHEET_C, GOAL_C = "#1a7f37", "#8250df", "#0969da"
ENT = {"kiran": GOAL_C, "mara": "#bf3989", "guard": "#9a6700"}
FS = 12
CW, LH = 0.602 * FS, 2.0 * FS   # points per x unit (one char) / y unit (one row)

doc = json.loads((ROOT / "examples/gate.json").read_text())
clauses = json.loads(subprocess.run([str(LANGLIB), "gate-events", str(ROOT / "examples/gate.json")],
                                    capture_output=True, text=True).stdout)

# ── layout of the parse trees (root up, words at the bottom) ──────────────────
TOK_Y = 0.0
toks, nodes = [], []          # toks: (x, word, pos, ref); nodes: (x, y, label, colour, kids_xy)
x = 2.0

def level(t):
    return 0 if "w" in t else 1 + max(level(k) for k in t["k"])

def lay(t):
    """Return the (x, y) of t's anchor; leaves get the next token slot."""
    global x
    if "w" in t:
        w = max(len(t["w"]), len(t["p"])) + 1.6
        cx = x + w / 2
        x += w
        toks.append((cx, t["w"], t["p"], t.get("ref")))
        return (cx, TOK_Y + 1.1)
    kid_xy = [lay(k) for k in t["k"]]
    cx = sum(p[0] for p in kid_xy) / len(kid_xy)
    cy = TOK_Y + 1.1 + 1.25 * level(t)
    label = t["c"] + (f"→{t['ref']}" if t.get("ref") else "")
    nodes.append((cx, cy, label, ENT.get(t.get("ref"), MUTED), kid_xy))
    return (cx, cy)

roots = []
for s in doc["sentences"]:
    roots.append(lay(s))
    x += 3.5
W = max(x + 2, 236)
tree_top = max(n[1] for n in nodes) + 0.8

# token index -> x, and the anchor of the NP that carries each ref
tok_x = [t[0] for t in toks]
np_anchor = {}  # (sentence-local first token, ref) -> xy
def find_refs(t, start):
    if "w" in t:
        return start + 1
    i = start
    for k in t["k"]:
        i = find_refs(k, i)
    return i

# ── bands (y grows upward; we stack downward from the tree) ───────────────────
TREE_BASE = 30.0      # tree band sits at the top
def T(y): return TREE_BASE + y
EV_Y = TREE_BASE - 4.0
ST_Y = EV_Y - 4.5
DER_TOP = ST_Y - 4.0

fig_h = TREE_BASE + tree_top + 2
fig = plt.figure(figsize=(W * CW / 72, fig_h * LH / 72))
ax = fig.add_axes([0, 0, 1, 1])
ax.set_xlim(0, W); ax.set_ylim(0, fig_h); ax.axis("off")

def box(cx, cy, text, colour, w=None, fill="white", fs=FS * 0.95, weight="normal"):
    w = w or len(text) * 0.74 + 2.5
    ax.add_patch(FancyBboxPatch((cx - w / 2, cy - 0.55), w, 1.1, boxstyle="round,pad=0.05,rounding_size=0.3",
                                edgecolor=colour, facecolor=fill, lw=1.3))
    ax.text(cx, cy, text, ha="center", va="center", family=SANS, fontsize=fs, color=colour, fontweight=weight)
    return (cx, cy)

def dashed(a, b, colour, lw=1.1, alpha=0.9):
    ax.annotate("", xy=b, xytext=a, arrowprops=dict(arrowstyle="-|>", ls="--", color=colour, lw=lw,
                                                    alpha=alpha, shrinkA=2, shrinkB=4))

def band_label(y, text):
    ax.text(0.6, y, text, family=SANS, fontsize=FS * 0.85, color=MUTED, va="center", style="italic")

# trees
for (cx, cy, label, colour, kids) in nodes:
    for (kx, ky) in kids:
        ax.plot([cx, kx], [T(cy) - 0.35, T(ky) + 0.35], color=FAINT, lw=0.9)
    ax.text(cx, T(cy), label, ha="center", va="center", family=MONO, fontsize=FS * 0.72,
            color=colour, fontweight="bold" if "→" in label else "normal")
for (cx, w, p, ref) in toks:
    ax.text(cx, T(TOK_Y + 0.45), w, ha="center", va="center", family=SANS, fontsize=FS,
            color=ENT.get(ref, INK), fontweight="bold")
    ax.text(cx, T(TOK_Y - 0.25), p, ha="center", va="center", family=MONO, fontsize=FS * 0.6, color=MUTED)
band_label(T(tree_top) - 0.2, "1  text, as a checked langlib document (constituency tree; →id marks a reference)")

# events, under their verbs
band_label(EV_Y + 1.3, "2  events read off the clauses (Bridge.lean: verb + nsubj / obj / obl refs)")
ev_xy = {}
for c in clauses:
    vx = tok_x[c["at"]]
    ev = c["event"].replace("LangLib.Scene.Event.", "").replace("LangLib.Scene.Gate.", "")
    for k in ("Ch.", "Pl.", "Ob.", "(", ")"): ev = ev.replace(k, "")
    name, *args = ev.split()
    pretty = f"{name}({', '.join(args)})"
    colour = GOAL_C if name == "shout" else (TEXT_C if name in ("grab", "move") and "gate" in args or name == "grab" else MUTED)
    ev_xy[pretty] = box(vx, EV_Y, pretty, colour)
    dashed((vx, T(TOK_Y - 0.6)), (vx, EV_Y + 0.6), colour)
    # argument words: subject / object / obl referents, nearest token with that ref in the sentence
    for ent in [c["subj"], c["obj"]] + [e for _, e in c["obls"]]:
        if ent in ENT:
            cands = [i for i, t in enumerate(toks) if t[3] == ent and abs(i - c["at"]) <= 4]
            if cands:
                i = min(cands, key=lambda i: abs(i - c["at"]))
                dashed((toks[i][0], T(TOK_Y - 0.6)), (vx + (toks[i][0] - vx) * 0.25, EV_Y + 0.6), ENT[ent], lw=0.8, alpha=0.6)

# fixed columns for the lower bands: premise x positions
XN, XT, XA, XG, XL, XU = 72, 100, 124, 150, 178, 210
mg, gr, sh = ev_xy["move(mara, gate)"], ev_xy["grab(guard, mara)"], ev_xy["shout(kiran, guard)"]

# scene facts and character sheet
band_label(ST_Y + 1.3, "3  scene state after the events (State.step), and Kiran's character sheet")
start = box(38, ST_Y, "start: everyone at the gate", MUTED)
st_near = box(XN, ST_Y, "loc Kiran = loc Mara = gate", TEXT_C)
st_thr = box(XT + 4, ST_Y, "threats ∋ (guard, Mara)", TEXT_C)
st_gag = box(XG, ST_Y, "Kiran not gagged", TEXT_C)
sheet = box(196, ST_Y, "Kiran: timid · loyalty ≻ safety ≻ pride · ally Mara", SHEET_C)
dashed((mg[0], EV_Y - 0.6), (st_near[0], ST_Y + 0.6), TEXT_C)
dashed((start[0] + 9.5, ST_Y), (st_near[0] - 9.5, ST_Y), MUTED)
dashed((gr[0], EV_Y - 0.6), (st_thr[0], ST_Y + 0.6), TEXT_C)

# derivation (premises on top, conclusion at the bottom)
band_label(DER_TOP + 1.2, "4  the defeasible derivation over shoutTheory (premises on top)")
y0 = DER_TOP - 0.4           # leaves of the attack branch
y1 = y0 - 1.6                # A/B premises, attack sub-conclusions
y2 = y1 - 1.6                # premises of the final rule
y3 = y2 - 1.6                # conclusion
def rule(x0, x1, y, label):
    ax.plot([x0, x1], [y, y], color=INK, lw=1)
    ax.text(x1 + 0.6, y, label, va="center", family=MONO, fontsize=FS * 0.68, color=MUTED)
def t(xc, y, s, c=INK, fs=FS * 0.95):
    ax.text(xc, y, s, ha="center", va="center", family=MONO, fontsize=fs, color=c)
# A: protect applies
t(XN, y1, "near(k,m)", TEXT_C); t(XT, y1, "threatens(g,m)", TEXT_C); t(XA, y1, "ally(k,m)", SHEET_C)
rule(XN - 6, XA + 6, y1 - 0.8, "fact")
A = (XN + XA) / 2; t(A, y2, "protect applies")
# B: nothing strict forbids it
t(XG, y1, "not gagged", TEXT_C); rule(XG - 7, XG + 7, y1 - 0.8, "closure")
t(XG, y2, "¬+Δ ¬shouts(k,g)")
# C: every attack fails
t(XL, y0, "loyalty ≻ safety", SHEET_C); rule(XL - 9, XL + 9, y0 - 0.8, "sup")
t(XU, y0, "gagged(k) unprovable"); rule(XU - 11, XU + 11, y0 - 0.8, "−∂")
t(XL, y1, "timid-quiet beaten", fs=FS * 0.85); t(XU, y1, "gagged-silent discarded", fs=FS * 0.85)
rule(XL - 9, XU + 11, y1 - 0.8, "∀ attackers")
C = (XL + XU) / 2; t(C, y2, "every attack fails")
# conclusion
rule(XN - 8, XU + 11, y2 - 0.8, "Def.rule protect")
goal = ((XN + XU) / 2, y3)
t(goal[0], goal[1], "+∂ shouts(k,g)", GOAL_C, fs=FS * 1.15)
t(goal[0], y3 - 1.1, "⇒ InCharacter s (shout kiran guard)      theorem fromText_valid : Valid start fromText",
  MUTED, fs=FS * 0.75)

# state → premises
dashed((st_near[0], ST_Y - 0.6), (XN, y1 + 0.5), TEXT_C)
dashed((st_thr[0], ST_Y - 0.6), (XT, y1 + 0.5), TEXT_C)
dashed((st_gag[0], ST_Y - 0.6), (XG, y1 + 0.5), TEXT_C)
dashed((sheet[0] - 18, ST_Y - 0.6), (XA, y1 + 0.5), SHEET_C)
dashed((sheet[0] - 6, ST_Y - 0.6), (XL, y0 + 0.5), SHEET_C)
# the shout event is the question the derivation answers: route down the right margin
xr = W - 3
ax.plot([sh[0] + 7, xr, xr], [EV_Y, EV_Y, y3], ls="--", color=GOAL_C, lw=1.3)
ax.annotate("", xy=(goal[0] + 8, y3), xytext=(xr, y3),
            arrowprops=dict(arrowstyle="-|>", ls="--", color=GOAL_C, lw=1.3, shrinkA=0, shrinkB=2))
ax.text(xr - 1, EV_Y + 0.7, "is this shout in character?", family=SANS, fontsize=FS * 0.8,
        color=GOAL_C, style="italic", ha="right")

ax.set_ylim(y3 - 2.2, fig_h)
fig.savefig(OUT / "8-bridge-full.png", dpi=150, facecolor="white", bbox_inches="tight")
print(OUT / "8-bridge-full.png")
