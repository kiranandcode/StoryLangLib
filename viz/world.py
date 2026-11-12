"""Figures for the modular world layer: the module structure, and the office
story's timeline (text order vs story time) with the end-state beliefs."""
import pathlib, subprocess
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch

OUT = pathlib.Path(__file__).resolve().parent / "out"
SANS, MONO = "DejaVu Sans", "DejaVu Sans Mono"
INK, MUTED, FAINT = "#1f2328", "#6e7781", "#d0d7de"
SPACE, MIND, SOCIAL, MAGIC, CORE = "#1a7f37", "#0969da", "#bf3989", "#8250df", "#57606a"


def modules():
    L = ['digraph M { rankdir=BT; bgcolor="white"; nodesep=0.35; ranksep=0.6;',
         'node [fontname="DejaVu Sans", fontsize=11, shape=box, style="rounded", color="#d0d7de"];',
         'edge [color="#8c959f", arrowsize=0.6, fontname="DejaVu Sans", fontsize=9, fontcolor="#6e7781"];',
         f'core [label=<<b>Domain W E</b><br/><font point-size="9">ok · step · why · Perceive<br/>Valid (decidable) · Timed stories</font>>, color="{CORE}"];',
         f'time [label=<<b>Time</b><br/><font point-size="9">Allen intervals (13, exhaustive + disjoint)<br/>timeline = consistency certificate</font>>, color="{CORE}"];',
         f'dl [label=<<b>Defeasible logic</b><br/><font point-size="9">Def / NotDef, coherent, Cert.sound</font>>, color="{CORE}"];',
         f'persona [label=<<b>Persona</b><br/><font point-size="9">traits · ranked values<br/>inCharacter / motivated</font>>, color="{CORE}"];',
         f'space [label=<<b>Space</b><br/><font point-size="9">HasSpace: where, who holds what<br/>move · take · drop · give</font>>, color="{SPACE}", fontcolor="{SPACE}"];',
         f'mind [label=<<b>Minds</b><br/><font point-size="9">HasMinds: nested beliefs<br/>witnessing · tell · whisper · lie</font>>, color="{MIND}", fontcolor="{MIND}"];',
         f'social [label=<<b>Relationships</b><br/><font point-size="9">HasBonds: trust · attraction · affection · tension<br/>flirt · confide · argue · ask · agree · withdraw · act<br/>consent gates every act</font>>, color="{SOCIAL}", fontcolor="{SOCIAL}"];',
         f'magic [label=<<b>Magic</b><br/><font point-size="9">HasMana: spells, mana<br/>cast · rest</font>>, color="{MAGIC}", fontcolor="{MAGIC}"];',
         f'office [shape=note, label=<<b>Office</b> = Space ⊕ Minds ⊕ Relationships<br/><font point-size="9">flashback, meanwhile, false belief, consent</font>>];',
         f'mage [shape=note, label=<<b>Mage</b> = Space ⊕ Minds ⊕ Magic<br/><font point-size="9">secret powers, mana limits</font>>];',
         'time -> core; dl -> persona; core -> space; core -> mind; core -> social; core -> magic; persona -> social;',
         'space -> mind [label="Observable, HasLoc"]; space -> social [label="HasLoc"]; space -> magic [label="HasLoc"];',
         'space -> office; mind -> office; social -> office; space -> mage; mind -> mage; magic -> mage;',
         '{ rank=same; space; persona; }', '{ rank=same; mind; social; magic; }', '}']
    out = OUT / "9-modules.png"
    subprocess.run(["dot", "-Tpng", "-Gdpi=160", "-o", str(out)], input="\n".join(L).encode(), check=True)
    return out


def timeline():
    # (told index, text, module colour, interval)
    ev = [(0, "Marcus confides in Kiran", SOCIAL, (2, 4)),
          (1, "Marcus flirts", SOCIAL, (4, 5)),
          (2, "Kiran flirts back", SOCIAL, (5, 6)),
          (3, "meanwhile: Mara takes the letter (office)", SPACE, (3, 6)),
          (4, "Marcus asks to kiss her", SOCIAL, (6, 7)),
          (5, "Kiran agrees", SOCIAL, (7, 8)),
          (6, "Marcus agrees", SOCIAL, (7, 8)),
          (7, "Kiran kisses Marcus", SOCIAL, (8, 9)),
          (8, "flashback: Marcus left the letter", SPACE, (0, 1)),
          (9, "… and came up to the roof", SPACE, (1, 2))]
    fig, ax = plt.subplots(figsize=(13, 6.4))
    for i, text, c, (s, e) in ev:
        y = -i
        ax.add_patch(FancyBboxPatch((s + 0.04, y - 0.32), e - s - 0.08, 0.64,
                                    boxstyle="round,pad=0,rounding_size=0.12", facecolor=c, alpha=0.18, edgecolor=c, lw=1.4))
        ax.text(-0.3, y, f"{i}  {text}", ha="right", va="center", family=SANS, fontsize=10.5, color=INK)
    ax.axvspan(3, 6, color="#ddf4ff", alpha=0.35, lw=0)
    ax.text(4.5, 0.75, "meanwhile (Allen: contains / overlaps)", ha="center", fontsize=9, color=MIND, family=SANS)
    ax.annotate("", xy=(0.5, -8.6), xytext=(2.0, 0.55), arrowprops=dict(arrowstyle="-|>", ls="--", color=MUTED,
                connectionstyle="arc3,rad=0.35"))
    ax.text(0.2, -6.6, "told last,\nhappened first\n(before/meets 0)", fontsize=9, color=MUTED, family=SANS)
    ax.text(7.5, -6.85, "equal", fontsize=8.5, color=MUTED, ha="center", family=SANS)
    ax.text(8.5, -7.65, "needs both\nconsents", fontsize=8.5, color=SOCIAL, ha="center", family=SANS)
    ax.set_xlim(-0.2, 9.4); ax.set_ylim(-9.8, 1.2)
    ax.set_xticks(range(10)); ax.set_yticks([])
    ax.set_xlabel("story time (the timeline is the certificate that the text's constraints are consistent)",
                  color=MUTED, family=SANS, fontsize=9.5)
    for s in ("top", "right", "left"): ax.spines[s].set_visible(False)
    ax.spines["bottom"].set_color(FAINT); ax.tick_params(colors=MUTED)
    ax.set_title("The office story: rows in the order the text tells it, bars in story time",
                 loc="left", fontsize=12.5, color=INK, family=SANS, fontweight="bold", x=-0.42)
    beliefs = ("at t = 9 (all proved by decide):\n"
               "Marcus believes the letter is in the office   FALSE (false belief)\n"
               "Mara knows she holds the letter\n"
               "Kiran saw the kiss; Mara never did\n"
               "Kiran stays on the roof throughout event 3")
    fig.text(0.02, -0.06, beliefs, family=MONO, fontsize=9.5, color=INK, va="top")
    fig.savefig(OUT / "10-office-timeline.png", dpi=160, bbox_inches="tight", facecolor="white")
    plt.close(fig)
    return OUT / "10-office-timeline.png"




def gossip():
    steps = ["Mara takes the\nletter (office)", "Mara goes\nto the roof", "Mara to Kiran:\n\"I never read it\" (lie)",
             "Mara puts the\nletter down (roof)", "Mara picks it\nup (roof)", "Marcus goes\nto the roof",
             "Mara to Marcus:\n\"I never read it\" (lie)"]
    G, R, A, N = ("#dafbe1", "#1a7f37"), ("#ffebe9", "#cf222e"), ("#fff8c5", "#9a6700"), ("#f6f8fa", MUTED)
    rows = {
        "Kiran": [("—", N), ("—", N), ("¬read(Mara)\ntold by Mara", A), ("¬read(Mara)\ntold", A),
                  ("read(Mara)\nseen ⇒ lore;\nhearsay dropped", G), ("read(Mara)", G), ("read(Mara)\nknows Mara lied", G)],
        "Marcus": [("read(Mara)\nseen holds ⇒ lore", G), ("read(Mara)", G), ("read(Mara)", G), ("read(Mara)", G),
                   ("read(Mara)", G), ("read(Mara)", G), ("read(Mara)\nlie REJECTED:\nnotes Mara claims ¬", R)],
    }
    fig, ax = plt.subplots(figsize=(15, 4.6))
    cw, ch = 2.0, 1.25
    for j, s in enumerate(steps):
        ax.text(j * cw + cw / 2, 2 * ch + 0.55, f"{j + 1}. {s}", ha="center", va="center", fontsize=9, family=SANS, color=INK)
    for i, (who, cells) in enumerate(rows.items()):
        y = (1 - i) * ch
        ax.text(-0.15, y + ch / 2, who, ha="right", va="center", fontsize=12, family=SANS, fontweight="bold", color=INK)
        for j, (txt, (fill, edge)) in enumerate(cells):
            ax.add_patch(FancyBboxPatch((j * cw + 0.08, y + 0.08), cw - 0.16, ch - 0.16,
                                        boxstyle="round,pad=0,rounding_size=0.08", facecolor=fill, edgecolor=edge, lw=1.1))
            ax.text(j * cw + cw / 2, y + ch / 2, txt, ha="center", va="center", fontsize=8.6, family=MONO, color=INK)
    ax.set_xlim(-1.4, len(steps) * cw + 0.1); ax.set_ylim(-0.3, 2 * ch + 1.1); ax.axis("off")
    ax.set_title("Who thinks Mara read the letter? (lore: whoever holds it has read it; seeing beats hearsay)",
                 loc="left", fontsize=12, family=SANS, fontweight="bold", color=INK)
    fig.text(0.07, 0.02, "theorems: marcus_infers · kiran_believed_the_lie · kiran_caught_the_lie · marcus_rejects_the_lie · "
             "contradiction_rejected;  Invariant: every mind stays consistent, checked by Valid",
             fontsize=8.5, family=MONO, color=MUTED)
    fig.savefig(OUT / "11-gossip-beliefs.png", dpi=160, bbox_inches="tight", facecolor="white")
    plt.close(fig)
    return OUT / "11-gossip-beliefs.png"


def office_text():
    ev = [(0, "Marcus confided in Kiran.", SOCIAL, (51, 52)),
          (1, "He flirted with her,", SOCIAL, (53, 54)),
          (2, "and she flirted with him.", SOCIAL, (55, 58)),
          (3, "Meanwhile, Mara took the letter.", SPACE, (56, 57)),
          (4, "Marcus asked Kiran for a kiss.", SOCIAL, (59, 60)),
          (5, "Kiran agreed to kiss him,", SOCIAL, (61, 62)),
          (6, "and Marcus agreed to kiss her.", SOCIAL, (63, 64)),
          (7, "Kiran kissed Marcus.", SOCIAL, (65, 66)),
          (8, "An hour earlier, Marcus had left the letter in the office", SPACE, (0, 1)),
          (9, "and gone up to the roof.", SPACE, (2, 3))]
    fig, (a1, a2) = plt.subplots(1, 2, figsize=(15, 5.2), gridspec_kw={"width_ratios": [1, 2.6], "wspace": 0.04}, sharey=True)
    for ax, lo, hi in ((a1, -0.5, 4.5), (a2, 49.5, 67)):
        for i, text, c, (s, e) in ev:
            if e <= lo or s >= hi: continue
            ax.add_patch(FancyBboxPatch((s + 0.05, -i - 0.3), e - s - 0.1, 0.6, boxstyle="round,pad=0,rounding_size=0.15",
                                        facecolor=c, alpha=0.2, edgecolor=c, lw=1.3))
        ax.set_xlim(lo, hi); ax.set_ylim(-9.7, 0.8)
        for s in ("top", "right", "left"): ax.spines[s].set_visible(False)
        ax.spines["bottom"].set_color(FAINT); ax.tick_params(colors=MUTED, left=False)
    a1.set_yticks([-i for i, *_ in ev], [f"{i}  {t}" for i, t, *_ in ev], fontsize=10, family=SANS)
    a2.annotate("", xy=(51, 0), xytext=(49.6, 0), arrowprops=dict(arrowstyle="-|>", ls="--", color=MUTED))
    a1.text(1.5, -7.1, "gap(8 → 0) ∈ [50, 70] min\n(\"an hour earlier\")", fontsize=9, color=MUTED, family=SANS)
    a2.text(56.5, 0.45, "meanwhile: during 2", fontsize=9, color=MIND, ha="center", family=SANS)
    a2.set_xlabel("minutes (timeline found by the solver, re-checked by Timed.Valid)", color=MUTED, family=SANS)
    fig.suptitle("Text → lexicon → story: events from the verbs, constraints from the adverbials  ·  theorem fromText_valid",
                 x=0.07, ha="left", fontsize=12, fontweight="bold", family=SANS, color=INK)
    fig.savefig(OUT / "12-office-from-text.png", dpi=160, bbox_inches="tight", facecolor="white")
    plt.close(fig)
    return OUT / "12-office-from-text.png"


if __name__ == "__main__":
    for f in (modules(), timeline(), gossip(), office_text()):
        print(f)
