"""The full stack, layer by layer: each Lean definition on the left, the rule it
encodes on the right, a line between them. Plus a system diagram."""
import html, pathlib, subprocess
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import proofs
from proofs import N, width, height, draw, MONO, INK, MUTED

OUT = pathlib.Path(__file__).resolve().parent / "out"
FS = 11
proofs.FS, proofs.CW, proofs.LH = FS, 0.602 * FS, 2.1 * FS
KW = ("inductive", "structure", "def", "theorem", "class", "instance", "mutual", "end", "where", "abbrev")
LEAN_C, LINK_C = "#953800", "#0969da"


def P(*premises, concl, label=""):
    """A rule: premises over a bar, conclusion below."""
    return N(concl, label, [N(p, bar=False) for p in premises])


def layer(fname, title, subtitle, items):
    """items: (lean source lines, rule node, kind) with kind 'inductive' | 'def' | 'theorem'."""
    lean_w = max(len(l) for src, _, _ in items for l in src) + 3
    rule_w = max(width(r) for _, r, _ in items) + 2
    gap = 10
    rows = [max(len(src) + 0.9, height(r) + 0.9) for src, r, _ in items]
    W, H = lean_w + gap + rule_w + 2, sum(rows) + 4.2
    fig, ax = proofs.figure(W, H)
    ax.text(0.5, H - 1.0, title, family="DejaVu Sans", fontsize=FS * 1.45, fontweight="bold", color=INK, va="center")
    ax.text(0.5, H - 2.1, subtitle, family="DejaVu Sans", fontsize=FS * 0.95, color=MUTED, va="center")
    ax.text(0.5, H - 3.2, "Lean", family=MONO, fontsize=FS * 0.9, color=MUTED, va="center")
    ax.text(lean_w + gap, H - 3.2, "rule", family=MONO, fontsize=FS * 0.9, color=MUTED, va="center")
    y = H - 3.8
    for (src, r, kind), h in zip(items, rows):
        y -= h
        top = y + h - 0.55
        for k, line in enumerate(src):
            weight = "bold" if line.lstrip().startswith(KW) else "normal"
            colour = LEAN_C if k == 0 else INK
            ax.text(0.5, top - k * 0.85, line, family=MONO, fontsize=FS * 0.86, color=colour, va="center",
                    fontweight=weight)
        ry = y + (h - height(r)) / 2
        draw(ax, r, lean_w + gap, ry)
        style = {"inductive": "-", "def": "--", "theorem": ":"}[kind]
        ax.annotate("", xy=(lean_w + gap - 0.6, ry + 0.4), xytext=(lean_w - 1.2, top),
                    arrowprops=dict(arrowstyle="-|>", ls=style, color=LINK_C, lw=1.0, alpha=0.75,
                                    connectionstyle="arc3,rad=0.0"))
        ax.text(lean_w + gap / 2 - 0.4, (top + ry + 0.4) / 2 + 0.35, kind, family=MONO, fontsize=FS * 0.7,
                color=LINK_C, ha="center", alpha=0.85)
        ax.plot([0.3, W - 0.3], [y + 0.05, y + 0.05], color="#eaeef2", lw=0.7)
    out = OUT / fname
    fig.savefig(out, dpi=150, facecolor="white")
    plt.close(fig)
    return out


def L1():
    return layer("s1-text.png", "Layer 1 · Text", "LangLib/Basic, Render, Check: a document is faithful when its leaves are the source's tokens", [
        (["inductive Tree where", "  | leaf (w : Word)"],
         P(concl="render (leaf w) = [w.form]", label="render-leaf"), "inductive"),
        (["  | node (info : NodeInfo) (kids : List Tree)", "theorem Tree.render_node :",
          "  (node i kids).render = (kids.map render).flatten"],
         P("render kᵢ = tsᵢ  (each child)", concl="render (node i [k₁…kₙ]) = ts₁ ++ … ++ tsₙ", label="render-node"), "theorem"),
        (["def check (text : String) (d : Doc) : CheckResult", "  ok := tokensMatch && badLeaves = [] && refIssues = []"],
         P("tokenize text = d.render", "∀ leaf w. isToken w.form", "∀ ref. declared, agrees",
           concl="faithful text d", label="check"), "def"),
        (["def Doc.checkRefs : RefReport", "  disagreement pos form entity expected"],
         P("w : PRON", "w.ref = e", "series(w.form) ≠ e.pron", concl="refIssue", label="agree"), "def"),
        (["  let ph := if fulls.any (·.pos < m.pos) then anaphoric",
          "            else if fulls.any (·.pos > m.pos) then cataphoric"],
         P("m pronoun → e", "full mention of e before m", concl="m anaphoric", label="phora"), "def"),
    ])


def L2():
    return layer("s2-defeasible.png", "Layer 2 · Defeasible logic", "LangLib/Story/DL: five mutually inductive relations; two theorems", [
        (["inductive Strict (T) : Lit α → Prop", "  | fact : q ∈ T.facts → Strict T q"],
         P("q ∈ F", concl="+Δ q", label="fact"), "inductive"),
        (["  | rule (r) : r ∈ T.rules → r.kind = .strict → r.head = q →", "      (∀ a ∈ r.body, Strict T a) → Strict T q"],
         P("r ∈ R strict", "head r = q", "∀a ∈ body r. +Δ a", concl="+Δ q", label="strict"), "inductive"),
        (["inductive Def (T) : Lit α → Prop", "  | rule (r) : r ∈ T.rules → r.kind ≠ .defeater → r.head = q →",
          "      (∀ a ∈ r.body, Def T a) → ¬ Strict T q.neg →", "      (∀ s ∈ T.rules, s.head = q.neg → Rebutted T q s) → Def T q"],
         P("r ∈ R, head r = q", "∀a ∈ body r. +∂ a", "¬ +Δ ~q", "∀s for ~q. Reb q s", concl="+∂ q", label="Def.rule"), "inductive"),
        (["inductive Rebutted (T) : Lit α → Rule α L → Prop", "  | beaten (t) : ... (∀ a ∈ t.body, Def T a) →",
          "      T.sup t s = true → Rebutted T q s"],
         P("t for q applicable", "t > s", concl="Reb q s", label="beaten"), "inductive"),
        (["inductive NotDef (T) : Lit α → Prop", "  | defeated (s) : ¬ Strict T q → s ∈ T.rules → s.head = q.neg →",
          "      (∀ a ∈ s.body, Def T a) → (∀ t … → Unbeaten T t s) → NotDef T q"],
         P("¬ +Δ q", "s for ~q applicable", "∀t for q. Unb t s", concl="−∂ q", label="defeated"), "inductive"),
        (["theorem coherent (T) : Def T q → ¬ NotDef T q"],
         P("+∂ q", "−∂ q", concl="⊥", label="coherent"), "theorem"),
        (["theorem Cert.sound (T) (c) (h : c.check T = true) :", "  (∀ q, (q,true) ∈ c.steps → Def T q) ∧ …"],
         P("check T c = true", "(q, +) ∈ c", concl="+∂ q", label="Cert.sound"), "theorem"),
    ])


def L3():
    return layer("s3-time.png", "Layer 3 · Time", "LangLib/World/Time: Allen relations by endpoints, durations, timelines as certificates", [
        (["def Allen.Holds : Allen → Interval → Interval → Prop", "  | before, a, b => a.e < b.s"],
         P("a.e < b.s", concl="a before b", label="before"), "def"),
        (["  | during, a, b => b.s < a.s ∧ a.e < b.e"],
         P("b.s < a.s", "a.e < b.e", concl="a during b", label="during"), "def"),
        (["theorem Interval.rel_holds (a b) : a.Proper → b.Proper →", "  (a.rel b).Holds a b",
          "theorem Allen.holds_unique : r.Holds a b → r'.Holds a b → r = r'"],
         P("a, b proper", concl="∃! r ∈ 13. r a b", label="JEPD"), "theorem"),
        (["def Metric.sat (t) : Metric → Bool", "  | .gap i j lo hi => a.e ≤ b.s && lo ≤ b.s - a.e && b.s - a.e ≤ hi"],
         P("t[i] = a", "t[j] = b", "lo ≤ b.s − a.e ≤ hi", concl="gap i j lo hi", label="gap"), "def"),
        (["def Timeline.Satisfies (t) (cs) : Prop :=", "  (∀ i ∈ t, i.Proper) ∧ ∀ c ∈ cs, c.Sat t"],
         P("∀i. proper", "∀c. ∃r ∈ c.rels. r t[c.i] t[c.j]", concl="t ⊨ cs", label="satisfies"), "def"),
    ])


def L4():
    return layer("s4-world.png", "Layer 4 · World core", "LangLib/World/Domain: composable modules, validity, stories told out of order", [
        (["class Domain (W E) where", "  ok : W → E → Bool;  step : W → E → W;  why : W → E → String",
          "instance [Domain W E₁] [Domain W E₂] : Domain W (E₁ ⊕ E₂)"],
         P("Domain W E₁", "Domain W E₂", concl="Domain W (E₁ ⊕ E₂)", label="sum"), "def"),
        (["def next (w) (e) : W := Perceive.perceive w e (Domain.step w e)"],
         P("w →ₑ w′ (step)", "witnesses of e learn", concl="next w e", label="next"), "def"),
        (["inductive Valid : W → List E → Prop", "  | nil : Valid w []"],
         P(concl="Valid w []", label="nil"), "inductive"),
        (["  | cons : Domain.ok w e = true → Invariant.holds (next w e) = true →",
          "      Valid (next w e) es → Valid w (e :: es)"],
         P("ok w e", "Inv (next w e)", "Valid (next w e) es", concl="Valid w (e :: es)", label="cons"), "inductive"),
        (["def Timed.Valid (w) (s : Timed E) : Prop :=", "  s.timeline.Satisfies s.constraints ∧ metric ∧",
          "  World.Valid w s.chrono"],
         P("timeline ⊨ constraints, metric", "Valid w (sort-by-end told)", concl="Valid w ⟨told, when⟩", label="timed"), "def"),
    ])


def L5():
    return layer("s5-modules.png", "Layer 5 · Modules", "Space, Minds, Relationships, Persona: preconditions, character, beliefs", [
        (["instance : Domain W (SpaceEv C P O) where", "  ok w | .take c o => holder w o == none && objLoc w o == loc w c"],
         P("o lies at loc c", "nobody holds o", concl="ok (take c o)", label="take"), "def"),
        (["  ok w | .act a b x => loc w a == loc w b &&", "      consented w b a x && consented w a b x"],
         P("a, b together", "(b,a,x) ∈ consent", "(a,b,x) ∈ consent", concl="ok (act a b x)", label="consent"), "def"),
        (["  ok w | .flirt a b => … && inCharacter (flirtTheory w a b) ⟨.flirts a b, true⟩",
          "theorem inCharacter_sound : inCharacter T q = true → NotDef T q.neg"],
         P("persona + bonds ⊢ −∂ ¬flirts a b", concl="ok (flirt a b)", label="in character"), "theorem"),
        (["def closure (ls) : List (BLit Φ)   -- forward chaining with Lore.rules",
          "def view (w) (c) := closure (c's atoms and denials)"],
         P("r ∈ Lore", "body r ⊆ view c", concl="head r ∈ view c", label="lore"), "def"),
        (["def hear (w) (c d) (b) : W", "  rejected := saw something b contradicts ∨ ¬consistent (add b)"],
         P("c saw b′", "b contradicts b′", concl="c rejects b from d; notes d claims b", label="seen > told"), "def"),
        (["instance : Invariant W := ⟨mindsConsistent⟩",
          "def consistent (ls) := ls.all fun x => ls.all fun y => !clash x y"],
         P("∀c. no φ, ¬φ ∈ view c", "∀c. no exclusive φ, ψ ∈ view c", concl="Inv w", label="consistent"), "def"),
    ])


def L6():
    return layer("s6-bridge.png", "Layer 6 · Bridge and lexicon", "Story/Bridge, World/Lexicon: checked text to a told story with time", [
        (["structure Clause where", "  verb; subj; obj; obls; objNoun; oblNouns; comp; embedded; advs",
          "partial def Tree.clauses …   -- VERB head child ⇒ clause"],
         P("node has head VERB v", "nsubj → s", "obj → o", concl="clause v s o …", label="clause"), "def"),
        (["def socialLex (R) : Lexicon (SocialEv C)", "  ([\"agree\"], fun c cs => do let k ← c.complement cs",
          "     return .agree (← subj) (← k.obj) (← actOf k.verb))"],
         P("clause agree s", "complement: kiss o", concl="agree s o kiss", label="lexicon"), "def"),
        (["def Lexicon.story (L) (d) : Story E", "  together := … ⟨i, sameTime, m⟩     -- \"meanwhile\""],
         P("advs(i) ∋ meanwhile", "m = previous main", concl="i sameTime m", label="meanwhile"), "def"),
        (["  metric := [.gap f m (n - n/6) (n + n/6)]    -- \"an hour earlier\""],
         P("advs(f) ∋ earlier", "amount = n min", concl="gap f m [⅚n, ⁷⁄₆n]", label="earlier"), "def"),
    ])


def system():
    def box(name, title, code, colour):
        rows = "".join(f'<tr><td align="left"><font face="DejaVu Sans Mono" point-size="9">{html.escape(l)}</font></td></tr>'
                       for l in code)
        return (f'{name} [shape=plaintext, label=<<table border="1" cellborder="0" cellspacing="0" cellpadding="4" '
                f'color="{colour}" style="rounded"><tr><td align="left"><b><font color="{colour}">{html.escape(title)}</font></b></td></tr>{rows}</table>>];')
    L = ['digraph S { rankdir=LR; bgcolor="white"; nodesep=0.35; ranksep=0.5; fontname="DejaVu Sans";',
         'edge [color="#8c959f", arrowsize=0.7, fontname="DejaVu Sans", fontsize=9, fontcolor="#6e7781"];',
         box("txt", "prose", ["Theo confided in Kiran.", "Meanwhile, Mara took the letter.", "An hour earlier, …"], "#57606a"),
         box("llm", "LLM (Opus / Sonnet / Fable)", ["prompt.md → JSON document", "retries with checker report"], "#57606a"),
         box("chk", "1 · langlib check", ["tokenize text = d.render", "refs resolve, pronouns agree", "→ faithful Doc"], "#1a7f37"),
         box("cl", "6 · Doc.clauses", ["verb, subj, obj, obls,", "complements, adverbials"], "#9a6700"),
         box("lex", "6 · Lexicon.story", ["spaceLex ++ socialLex ++ …", "told : List E", "constraints, metric"], "#9a6700"),
         box("sol", "3 · solve (untrusted)", ["difference constraints", "Bellman–Ford + search", "→ timeline"], "#0969da"),
         box("tim", "3 · Timed E", ["told, constraints, metric,", "timeline (certificate)"], "#0969da"),
         box("val", "4 · Timed.Valid w s", ["timeline ⊨ constraints, metric", "Valid w chrono", "  ok · Inv · next"], "#57606a"),
         box("mod", "5 · modules", ["Space · Minds · Relationships", "Persona · Magic · …", "ok / step / why / Perceive"], "#bf3989"),
         box("dl", "2 · defeasible logic", ["inCharacter T q = true", "  ⇒ NotDef T ¬q (Cert.sound)"], "#8250df"),
         box("thm", "theorems", ["fromText_valid : fromText.Valid start", "theo_false_belief", "kiss_needs_consent"], "#1a7f37"),
         box("fb", "feedback to the writer", ["why: \"out of character …", "  first establish …\"", "token diffs, ref issues"], "#cf222e"),
         'txt -> llm -> chk; chk -> cl [label="Doc"]; cl -> lex; lex -> sol [label="Story"]; sol -> tim; tim -> val;',
         'mod -> val [label="Domain W E"]; dl -> mod [label="persona rules"]; val -> thm [label="decide +kernel"];',
         'chk -> fb [style=dashed, label="not faithful"]; val -> fb [style=dashed, label="firstFailure"]; fb -> llm [style=dashed];',
         '{ rank=same; mod; dl; }', '}']
    out = OUT / "s0-system.png"
    subprocess.run(["dot", "-Tpng", "-Gdpi=150", "-o", str(out)], input="\n".join(L).encode(), check=True)
    return out


if __name__ == "__main__":
    for f in (system(), L1(), L2(), L3(), L4(), L5(), L6()):
        print(f)
