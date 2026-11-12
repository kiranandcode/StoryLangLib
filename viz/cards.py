"""Rule cards: each inductive relation with its notation and reading, then its
rules one per row (rule on paper | Lean constructor), with theorems shaded in
among them. No arrows: a row is read left to right."""
import pathlib
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch
import proofs
from proofs import N, width, height, draw, MONO, INK, MUTED

OUT = pathlib.Path(__file__).resolve().parent / "out"
SANS = "DejaVu Sans"
FS = 11
proofs.FS, proofs.CW, proofs.LH = FS, 0.602 * FS, 2.1 * FS
THM_BG, HEAD_BG, RULE_C, LEAN_C = "#fff8c5", "#f6f8fa", "#0969da", "#57606a"


def P(*premises, concl, label=""):
    return N(concl, label, [N(p, bar=False) for p in premises])


def card(fname, title, items):
    """items: ("rel", notation, reading, lean name) | ("rule", name, rule node, lean lines)
    | ("thm", name, rule node, lean lines) | ("note", text)."""
    rule_w = max([width(it[2]) for it in items if it[0] in ("rule", "thm")] + [30]) + 2
    lean_w = max([len(l) for it in items if it[0] in ("rule", "thm") for l in it[3]] + [30]) + 2
    name_w = 16
    W = name_w + rule_w + lean_w + 6

    def h(it):
        if it[0] == "rel": return 2.6
        if it[0] == "note": return 1.4
        return max(height(it[2]) + 0.8, len(it[3]) * 0.9 + 0.8)

    H = sum(h(it) for it in items) + 2.2
    fig, ax = proofs.figure(W, H)
    ax.text(0.6, H - 1.0, title, family=SANS, fontsize=FS * 1.5, fontweight="bold", color=INK, va="center")
    y = H - 2.0
    n = 0
    for it in items:
        hh = h(it)
        y -= hh
        if it[0] == "rel":
            _, notation, reading, lean = it
            ax.add_patch(FancyBboxPatch((0.4, y + 0.25), W - 0.8, hh - 0.4, boxstyle="round,pad=0,rounding_size=0.3",
                                        facecolor=HEAD_BG, edgecolor="#d0d7de", lw=0.8))
            ax.text(1.0, y + hh / 2 + 0.35, notation, family=MONO, fontsize=FS * 1.35, color=RULE_C,
                    fontweight="bold", va="center")
            ax.text(1.0, y + hh / 2 - 0.55, reading, family=SANS, fontsize=FS * 0.95, color=INK, va="center")
            ax.text(W - 1.0, y + hh / 2, lean, family=MONO, fontsize=FS * 0.85, color=LEAN_C, va="center", ha="right")
            continue
        if it[0] == "note":
            ax.text(1.0, y + hh / 2, it[1], family=SANS, fontsize=FS * 0.9, color=MUTED, va="center", style="italic")
            continue
        kind, name, rule, lean = it
        n += 1
        if kind == "thm":
            ax.add_patch(FancyBboxPatch((0.4, y + 0.1), W - 0.8, hh - 0.2, boxstyle="round,pad=0,rounding_size=0.25",
                                        facecolor=THM_BG, edgecolor="#d4a72c", lw=0.8))
        tag = "theorem" if kind == "thm" else "rule"
        ax.text(1.0, y + hh / 2 + 0.3, f"({n})", family=MONO, fontsize=FS * 0.85, color=MUTED, va="center")
        ax.text(1.0, y + hh / 2 - 0.45, name, family=MONO, fontsize=FS * 0.85,
                color="#9a6700" if kind == "thm" else INK, va="center", fontweight="bold")
        ax.text(1.0, y + hh / 2 - 1.2, tag, family=SANS, fontsize=FS * 0.7, color=MUTED, va="center")
        draw(ax, rule, name_w, y + (hh - height(rule)) / 2)
        lx = name_w + rule_w + 3
        ax.plot([lx - 1.5, lx - 1.5], [y + 0.3, y + hh - 0.3], color="#d0d7de", lw=0.8)
        top = y + hh / 2 + (len(lean) - 1) * 0.45
        for k, line in enumerate(lean):
            ax.text(lx, top - k * 0.9, line, family=MONO, fontsize=FS * 0.8, color=LEAN_C, va="center")
    out = OUT / fname
    fig.savefig(out, dpi=150, facecolor="white")
    plt.close(fig)
    return out


def key():
    rows = [("T ⊢+Δ q", "Strict T q", "in theory T, q follows by strict rules alone"),
            ("T ⊢+∂ q", "Def T q", "in T, q is defeasibly provable (plausible)"),
            ("T ⊢−∂ q", "NotDef T q", "in T, q is demonstrably not defeasibly provable"),
            ("T ⊢ s ⇏ q", "Rebutted T q s", "rule s's attack on q fails"),
            ("T ⊢ r ✗", "Discarded T r", "some premise of rule r is refuted"),
            ("T ⊢ t ⊁ s", "Unbeaten T t s", "rule t does not override rule s"),
            ("w |= es", "Valid w es", "from state w, the events es make a valid story"),
            ("a ⟨r⟩ b", "Allen.Holds r a b", "interval a stands in Allen relation r to b"),
            ("t |= cs", "Timeline.Satisfies t cs", "timeline t meets every 'when' constraint"),
            ("view w c", "Mind.view", "what c believes now (consistent, by theorem)"),
            ("viewAt w c t", "Mind.viewAt", "what c now believes held at time t"),
            ("viewAsOf w c s", "Mind.viewAsOf", "what c believed at time s (as they remember it)"),
            ("~q", "Lit.neg q", "the opposite of q"),
            ("t > s", "T.sup t s = true", "rule t overrides rule s (e.g. it serves a value the agent ranks higher)")]
    W, H = 118, len(rows) * 1.5 + 3.5
    fig, ax = proofs.figure(W, H)
    ax.text(0.6, H - 1.0, "Notation key", family=SANS, fontsize=FS * 1.5, fontweight="bold", color=INK, va="center")
    for i, (nota, lean, reading) in enumerate(rows):
        y = H - 2.6 - i * 1.5
        if i % 2 == 0:
            ax.add_patch(FancyBboxPatch((0.4, y - 0.65), W - 0.8, 1.3, boxstyle="square,pad=0", facecolor=HEAD_BG, lw=0))
        ax.text(1.0, y, nota, family=MONO, fontsize=FS * 1.2, color=RULE_C, va="center", fontweight="bold")
        ax.text(22, y, lean, family=MONO, fontsize=FS * 0.9, color=LEAN_C, va="center")
        ax.text(52, y, reading, family=SANS, fontsize=FS * 0.95, color=INK, va="center")
    out = OUT / "c0-key.png"
    fig.savefig(out, dpi=150, facecolor="white")
    plt.close(fig)
    return out


def dl():
    return card("c1-defeasible.png", "Defeasible logic (LangLib/Story/DL.lean)", [
        ("note", "T = ⟨F, R, >⟩: facts, rules (body ⇒ head), and which rule overrides which. See the primer card."),
        ("rel", "T ⊢+Δ q", "q follows from the facts by strict rules alone", "inductive Strict"),
        ("rule", "fact", P("q ∈ F   (F = T.facts)", concl="T ⊢+Δ q"), ["| fact : q ∈ T.facts →", "    T ⊢+Δ q"]),
        ("rule", "strict", P("r ∈ R (= T.rules), strict", "head r = q (its conclusion)", "∀a ∈ body r. T ⊢+Δ a", concl="T ⊢+Δ q"),
         ["| rule r : r ∈ T.rules → r.kind = .strict →", "    r.head = q → (∀ a ∈ r.body, T ⊢+Δ a) →", "    T ⊢+Δ q"]),
        ("rel", "T ⊢+∂ q", "q is defeasibly provable: some rule supports it and every attack on it fails", "inductive Def"),
        ("rule", "Def.strict", P("T ⊢+Δ q", concl="T ⊢+∂ q"), ["| strict : (T ⊢+Δ q) → T ⊢+∂ q"]),
        ("rule", "Def.rule", P("r ∈ R, head r = q, r not a defeater", "∀a ∈ body r. T ⊢+∂ a", "T ⊬+Δ ~q",
                               "∀s with head ~q. T ⊢ s ⇏ q", concl="T ⊢+∂ q"),
         ["| rule r : r ∈ T.rules → r.kind ≠ .defeater →", "    r.head = q → (∀ a ∈ r.body, T ⊢+∂ a) →",
          "    (¬ T ⊢+Δ q.neg) →", "    (∀ s ∈ T.rules, s.head = q.neg → T ⊢ s ⇏ q) →", "    T ⊢+∂ q"]),
        ("rel", "T ⊢ s ⇏ q", "the attack of rule s on q fails", "inductive Rebutted"),
        ("rule", "discarded", P("T ⊢ s ✗", concl="T ⊢ s ⇏ q"), ["| discarded : (T ⊢ s ✗) → T ⊢ s ⇏ q"]),
        ("rule", "beaten", P("t for q, not a defeater", "∀a ∈ body t. T ⊢+∂ a", "t > s", concl="T ⊢ s ⇏ q"),
         ["| beaten t : t ∈ T.rules → t.kind ≠ .defeater →", "    t.head = q → (∀ a ∈ t.body, T ⊢+∂ a) →",
          "    T.sup t s = true → T ⊢ s ⇏ q"]),
        ("rel", "T ⊢ r ✗", "rule r is out of play: one of its premises is refuted", "inductive Discarded"),
        ("rule", "mk", P("a ∈ body r", "T ⊢−∂ a", concl="T ⊢ r ✗"), ["| mk a : a ∈ r.body → (T ⊢−∂ a) →", "    T ⊢ r ✗"]),
        ("rel", "T ⊢−∂ q", "q is demonstrably not provable: three ways it can fail", "inductive NotDef"),
        ("rule", "unsupported", P("T ⊬+Δ q", "∀r for q. T ⊢ r ✗", concl="T ⊢−∂ q"),
         ["| unsupported : (¬ T ⊢+Δ q) →", "    (∀ r ∈ T.rules, r.kind ≠ .defeater →", "      r.head = q → T ⊢ r ✗) → T ⊢−∂ q"]),
        ("rule", "contradicted", P("T ⊬+Δ q", "T ⊢+Δ ~q", concl="T ⊢−∂ q"),
         ["| contradicted : (¬ T ⊢+Δ q) →", "    (T ⊢+Δ q.neg) → T ⊢−∂ q"]),
        ("rule", "defeated", P("T ⊬+Δ q", "s for ~q applies", "∀t for q. T ⊢ t ⊁ s", concl="T ⊢−∂ q"),
         ["| defeated s : (¬ T ⊢+Δ q) → s ∈ T.rules →", "    s.head = q.neg → (∀ a ∈ s.body, T ⊢+∂ a) →",
          "    (∀ t ∈ T.rules, … → T ⊢ t ⊁ s) → T ⊢−∂ q"]),
        ("thm", "coherent", P("T ⊢+∂ q", "T ⊢−∂ q", concl="⊥"),
         ["theorem coherent (T) :", "  (T ⊢+∂ q) → ¬ T ⊢−∂ q"]),
        ("rel", "T ⊢ t ⊁ s", "rule t (for q) does not override the attacker s", "inductive Unbeaten"),
        ("rule", "discarded", P("T ⊢ t ✗", concl="T ⊢ t ⊁ s"), ["| discarded : (T ⊢ t ✗) → T ⊢ t ⊁ s"]),
        ("rule", "notSup", P("not t > s", concl="T ⊢ t ⊁ s"), ["| notSup : T.sup t s = false → T ⊢ t ⊁ s"]),
        ("note", "The relations are found by an untrusted evaluator; the certificate it returns is checked by a boolean function whose soundness is proved:"),
        ("thm", "Cert.sound", P("check T c = true", "(q, +) ∈ c", concl="T ⊢+∂ q"),
         ["theorem Cert.sound (T c) (h : c.check T = true) :", "  (∀ q, (q, true) ∈ c.steps → T ⊢+∂ q) ∧",
          "  (∀ q, (q, false) ∈ c.steps → T ⊢−∂ q)"]),
    ])


def stories():
    return card("c2-stories.png", "Stories and time (LangLib/World/Domain.lean, Time.lean)", [
        ("rel", "w |= es", "from state w, the events es make a valid story", "inductive Valid"),
        ("rule", "nil", P(concl="w |= []"), ["| nil : w |= []"]),
        ("rule", "cons", P("ok w e", "Inv (next w e)", "next w e |= es", concl="w |= e :: es"),
         ["| cons : Domain.ok w e = true →", "    Invariant.holds (next w e) = true →", "    (next w e |= es) → w |= e :: es"]),
        ("note", "next w e = tick (perceive w e (step w e)): the module's effect, then what witnesses see, then the clock."),
        ("thm", "validB_iff", P("validB w es = true", concl="w |= es"),
         ["theorem validB_iff (w es) :", "  validB w es = true ↔ w |= es"]),
        ("rel", "a ⟨r⟩ b", "interval a stands in Allen relation r to interval b (by endpoints)", "def Allen.Holds"),
        ("rule", "before", P("a.e < b.s", concl="a ⟨before⟩ b"), ["| before, a, b => a.e < b.s"]),
        ("rule", "during", P("b.s < a.s", "a.e < b.e", concl="a ⟨during⟩ b"), ["| during, a, b => b.s < a.s ∧ a.e < b.e"]),
        ("thm", "JEPD", P("a, b proper", concl="exactly one r: a ⟨r⟩ b"),
         ["theorem Interval.rel_holds : (a.rel b).Holds a b", "theorem Allen.holds_unique :", "  r.Holds a b → r'.Holds a b → r = r'"]),
        ("rel", "t |= cs", "timeline t (endpoints for each event) meets every constraint", "def Timeline.Satisfies"),
        ("rule", "satisfies", P("∀i. t[i] proper", "∀c ∈ cs. ∃r ∈ c.rels. t[c.i] ⟨r⟩ t[c.j]", concl="t |= cs"),
         ["(∀ i ∈ t, i.Proper) ∧ ∀ c ∈ cs, c.Sat t"]),
        ("rule", "gap", P("t[i] = a", "t[j] = b", "lo ≤ b.s − a.e ≤ hi", concl="t |= gap i j lo hi"),
         ["| .gap i j lo hi => a.e ≤ b.s && lo ≤ b.s - a.e", "                  && b.s - a.e ≤ hi"]),
        ("rule", "timed", P("t |= constraints", "t |= durations", "w |= (told, sorted by when each ends)", concl="Timed.Valid w s"),
         ["def Timed.Valid w s := s.timeline.Satisfies … ∧", "  metric.all (sat ·) ∧ World.Valid w s.chrono"]),
    ])


def minds():
    return card("c3-minds.png", "Minds: evidence, attitudes, views over time (LangLib/World/Mind.lean)", [
        ("rel", "strength c e l", "how strongly c takes evidence e for literal l: a prior plus named reasons", "def strength"),
        ("rule", "strength", P("prior(e) = p", "reasons(c, e, l) = r₁ … rₖ", concl="strength = p + Σ rᵢ"),
         ["def strength w c e l :=", "  ((reasonsFor w c e l).map (·.2)).sum", "-- seen 5, told 3, rumour 1;",
          "-- trust ±1, topic, gullible ±1 …"]),
        ("rule", "attitude", P("s = strength c e l", "s ≥ accept(c)", "c not stubborn", concl="radical"),
         ["if s ≥ acceptAt c then", "  (if stubborn c then .conservative else .radical)",
          "else if s ≥ acceptAt c - 1 then .conservative", "else .note   -- only 'd says l' is kept"]),
        ("rel", "admit ls", "the greedy consistent prefix: keep each literal iff it stays consistent", "def admit"),
        ("rule", "keep", P("closure(kept ++ [l]) consistent", concl="l kept"),
         ["ls.foldl (fun kept l =>", "  if consistent (closure (kept ++ [l]))", "  then kept ++ [l] else kept) []"]),
        ("rule", "skip", P("closure(kept ++ [l]) inconsistent", concl="l outranked (stays in the base)"),
         ["-- nothing is deleted from beliefs w c"]),
        ("thm", "view_consistent", P("the lore alone is consistent", concl="view w c is consistent"),
         ["theorem view_consistent (w c)", "  (h : consistent (closure []) = true) :", "  consistent (view w c) = true"]),
        ("rel", "view / viewAt / viewAsOf", "now, about time t, and as remembered from time s", "def view, viewAt, viewAsOf"),
        ("rule", "stale", P("h, h′ changeable", "h′ newer, adopted", "h′ contradicts h", concl="h out of the present view"),
         ["def stale hs h := isFluent h && hs.any fun h' =>", "  isFluent h' && h'.up != .note &&",
          "  h'.about > h.about && clash h h'"]),
        ("rule", "viewAt", P("items about times ≤ t", concl="what c now believes held at t"),
         ["def viewAt w c t := closure (admit (lits", "  ((beliefs w c).filter (·.about ≤ t))))"]),
        ("rule", "settled", P("l ∈ viewAt c t", "l permanent", "l concluded, not stated", concl="l ∈ view c"),
         ["settled := times.flatMap fun t => (viewAt w c t)", "  .filter fun l => !fluent l.1 && !base.contains l"]),
        ("rule", "viewAsOf", P("items learned at times ≤ s", concl="what c believed at s"),
         ["def viewAsOf w c s := closure (admit (lits", "  ((beliefs w c).filter (·.heard ≤ s))))"]),
        ("rel", "events", "how minds change", "instance Domain W (MindEv C Φ)"),
        ("rule", "realise", P("l true", "l ∈ closure(view c)", concl="ok (realise c l)"),
         ["| .realise c l => truthLit w l &&", "    (closure (view w c)).contains l"]),
        ("rule", "betrayal", P("c perceives l′", "d told c l", "l clashes with view c", concl="trust(c→d) − 1, once"),
         ["learn …: liars := reports from d whose", "  literal clashes with the new view;",
          "  mark caught; Credence.onBetrayal w c d"]),
    ])


if __name__ == "__main__":
    for f in (key(), dl(), stories(), minds()):
        print(f)


def doc(fname, title, blocks, W=112):
    """blocks: (kind, text): 'h' heading, 'p' prose, 'm' monospace line, 'gap'."""
    H = 2.5 + sum({"h": 1.9, "p": 1.15, "m": 1.1, "gap": 0.6}[k] for k, _ in blocks)
    fig, ax = proofs.figure(W, H)
    ax.text(0.6, H - 1.1, title, family=SANS, fontsize=FS * 1.5, fontweight="bold", color=INK, va="center")
    y = H - 2.4
    for k, t in blocks:
        if k == "h":
            y -= 1.0
            ax.text(0.6, y, t, family=SANS, fontsize=FS * 1.15, fontweight="bold", color=RULE_C, va="center")
            y -= 0.9
        elif k == "p":
            ax.text(1.2, y, t, family=SANS, fontsize=FS * 0.98, color=INK, va="center"); y -= 1.15
        elif k == "m":
            ax.text(2.0, y, t, family=MONO, fontsize=FS * 0.95, color=INK, va="center"); y -= 1.1
        else:
            y -= 0.6
    out = OUT / fname
    fig.savefig(out, dpi=150, facecolor="white")
    plt.close(fig)
    return out


def primer():
    return doc("c1a-primer.png", "Before the rules: what T, F, R, head, strict, defeater and 'defeasibly' mean", [
        ("h", "A theory T is a small database:  T = ⟨ F, R, > ⟩   (Lean: T.facts, T.rules, T.sup)"),
        ("p", "F   facts: things simply given.   e.g. timid(Kiran), ally(Kiran, Mara), threatens(guard, Mara)"),
        ("p", "R   rules: each rule r has premises  body r  and a conclusion  head r."),
        ("p", ">   which rule overrides which. In stories it comes from the character's values: loyalty ≻ safety makes"),
        ("p", "     a loyalty rule override a safety rule. Strict rules override everything."),
        ("h", "Three kinds of rule (r.kind)"),
        ("m", "strict       body → head    like logical implication; never overridden"),
        ("m", "                            gagged(k) → ¬shouts(k, g)"),
        ("m", "defeasible   body ⇒ head    'normally': holds unless something overrides it"),
        ("m", "                            timid(k) ⇒ ¬shouts(k, g)          [safety]"),
        ("m", "                            threatens(g,m), ally(k,m), near(k,m) ⇒ shouts(k, g)   [loyalty]"),
        ("m", "defeater     body ⇝ head    can only BLOCK the opposite conclusion; never proves head by itself"),
        ("m", "                            drunk(k) ⇝ shouts(k, g)   (a drunk timid person might shout)"),
        ("h", "Three judgements, each a derivation (a proof tree built from the rules on the next card)"),
        ("m", "T ⊢+Δ q    q follows from F by strict rules only: certain, can never be withdrawn"),
        ("m", "T ⊢+∂ q    q is defeasibly provable: a derivation that may use 'normally' rules, in which every"),
        ("m", "           rule arguing for ~q is beaten or out of play"),
        ("m", "T ⊢−∂ q    there is provably no such derivation"),
        ("m", "T ⊬+Δ q    short for ¬(T ⊢+Δ q);   ~q is the opposite literal (q negated)"),
        ("p", "'Defeasibly' = 'by default, until defeated': adding facts can withdraw a conclusion (non-monotonic)."),
        ("p", "Timid Kiran at the market: T ⊢+∂ ¬shouts.  Add threatens(guard, Mara):  T′ ⊢+∂ shouts.  Add only drunk(k):  neither."),
    ])


def example():
    k = "shouts(k,g)"
    return card("c1b-example.png", "Worked example: why  T ⊢+∂ shouts(k,g)  at the gate (k = Kiran, m = Mara, g = guard)", [
        ("rel", "T = ⟨F, R, >⟩", "F = {timid(k), ally(k,m), near(k,m), threatens(g,m)}    > : protect > timidQuiet (loyalty ≻ safety)",
         "Scene.shoutTheory"),
        ("note", "R = { timidQuiet: timid(k) ⇒ ¬shouts [safety],  protect: threatens(g,m), ally(k,m), near(k,m) ⇒ shouts [loyalty],  gagged: gagged(k) → ¬shouts,  drink: drunk(k) ⇝ shouts }"),
        ("rule", "facts", P("threatens(g,m) ∈ F", concl="T ⊢+Δ threatens(g,m)"),
         ["Strict.fact", "(same for ally(k,m), near(k,m), timid(k))"]),
        ("rule", "lift", P("T ⊢+Δ threatens(g,m)", concl="T ⊢+∂ threatens(g,m)"), ["Def.strict"]),
        ("rule", "no gag", P("gagged(k) ∉ F", "no rule concludes gagged(k)", "T ⊬+Δ gagged(k)", concl="T ⊢−∂ gagged(k)"),
         ["NotDef.unsupported"]),
        ("rule", "gag rule out", P("gagged(k) ∈ body gagged", "T ⊢−∂ gagged(k)", concl="T ⊢ gagged ✗"), ["Discarded.mk"]),
        ("rule", "attack 1 fails", P("T ⊢ gagged ✗", concl=f"T ⊢ gagged ⇏ {k}"), ["Rebutted.discarded"]),
        ("rule", "attack 2 fails", P("protect applies (its body is +∂)", "protect > timidQuiet", concl=f"T ⊢ timidQuiet ⇏ {k}"),
         ["Rebutted.beaten  (t := protect)"]),
        ("rule", "conclusion", P("protect ∈ R, head = shouts", "body all +∂", f"T ⊬+Δ ¬{k}", "both attacks fail", concl=f"T ⊢+∂ {k}"),
         ["Def.rule  (r := protect)"]),
        ("thm", "so", P(f"T ⊢+∂ {k}", concl=f"¬ T ⊢−∂ {k}"), ["coherent: it is not also refuted"]),
        ("note", "At the market there is no threats(merchant, m): protect is out of play (✗), timidQuiet applies and nothing overrides it,"),
        ("rule", "market", P("timidQuiet applies", "protect: T ⊢ protect ⊁ timidQuiet (it is ✗)", f"T ⊬+Δ {k}", concl=f"T ⊢−∂ {k}"),
         ["NotDef.defeated  (s := timidQuiet)", "→ the shout is out of character"]),
    ])


def unknowns_dialogue_goals():
    return card("c4-dialogue-goals.png", "Unknowns, dialogue, goals (World/Domain, Space, Dialogue, Goals)", [
        ("rel", "ok3 w e ∈ {yes, no, unknown}", "three-valued preconditions: what the text never said is unknown, not false", "Domain.ok3"),
        ("rule", "and", P("a = no or b = no", concl="a ∧ b = no"), ["Tri.and: no wins, then unknown, then yes"]),
        ("rule", "together3", P("loc a or loc b unknown", concl="together3 a b = unknown"),
         ["def together3 w a b := if locKnown a && locKnown b", "  then ofBool (loc a == loc b) else .unknown"]),
        ("rule", "assume", P("ok3 w e = unknown", concl="step assumes it: meet / meetObj"),
         ["-- 'Mara took the letter' puts Mara where it was", "def meet w a b := … assumeAt w a b"]),
        ("rel", "w |=? es", "plausible under assumptions: no event is ruled out", "inductive Plausible"),
        ("rule", "cons", P("ok3 w e ≠ no", "Inv (next w e)", "next w e |=? es", concl="w |=? e :: es"),
         ["| cons : Domain.ok3 w e ≠ .no →", "    Invariant.holds (next w e) = true →", "    (next w e |=? es) → w |=? e :: es"]),
        ("thm", "plausibleB_iff", P("plausibleB w es = true", concl="w |=? es"), ["theorem plausibleB_iff : plausibleB w es = true ↔ w |=? es"]),
        ("note", "assumptions w es lists every event that needed one, with why (e.g. 'assumes they were together')."),
        ("rel", "dialogue", "speech acts beyond telling", "inductive DialogueEv"),
        ("rule", "answer", P("c asked d about φ (open)", "l ∈ view d", "together", concl="ok (answer d c l); c learns l (told d)"),
         ["| .answer d c l => together3 ∧", "    isOpen w c d l.1 && (view w d).contains l"]),
        ("rule", "hint", P("l ∈ view c", "together", concl="d learns l (relayed c: weaker)"), ["| .hint c d l => learn d l (.relayed c)"]),
        ("rule", "sarcasm", P("c says ~l meaning l", "rapport(d, c)", concl="d learns l"),
         ["let heard := if Rapport.getsIt w d c then l else flip l", "-- no rapport: d (and bystanders) take ~l"]),
        ("rule", "promise", P("c promises d l", concl="l is a goal of c; kept iff l true"), ["promises w := (c, d, l) :: …", "def kept w := (promises w).filter (truthLit w ·.2.2)"]),
        ("rel", "motives", "why each action happened (IPOCL / Sabre: explained actions)", "def motives"),
        ("rule", "by plan", P("p ∈ plans c", "e = first step of p", concl="e explained (p advances)"),
         ["let byPlan := (plans w c).find? fun p =>", "  p.steps.head? = some e"]),
        ("rule", "by goal", P("g ∈ effects e", "g ∈ goals c ∪ promises c", concl="e explained"),
         ["(Purpose.effects w e).find? (goalsOf w c).contains"]),
        ("rule", "else", P("agent c", "no plan step, no goal served", concl="e unmotivated (reported)"), ["def unmotivated w es := … .none"]),
        ("rule", "planWorks", P("w |=? steps p", "goal p true after them", concl="planWorks w p"),
         ["plausibleB w steps && truth (run w steps) goal"]),
    ])
