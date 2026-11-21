# The Rules view: an argument's inferences as informal rules

`studio/web/src/Rules.tsx` draws each inference of an argument reading
(`langlib rules <dir>`, LangLib/Studio/RulesView.lean; stories through
`studio/rules_story.py`) as a natural-deduction rule on a card: verbatim
premises one per row above a line, each with what it rests on in a left
column (a tag chip, or the rule that concludes it), the conclusion below, the
scheme and kind at the right end of the line (solid strict, dashed
defeasible, dotted while no scheme has been read), and the grounded label in
the card's header. The tree is an outline: the conclusion's card first, the
rules its premises rest on indented under it on a rail, each folded to one
line until opened. A first version stacked sub-rules above their premises
side by side, proof-tree style; with a root of twelve premises that read as
a cramped grid, so it was replaced. The same component runs in the
Studio (a Rules tab beside Argument; deslop sides and the Death Note arc under
"arguments (rules only)" in the picker) and in the deslop UI (a Rules tab,
from the bundle `npm run build:rules` writes to `tools/house/deslop_ui/rules-view/`).
Data: `GET /api/rules?doc=…` and `/api/rules/md?doc=…` (markdown,
`tools/house/rules_md.py`) in the Studio; `/api/rules?id=…&side=…` in deslop.

What the layout rests on, from `docs/ui-visualisation-evidence.md`:

- **Text beside the tree, linked by hover.** Spatial contiguity is the
  best-replicated result there (Ginns 2006, d = 0.72; Schroeder & Cenkci 2018,
  g = 0.63), and colour-linking text to the parts of a diagram reduces split
  attention (Kalyuga et al. 1999). So the source text sits next to the rules,
  and hovering a quote highlights that stretch in its paragraph instead of
  repeating the paragraph in the rule.
- **A top-down tree, no drawn attack edges.** Crossings are the aesthetic that
  matters most and edge bundling hurts path tracing (Purchase 1997; McGee &
  Dingliana 2012); top-down trees read well (Burch et al. 2011). Sub-rules
  sit under the rule they support, on an indented rail, so support needs no
  edges at all, and
  attacks, which would cross the tree, are a margin list on each rule whose
  links scroll to and flash the other end. This also survives any wrapping.
- **Second channel for the line.** Solid against dashed carries strict against
  defeasible (Holten & van Wijk 2009 recommend a second, non-hue channel), and
  the line is drawn as a gradient so its dashes stay legible at any width.
- **Labels.** Grounded semantics as the default (Cramer & Guillaume 2019, about
  75–83% agreement with lay judgement), three labels each with a text badge,
  UNDEC by a dashed outline rather than a third saturated hue. A rule that is
  IN because its attackers are OUT says "reinstated" (Rahwan et al. 2010
  found readers only partly restore confidence otherwise).
- **Collapsed by default, filtered on demand.** Reading a map does not raise
  comprehension (Dwyer et al. 2010), and unfiltered views cost effort without
  gaining accuracy (Huang et al. 2009): sub-rules below the first level are
  folded, and critical questions, thin-support reasons and attacks live in the
  detail panel of the one rule clicked.
- **Tags by strength, not by kind.** Chips for the authors' word, hedges and
  promises are drawn in the warning colour, the rest neutral: two classes
  rather than six hues (Healey 1996), and the distinction the thin-support
  check cares about.

Unclassified inferences (`infer` moves without a `rule` field) come from
`studio/rules_docs.py`, with the sentence a move points at (`s`) as the quote.
