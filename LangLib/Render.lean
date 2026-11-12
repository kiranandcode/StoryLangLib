import LangLib.Basic
import LangLib.Token

/-!
# Rendering

A tree renders to the list of its leaves' forms, left to right.
-/

namespace LangLib

mutual
def Tree.render : Tree → List String
  | .leaf w => [w.form]
  | .node _ kids => Tree.renderList kids

def Tree.renderList : List Tree → List String
  | [] => []
  | t :: ts => t.render ++ Tree.renderList ts
end

@[simp] theorem Tree.render_leaf (w : Word) : (Tree.leaf w).render = [w.form] := by
  simp [Tree.render]

@[simp] theorem Tree.renderList_cons (t : Tree) (ts : List Tree) :
    Tree.renderList (t :: ts) = t.render ++ Tree.renderList ts := by
  simp [Tree.renderList]

theorem Tree.render_node (i : NodeInfo) (kids : List Tree) :
    (Tree.node i kids).render = (kids.map Tree.render).flatten := by
  simp only [Tree.render]
  induction kids with
  | nil => simp [Tree.renderList]
  | cons t ts ih => simp [ih]

/-- Leaves, left to right. -/
partial def Tree.leaves : Tree → List Word
  | .leaf w => [w]
  | .node _ kids => kids.flatMap Tree.leaves

def Sentence.render (s : Sentence) : List String := s.tree.render

def Doc.render (d : Doc) : List String := d.sentences.flatMap Sentence.render

def Doc.toText (d : Doc) : String := detokenize d.render

/-- Bracketed one-line view, e.g. `[S [NP:nsubj She/PRON] [VP ran/VERB]]`. -/
partial def Tree.pretty : Tree → String
  | .leaf w => s!"{w.form}/{w.upos.name}"
  | .node i kids =>
    let role := match i.role with | some r => s!":{r.name}" | none => ""
    let ref := match i.ref with | some e => s!"@{e}" | none => ""
    let spk := match i.speaker with | some e => s!"<{e}>" | none => ""
    s!"[{i.cat.name}{role}{ref}{spk} " ++ " ".intercalate (kids.map Tree.pretty) ++ "]"

end LangLib
