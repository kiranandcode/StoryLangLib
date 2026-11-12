import Lean.Data.Json
import LangLib.Basic
import LangLib.Token
import LangLib.Render
import LangLib.Diff
import LangLib.Refs
import LangLib.Json

/-!
# Faithfulness check

`check text doc` is the gate an LLM's encoding must pass:

1. every leaf is exactly one token;
2. the rendered tokens equal `tokenize text` (otherwise the edits are listed);
3. the reference layer is well formed (`Doc.checkRefs`).
-/

namespace LangLib
open Lean

structure CheckResult where
  tokensMatch : Bool
  srcTokens : Nat
  treeTokens : Nat
  badLeaves : List String
  edits : List Edit
  refs : RefReport
  stats : List (String × Nat)

def CheckResult.ok (r : CheckResult) : Bool :=
  r.tokensMatch && r.badLeaves.isEmpty && r.refs.issues.isEmpty

private partial def countNodes : Tree → Nat × Nat × Nat
  | .leaf _ => (0, 1, 1)
  | .node _ kids =>
    kids.foldl (fun (n, l, d) k =>
      let (n', l', d') := countNodes k
      (n + n', l + l', max d (d' + 1))) (1, 0, 1)

def check (text : String) (d : Doc) : CheckResult :=
  let src := (tokenize text).toArray
  let got := d.render.toArray
  let leaves := d.sentences.flatMap (·.tree.leaves)
  let bad := (leaves.filter fun w => !isToken w.form).map (·.form)
  let edits := tokenDiff src got
  let refs := d.checkRefs
  let (nodes, _, depth) := d.sentences.foldl (fun (n, l, dp) s =>
    let (n', l', d') := countNodes s.tree
    (n + n', l + l', max dp d')) (0, 0, 0)
  { tokensMatch := edits.isEmpty, srcTokens := src.size, treeTokens := got.size,
    badLeaves := bad, edits, refs,
    stats := [("sentences", d.sentences.length), ("nodes", nodes), ("maxDepth", depth),
              ("entities", d.entities.length), ("mentions", refs.mentions)] }

def CheckResult.toJson (text : String) (r : CheckResult) (maxEdits : Nat := 12) : Json :=
  let src := (tokenize text).toArray
  Json.mkObj [
    ("ok", r.ok),
    ("tokensMatch", r.tokensMatch),
    ("srcTokens", r.srcTokens),
    ("treeTokens", r.treeTokens),
    ("editCount", r.edits.length),
    ("edits", Json.arr ((r.edits.take maxEdits).map fun e => Json.str (e.describe src)).toArray),
    ("badLeaves", Json.arr (r.badLeaves.map Json.str).toArray),
    ("refIssues", Json.arr (r.refs.issues.map fun i => Json.str i.describe).toArray),
    ("pronouns", Json.arr (r.refs.pronouns.map fun (m, p) =>
      Json.mkObj [("pos", m.pos), ("form", m.text), ("entity", m.entity),
                  ("phora", p.name)]).toArray),
    ("stats", Json.mkObj (r.stats.map fun (k, v) => (k, Json.num v)))]

end LangLib
