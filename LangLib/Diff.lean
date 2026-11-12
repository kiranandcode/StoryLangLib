/-!
# Token diff

Aligns the source tokens with the rendered tokens (edit distance, unit costs)
and reports the edits, so a model can be told exactly which words it dropped,
invented or changed.
-/

namespace LangLib

inductive Edit where
  /-- token of the source text that the tree leaves out -/
  | missing (at_ : Nat) (tok : String)
  /-- token of the tree that is not in the source -/
  | extra (at_ : Nat) (tok : String)
  /-- source token `src` rendered as `got` -/
  | changed (at_ : Nat) (src got : String)
  deriving Repr, BEq

def Edit.describe (ts : Array String) : Edit → String
  | .missing i t => s!"token {i} \"{t}\" is missing{ctx i}"
  | .extra i t => s!"extra token \"{t}\" inserted before source token {i}{ctx i}"
  | .changed i s g => s!"token {i} \"{s}\" was written as \"{g}\"{ctx i}"
where
  ctx (i : Nat) : String :=
    let lo := i - min i 4
    let win := (ts.extract lo (i + 4)).toList
    s!" (near: {" ".intercalate win})"

/-- Edits turning `src` into `got`, in source order. Falls back to the first
mismatch alone when the inputs are too large to align. -/
def tokenDiff (src got : Array String) (limit : Nat := 4000000) : List Edit := Id.run do
  let n := src.size
  let m := got.size
  if n * m > limit then
    let mut i := 0
    while i < n && i < m && src[i]! == got[i]! do i := i + 1
    if i == n && i == m then return []
    if i < n && i < m then return [.changed i src[i]! got[i]!]
    if i < n then return [.missing i src[i]!]
    return [.extra i got[i]!]
  -- d[i][j] = cost of aligning src[i:] with got[j:]
  let w := m + 1
  let mut d : Array Nat := Array.replicate ((n + 1) * w) 0
  for i' in [0:n + 1] do
    let i := n - i'
    for j' in [0:m + 1] do
      let j := m - j'
      let v :=
        if i == n then m - j
        else if j == m then n - i
        else
          let sub := d[(i + 1) * w + j + 1]! + (if src[i]! == got[j]! then 0 else 1)
          min sub (min (d[(i + 1) * w + j]! + 1) (d[i * w + j + 1]! + 1))
      d := d.set! (i * w + j) v
  let mut out := #[]
  let mut i := 0
  let mut j := 0
  while i < n || j < m do
    let here := d[i * w + j]!
    if i < n && j < m && src[i]! == got[j]! && here == d[(i + 1) * w + j + 1]! then
      i := i + 1; j := j + 1
    else if i < n && j < m && here == d[(i + 1) * w + j + 1]! + 1 then
      out := out.push (.changed i src[i]! got[j]!); i := i + 1; j := j + 1
    else if i < n && here == d[(i + 1) * w + j]! + 1 then
      out := out.push (.missing i src[i]!); i := i + 1
    else
      out := out.push (.extra i got[j]!); j := j + 1
  return out.toList

end LangLib
