/-!
# Tokenizer

Splits English text into words and punctuation. The rules are deliberately
simple and deterministic, because both the source text and every tree leaf are
cut by the same function:

* whitespace separates tokens and is dropped;
* a word is a run of letters and digits (any non-ASCII character that is not in
  `unicodePunct` counts as a letter), joined across an apostrophe or hyphen that
  sits between two word characters (`don't`, `O'Brien`, `well-known`), and
  across `.` or `,` between two digits (`3.14`, `1,000`);
* every other character is a one-character punctuation token, except runs of
  `-` and runs of `.`, which are one token each (`--`, `...`).
-/

namespace LangLib

def unicodePunct : List Char :=
  ['“', '”', '‘', '’', '—', '–', '…', '«', '»', '„', '‚', '′', '″', '•', '·',
   '§', '¶', '†', '‡', '¡', '¿', '‹', '›']

def isSpaceChar (c : Char) : Bool :=
  c.isWhitespace || c == ' ' || c == ' ' || c == ' ' || c == ' '

def isWordChar (c : Char) : Bool :=
  c.isAlphanum || (c.toNat ≥ 128 && !isSpaceChar c && !unicodePunct.contains c)

private def joins (prev c next : Char) : Bool :=
  ((c == '\'' || c == '’' || c == '-') && isWordChar prev && isWordChar next) ||
  ((c == '.' || c == ',') && prev.isDigit && next.isDigit)

private partial def scanWord (cs : Array Char) (j : Nat) : Nat :=
  if h : j < cs.size then
    if isWordChar cs[j] then scanWord cs (j + 1)
    else if j + 1 < cs.size && j > 0 && joins cs[j - 1]! cs[j] cs[j + 1]! then
      scanWord cs (j + 2)
    else j
  else j

private partial def scanRun (cs : Array Char) (c : Char) (j : Nat) : Nat :=
  if j < cs.size && cs[j]! == c then scanRun cs c (j + 1) else j

private def slice (cs : Array Char) (i j : Nat) : String :=
  String.ofList (cs.extract i j).toList

partial def tokenize (s : String) : List String :=
  let cs := s.toList.toArray
  let rec go (i : Nat) (acc : Array String) : Array String :=
    if h : i < cs.size then
      let c := cs[i]
      if isSpaceChar c then go (i + 1) acc
      else if isWordChar c then
        let j := scanWord cs (i + 1)
        go j (acc.push (slice cs i j))
      else if c == '-' || c == '.' then
        let j := scanRun cs c (i + 1)
        go j (acc.push (slice cs i j))
      else go (i + 1) (acc.push (String.singleton c))
    else acc
  (go 0 #[]).toList

/-- Is `s` exactly one token? -/
def isToken (s : String) : Bool := tokenize s == [s]

private def noSpaceBefore (t : String) : Bool :=
  [",", ".", ";", ":", "!", "?", ")", "]", "}", "”", "’", "...", "…", "%"].contains t ||
  t.startsWith "'" && t.length > 1

private def noSpaceAfter (t : String) : Bool :=
  ["(", "[", "{", "“", "‘", "$", "£"].contains t

/-- Join tokens back into readable text (for display; not used in checking).
Straight double quotes alternate between opening and closing. -/
def detokenize (ts : List String) : String := Id.run do
  let mut out := ""
  let mut prev : Option String := none
  let mut openDq := false
  for t in ts do
    let isDq := t == "\""
    let attach :=
      match prev with
      | none => true
      | some p =>
        noSpaceAfter p || (p == "\"" && openDq) || noSpaceBefore t ||
        (isDq && openDq) || p == "—" || t == "—"
    out := if attach then out ++ t else out ++ " " ++ t
    if isDq then openDq := !openDq
    prev := some t
  return out

end LangLib
