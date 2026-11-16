"""Compact s-expression annotations -> langlib documents (eval/prompt.md format).

    sx.py <file.sx> ...        write <file>.json beside each

A file holds entity and topic lines, then one tree per sentence:

    entity kiran person she "Kiran"          [generic] [of=a,b]
    topic t1 "Kiran arrives" kiran
    (S%t1 (SBAR.advcl When/SCONJ.mark
            (S.head (NP.nsubj@kiran she/PRON.head)
                    (VP.head finally/ADV.advmod walked/VERB.head=walk{Fin,Past} in/ADV.advmod)))
          ,/PUNCT Kiran/PROPN.nsubj@kiran
          (VP.head didn't/AUX.aux=do{Fin,Past} look/VERB.head{Inf}
                   (PP.obl at/ADP.case him/PRON.head@m))
          ./PUNCT)

Node:  (CAT[.role][@ref][%topic][!speaker] kids...)   a top-level node is the root
Leaf:  form/UPOS[.role][=lemma][{feats}][@ref][~sense] PUNCT defaults to role punct
Feats: k=v pairs, or the shorthands Fin Inf Part Ger (VerbForm), Past Pres (Tense).
Escape ( ) and \\ in a form with a backslash: \\(/PUNCT.
"""
import json, re, sys

UPOS = "ADJ ADP ADV AUX CCONJ DET INTJ NOUN NUM PART PRON PROPN PUNCT SCONJ SYM VERB X".split()
LEAF = re.compile(r"^(?P<w>.+?)/(?P<p>%s)(?:\.(?P<r>[a-z]+))?(?:=(?P<l>[^{@~]+))?"
                  r"(?:\{(?P<f>[^}]*)\})?(?:@(?P<ref>[\w-]+))?(?:~(?P<s>[\w-]+))?$" % "|".join(UPOS))
HEAD = re.compile(r"^(?P<c>[A-Z]+)(?:\.(?P<r>[a-z]+))?(?:@(?P<ref>[\w-]+))?(?:%(?P<t>[\w-]+))?(?:!(?P<spk>[\w-]+))?$")
SHORT = {"Fin": ("VerbForm", "Fin"), "Inf": ("VerbForm", "Inf"), "Part": ("VerbForm", "Part"),
         "Ger": ("VerbForm", "Ger"), "Past": ("Tense", "Past"), "Pres": ("Tense", "Pres")}


def atoms(src):
    """Tokens: '(' ')' and atoms (backslash escapes the next character)."""
    out, i, n = [], 0, len(src)
    while i < n:
        ch = src[i]
        if ch.isspace():
            i += 1
        elif ch in "()":
            out.append(ch); i += 1
        else:
            buf = []
            while i < n and not src[i].isspace() and src[i] not in "()":
                if src[i] == "\\" and i + 1 < n:
                    buf.append(src[i + 1]); i += 2
                else:
                    buf.append(src[i]); i += 1
            out.append("".join(buf))
    return out


def leaf(a, where):
    m = LEAF.match(a)
    if not m:
        raise SystemExit(f"{where}: bad leaf {a!r} (form/UPOS[.role][=lemma][{{feats}}][@ref])")
    d = {"w": m["w"], "p": m["p"]}
    r = m["r"] or ("punct" if m["p"] == "PUNCT" else None)
    if r: d["r"] = r
    if m["l"]: d["l"] = m["l"]
    if m["f"]:
        f = {}
        for x in m["f"].split(","):
            x = x.strip()
            if not x: continue
            k, v = SHORT[x] if x in SHORT else x.split("=", 1)
            f[k] = v
        d["f"] = f
    if m["ref"]: d["ref"] = m["ref"]
    if m["s"]: d["sense"] = m["s"]
    return d


def parse(toks, i, where):
    """Parse a node starting at toks[i] == '('; return (tree, next index)."""
    i += 1
    h = HEAD.match(toks[i]) if i < len(toks) else None
    if not h:
        raise SystemExit(f"{where}: bad node head {toks[i] if i < len(toks) else 'EOF'!r}")
    d = {"c": h["c"]}
    for k, key in (("r", "r"), ("ref", "ref"), ("spk", "spk"), ("t", "topic")):
        if h[k]: d[key] = h[k]
    i += 1
    kids = []
    while i < len(toks) and toks[i] != ")":
        if toks[i] == "(":
            k, i = parse(toks, i, where)
        else:
            k, i = leaf(toks[i], where), i + 1
        kids.append(k)
    if i >= len(toks):
        raise SystemExit(f"{where}: unclosed ({d['c']}")
    d["k"] = kids
    return d, i + 1


def compile_sx(text, where="sx"):
    ents, topics, body = [], [], []
    for ln in text.splitlines():
        s = ln.strip()
        if s.startswith("#") or not s:
            body.append("")
        elif s.startswith("entity "):
            parts = re.findall(r'"[^"]*"|\S+', s)[1:]
            e = {"id": parts[0], "kind": parts[1], "pron": parts[2]}
            for p in parts[3:]:
                if p.startswith('"'): e["name"] = p.strip('"')
                elif p == "generic": e["generic"] = True
                elif p.startswith("of="): e["of"] = p[3:].split(",")
            ents.append(e)
        elif s.startswith("topic "):
            parts = re.findall(r'"[^"]*"|\S+', s)[1:]
            topics.append({"id": parts[0], "label": parts[1].strip('"'),
                           "entities": parts[2].split(",") if len(parts) > 2 else []})
        else:
            body.append(ln)
    toks = atoms("\n".join(body))
    sents, i = [], 0
    while i < len(toks):
        if toks[i] != "(":
            raise SystemExit(f"{where}: text outside a tree: {toks[i]!r}")
        t, i = parse(toks, i, f"{where} sentence {len(sents) + 1}")
        t.setdefault("r", "root")
        sents.append(t)
    return {"entities": ents, "topics": topics, "sentences": sents}


if __name__ == "__main__":
    for p in sys.argv[1:]:
        doc = compile_sx(open(p).read(), p)
        out = re.sub(r"\.sx$", "", p) + ".json"
        json.dump(doc, open(out, "w"), ensure_ascii=False)
        print(out, len(doc["sentences"]), "sentences")
