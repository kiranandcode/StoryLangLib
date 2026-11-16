"""Compact annotation syntax -> langlib JSON (eval/prompt.md format).

    python3 stories/roof-eleven/sx.py NN     reads paragraphs/NN.sx, writes paragraphs/NN.json

    ent theo "Theo" person he              one per line: id, name, kind, pron
    topic t1 "label" kiran theo
    (S root topic=t1 (NP nsubj ref=theo He|PRON|head) came|VERB|head|l=come .|PUNCT|punct)

A node is `(CAT ROLE key=val ... children)`, keys ref spk topic sense; a leaf is
`WORD|UPOS|ROLE|k=v,k=v` with keys ref, sense, l (lemma), anything else a UD
feature (Tense=Pres). `#` starts a comment line.
"""
import json
import re
import sys
from pathlib import Path

NODE_KEYS = {"ref", "spk", "topic", "sense"}


def leaf(t):
    w, p, *rest = t.split("|")
    d = {"w": w, "p": p}
    if rest and rest[0]:
        d["r"] = rest[0]
    for kv in (rest[1].split(",") if len(rest) > 1 and rest[1] else []):
        k, v = kv.split("=", 1)
        if k in ("ref", "sense"):
            d[k] = v
        elif k == "l":
            d["l"] = v
        else:
            d.setdefault("f", {})[k] = v
    return d


def parse(toks, i):
    node = {"c": toks[i + 1], "r": toks[i + 2], "k": []}
    i += 3
    while toks[i] != ")":
        t = toks[i]
        if t == "(":
            child, i = parse(toks, i)
            node["k"].append(child)
            continue
        if "|" not in t and "=" in t and t.split("=", 1)[0] in NODE_KEYS:
            k, v = t.split("=", 1)
            node[k] = v
        else:
            node["k"].append(leaf(t))
        i += 1
    return node, i + 1


def convert(text):
    ents, topics, body = [], [], []
    for line in text.splitlines():
        s = line.strip()
        if not s or s.startswith("#"):
            continue
        if s.startswith("ent "):
            m = re.match(r'ent (\S+) "([^"]*)" (\S+) (\S+)', s)
            ents.append({"id": m[1], "name": m[2], "kind": m[3], "pron": m[4]})
        elif s.startswith("topic "):
            m = re.match(r'topic (\S+) "([^"]*)"(.*)', s)
            topics.append({"id": m[1], "label": m[2], "entities": m[3].split()})
        else:
            body.append(line)
    toks = re.findall(r'\(|\)|[^\s()]+', "\n".join(body))
    sents, i = [], 0
    while i < len(toks):
        n, i = parse(toks, i)
        sents.append(n)
    return {"entities": ents, "topics": topics, "sentences": sents}


if __name__ == "__main__":
    d = Path(__file__).parent / "paragraphs"
    for k in sys.argv[1:]:
        (d / f"{int(k):02}.json").write_text(json.dumps(convert((d / f"{int(k):02}.sx").read_text()), ensure_ascii=False) + "\n")
