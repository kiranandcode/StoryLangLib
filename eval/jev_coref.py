"""Spot-check the reference layer of langlib documents with Jev.

The token check proves a document says the same words as the source; it says
nothing about whether `ref`s point at the right entity. For every third-person
pronoun mention, this asks Jev to pick its referent from the document's own
entities, with the pronoun marked in the passage, and compares the pick with
the document's `ref`.

usage: python3 jev_coref.py <text.txt> <doc.json> [...more pairs]
       python3 jev_coref.py --runs MODEL COND   # every final, token-faithful doc of a run
"""
import json, pathlib, subprocess, sys
from concurrent.futures import ThreadPoolExecutor
import jev

HERE = pathlib.Path(__file__).parent
LANGLIB = HERE.parent / ".lake/build/bin/langlib"


def check_pair(text_path: pathlib.Path, doc_path: pathlib.Path) -> list[dict]:
    rep = json.loads(subprocess.run([str(LANGLIB), "check", str(text_path), str(doc_path)],
                                    capture_output=True, text=True).stdout)
    if not rep.get("tokensMatch"):
        return []
    doc = json.loads(doc_path.read_text())
    ents = {e["id"]: e.get("name", e["id"]) for e in doc.get("entities", [])}
    toks = subprocess.run([str(LANGLIB), "tokenize", str(text_path)],
                          capture_output=True, text=True).stdout.splitlines()
    if len(ents) < 2:
        return []

    def ask(p):
        i = p["pos"]
        marked = " ".join(toks[:i] + [f"[[{toks[i]}]]"] + toks[i + 1:])
        crit = {eid: f"refers to {name}" for eid, name in ents.items()}
        a = jev.system_one(marked, {"ref": jev.choice(
            f"Who or what does the pronoun marked [[{toks[i]}]] refer to?", crit)})["ref"]
        return {"passage": text_path.stem, "pos": i, "form": p["form"], "doc_ref": p["entity"],
                "jev_ref": a.get("choice"), "jev_p_doc": (a.get("probabilities") or {}).get(p["entity"]),
                "phora": p["phora"]}

    with ThreadPoolExecutor(8) as ex:
        return list(ex.map(ask, rep["pronouns"]))


def main():
    args = sys.argv[1:]
    pairs = []
    if args[:1] == ["--runs"]:
        model, cond = args[1], args[2]
        for line in (HERE / "runs/results.jsonl").read_text().splitlines():
            r = json.loads(line)
            if r["model"] == model and r["cond"] == cond:
                n = len(r["rounds"])
                pairs.append((HERE / "corpus" / f"{r['passage']}.txt",
                              HERE / "runs" / model / cond / f"{r['passage']}.r{n}.json"))
    else:
        pairs = [(pathlib.Path(a), pathlib.Path(b)) for a, b in zip(args[::2], args[1::2])]
    rows = [row for t, d in pairs for row in check_pair(t, d)]
    for r in rows:
        mark = "ok " if r["jev_ref"] == r["doc_ref"] else "XX "
        print(mark, json.dumps(r))
    if rows:
        agree = sum(r["jev_ref"] == r["doc_ref"] for r in rows)
        print(f"agreement {agree}/{len(rows)} = {agree / len(rows):.0%}")


if __name__ == "__main__":
    main()
