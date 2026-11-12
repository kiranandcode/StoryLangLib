"""Ask models to encode each corpus passage as a langlib document, check each
answer with `langlib check`, and feed the report back until it passes or the
round budget runs out.

usage: python3 run_eval.py [--models haiku,sonnet,opus,fable] [--conds raw,tokens]
                           [--rounds 3] [--jobs 8] [--only austen-0,...]
Results go to runs/<model>/<cond>/<passage>.r<n>.{json,check.json} and
runs/results.jsonl (one line per passage x model x condition).
"""
import argparse, json, pathlib, re, subprocess, time
from concurrent.futures import ThreadPoolExecutor

HERE = pathlib.Path(__file__).parent
LANGLIB = HERE.parent / ".lake/build/bin/langlib"
PROMPTS = {"nested": (HERE / "prompt.md").read_text(), "flat": (HERE / "prompt-flat.md").read_text()}
SYSTEM = "You are an annotation engine. You output a single JSON document and nothing else."


def call_model(model: str, prompt: str) -> tuple[str, dict]:
    t0 = time.time()
    p = subprocess.run(
        ["claude", "-p", "--model", model, "--tools", "", "--setting-sources", "",
         "--strict-mcp-config", "--no-session-persistence", "--output-format", "json",
         "--system-prompt", SYSTEM],
        input=prompt, capture_output=True, text=True, timeout=1200)
    meta = {"secs": round(time.time() - t0, 1)}
    try:
        out = json.loads(p.stdout)
    except json.JSONDecodeError:
        return "", meta | {"error": (p.stderr or p.stdout)[-500:]}
    meta["cost"] = out.get("total_cost_usd")
    meta["out_tokens"] = out.get("usage", {}).get("output_tokens")
    return out.get("result", ""), meta


def extract_json(s: str) -> str:
    s = s.strip()
    m = re.search(r"```(?:json)?\s*(.*?)```", s, re.S)
    if m:
        s = m.group(1)
    i, j = s.find("{"), s.rfind("}")
    return s[i : j + 1] if i >= 0 else s


def check(text_path: pathlib.Path, doc_path: pathlib.Path) -> dict:
    p = subprocess.run([str(LANGLIB), "check", str(text_path), str(doc_path)],
                       capture_output=True, text=True)
    try:
        return json.loads(p.stdout)
    except json.JSONDecodeError:
        return {"ok": False, "parseError": p.stderr or p.stdout}


def tokens(text_path: pathlib.Path) -> list[str]:
    out = subprocess.run([str(LANGLIB), "tokenize", str(text_path)],
                         capture_output=True, text=True).stdout
    return out.splitlines()


def unclosed(s: str) -> str:
    """The closers needed to balance `s`, ignoring brackets inside strings."""
    stack, instr, esc = [], False, False
    for ch in s:
        if instr:
            if esc: esc = False
            elif ch == "\\": esc = True
            elif ch == '"': instr = False
        elif ch == '"': instr = True
        elif ch in "[{": stack.append(ch)
        elif ch in "]}" and stack: stack.pop()
    return "".join("}" if c == "{" else "]" for c in reversed(stack))


def feedback(rep: dict, doc: str = "") -> str:
    if "parseError" in rep:
        msg = f"Your JSON was rejected: {rep['parseError']}"
        missing = unclosed(doc)
        if missing:
            msg += (f"\nYour brackets do not balance: the document ends with {len(missing)} "
                    f"unclosed brackets and would need `{missing}` appended. Count the closers "
                    "at the end of each sentence tree and of the document carefully.")
        return msg
    lines = []
    if not rep["tokensMatch"]:
        lines.append(f"The leaves do not match the passage: the passage has {rep['srcTokens']} "
                     f"tokens, your tree has {rep['treeTokens']}, {rep['editCount']} differences:")
        lines += [f"- {e}" for e in rep["edits"]]
    if rep["badLeaves"]:
        lines.append("These leaves are not single tokens (split them): " + ", ".join(rep["badLeaves"]))
    if rep["refIssues"]:
        lines.append("Reference problems:")
        lines += [f"- {i}" for i in rep["refIssues"][:15]]
    return "\n".join(lines)


def run_one(model: str, cond: str, pid: str, rounds: int, fmt: str = "nested") -> dict:
    text_path = HERE / "corpus" / f"{pid}.txt"
    text = text_path.read_text()
    out_dir = HERE / "runs" / model / (cond if fmt == "nested" else f"{cond}-{fmt}")
    out_dir.mkdir(parents=True, exist_ok=True)
    base = PROMPTS[fmt] + f"\n## Passage\n\n{text}"
    if cond == "tokens":
        base += "\n## Tokens (the leaves must be exactly these, in order)\n\n" + \
            " ".join(f"{i}:{t}" for i, t in enumerate(tokens(text_path))) + "\n"
    prompt, hist = base, []
    for r in range(1, rounds + 1):
        raw, meta = call_model(model, prompt)
        doc = extract_json(raw)
        doc_path = out_dir / f"{pid}.r{r}.json"
        doc_path.write_text(doc)
        rep = check(text_path, doc_path) if doc else {"ok": False, "parseError": meta.get("error", "empty")}
        (out_dir / f"{pid}.r{r}.check.json").write_text(json.dumps(rep, indent=1))
        hist.append({"round": r, **meta, "ok": rep.get("ok", False),
                     "tokensMatch": rep.get("tokensMatch"), "editCount": rep.get("editCount"),
                     "refIssues": len(rep.get("refIssues", [])), "parseError": "parseError" in rep})
        print(f"{model:7} {cond:6} {pid:13} r{r} ok={rep.get('ok')} edits={rep.get('editCount')} "
              f"refs={len(rep.get('refIssues', []))} {meta.get('secs')}s", flush=True)
        if rep.get("ok"):
            break
        prompt = (base + "\n## Your previous answer\n\n" + doc +
                  "\n\n## Checker report\n\n" + feedback(rep, doc) +
                  "\n\nOutput the corrected JSON document in full.")
    return {"model": model, "cond": cond if fmt == "nested" else f"{cond}-{fmt}", "passage": pid, "rounds": hist,
            "passed": hist[-1]["ok"], "passed_round": len(hist) if hist[-1]["ok"] else None}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--models", default="haiku,sonnet,opus,fable")
    ap.add_argument("--conds", default="raw,tokens")
    ap.add_argument("--rounds", type=int, default=3)
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--only", default="")
    ap.add_argument("--format", default="nested", choices=["nested", "flat"])
    a = ap.parse_args()
    pids = sorted(p.stem for p in (HERE / "corpus").glob("*.txt"))
    if a.only:
        pids = [p for p in pids if p in a.only.split(",")]
    jobs = [(m, c, p) for m in a.models.split(",") for c in a.conds.split(",") for p in pids]
    res_path = HERE / "runs" / "results.jsonl"
    res_path.parent.mkdir(exist_ok=True)
    with ThreadPoolExecutor(a.jobs) as ex, res_path.open("a") as f:
        for res in ex.map(lambda j: run_one(*j, a.rounds, a.format), jobs):
            f.write(json.dumps(res) + "\n"); f.flush()


if __name__ == "__main__":
    main()
