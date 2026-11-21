"""Check every document the Rules view can open, the way the Studio serves it.

    rules_check_all.py [--out DIR] [--only SUBSTR] [--cache DIR] [--no-lean]

For each document (papers in stories/private-papers, essays stories/essay-*,
deslop sides in stories/private-deslop and docs/deslop, every story, the
Death Note arc) this builds its rules JSON as studio/server.py does
(studio/rules_docs.py, studio/rules_story.py), checks it with
`langlib rules-json`, writes the kernel-checked Lean of tools/house/rules_lean.py
to DIR (default: a temporary directory; nothing is written into the repo, so
private documents stay private), compiles each file with `lake env lean`
(one at a time, through studio/procs.py) and prints a table:

    doc · rules · ok · shaped · faults · enthymemes · unread · proved

`--cache DIR` keeps each story's `langlib story` and `langlib power` output in
DIR and reuses it (the readings take a while; the adapters are what changes).
Exits non-zero when a story is not ok, not shaped or not proved.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "studio"))
sys.path.insert(0, str(ROOT / "tools/house"))
import procs  # noqa: E402
import rules_docs  # noqa: E402
import rules_lean  # noqa: E402
import rules_story  # noqa: E402

STORIES = ROOT / "stories"


def _cli(args: list[str], cache: Path | None, key: str, timeout: float) -> dict:
    """`langlib <args>` as JSON (extras._cli's reading of it), cached under `key`."""
    f = cache / f"{key}.json" if cache else None
    if f and f.exists():
        out = f.read_text()
    else:
        res = procs.run(procs.langlib_argv(*args), timeout=timeout)
        out = res.stdout
        try:
            json.loads(out)
        except json.JSONDecodeError:
            out = json.dumps({"error": (res.stderr or res.stdout or ("timed out" if res.timed_out else "no output"))[-2000:]})
        if f:
            f.write_text(out)
    r = json.loads(out)
    return r if isinstance(r, dict) else {"value": r}


def story_doc(name: str, cache: Path | None) -> dict:
    """server.py `rules_doc` for `story:<name>`, synchronously."""
    d = STORIES / name
    report = _cli(["story", str(d)], cache, f"{name}.story", 300)
    spec = json.loads((d / "story.json").read_text())
    report["title"] = spec.get("title", name)
    report["name"] = name
    power = _cli(["power", str(d)], cache, f"{name}.power", 300)
    return rules_docs.check(rules_story.story_doc(name, report, spec, power))


def story_dirs() -> list[str]:
    return sorted(p.name for p in STORIES.iterdir() if (p / "story.json").exists())


def all_docs() -> list[dict]:
    return rules_docs.docs(story_dirs())


def summary(doc: dict) -> dict:
    rs = doc.get("rules") or {}
    rules = rs.get("rules", [])
    faults = sum(len(r.get("faults", [])) for r in rules)
    unread = sum(1 for r in rules if any(f.get("kind") == "unread" for f in r.get("faults", [])))
    enth = sum(len(e["slots"]) for e in rs.get("enthymemes", []))
    return {"rules": len(rules), "ok": bool(rs.get("ok")), "shaped": bool(rs.get("shaped")), "faults": faults,
            "enthymemes": enth, "unread": unread, "errors": rs.get("errors", [])}


def collisions(rules: dict) -> list[str]:
    """Distinct terms rules_lean would give one constructor name (the kernel would then decide something else)."""
    seen: dict[str, str] = {}
    out = []
    for r in rules["rules"]:
        for n in [r["id"], r["concl"], *(p["t"] for p in r["premises"])]:
            i = rules_lean.ident(n)
            if seen.setdefault(i, n) != n:
                out.append(f"{seen[i]} / {n}")
    return sorted(set(out))


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--out", type=Path, default=None)
    ap.add_argument("--only", default="")
    ap.add_argument("--cache", type=Path, default=None)
    ap.add_argument("--no-lean", action="store_true")
    a = ap.parse_args()
    procs.install_signal_handlers()
    out = a.out or Path(tempfile.mkdtemp(prefix="rulecheck-"))
    out.mkdir(parents=True, exist_ok=True)
    if a.cache:
        a.cache.mkdir(parents=True, exist_ok=True)
    rows, bad = [], []
    for k, d in enumerate(all_docs()):
        if a.only and a.only not in d["id"]:
            continue
        try:
            doc = story_doc(d["id"][6:], a.cache) if d["id"].startswith("story:") else rules_docs.get(d["id"])
        except Exception as e:  # noqa: BLE001  report it and go on
            doc = {"error": f"{type(e).__name__}: {e}"}
        if doc.get("error"):
            rows.append((d["id"], {"error": str(doc["error"])[:120]}))
            if d["group"] in ("stories", "lean"):
                bad.append(d["id"])
            continue
        s = summary(doc)
        col = collisions(doc["rules"])
        if col:
            s["errors"] = s["errors"] + [f"constructor clash: {c}" for c in col]
        proved = "skip"
        if not a.no_lean:
            ns = "RuleCheck." + re.sub(r"\W", "_", d["id"]).strip("_")
            f = out / f"{k:02d}_{re.sub(r'[^A-Za-z0-9]+', '_', d['id']).strip('_')[-60:]}.lean"
            f.write_text(rules_lean.lean(doc["rules"], ns))
            res = procs.run(["lake", "env", "lean", str(f)], timeout=600)
            proved = "yes" if res.returncode == 0 else "no"
            if res.returncode:
                s["errors"] = s["errors"] + [f"lean: {(res.stdout + res.stderr).strip()[:600]}"]
            s["lean"] = str(f)
        s["proved"] = proved
        rows.append((d["id"], s))
        story = d["group"] in ("stories", "lean")
        if story and not (s["ok"] and s["shaped"] and proved in ("yes", "skip") and not col):
            bad.append(d["id"])
        print(f"{d['id']}: {s['rules']} rules, ok={s['ok']} shaped={s['shaped']} proved={proved}", file=sys.stderr, flush=True)
    w = max([len(i) for i, _ in rows] + [3])
    print(f"{'doc':<{w}}  rules  ok   shaped  faults  enthymemes  unread  proved")
    for i, s in rows:
        if "error" in s:
            print(f"{i:<{w}}  error: {s['error']}")
            continue
        yn = lambda b: "yes" if b else "no"  # noqa: E731
        print(f"{i:<{w}}  {s['rules']:>5}  {yn(s['ok']):<3}  {yn(s['shaped']):<6}  {s['faults']:>6}  {s['enthymemes']:>10}  {s['unread']:>6}  {s['proved']}")
    for i, s in rows:
        for e in s.get("errors", []):
            print(f"  {i}: {e}")
    print(f"\nLean files in {out}")
    if bad:
        print(f"stories not ok, shaped and proved: {', '.join(bad)}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
