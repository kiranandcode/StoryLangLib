"""An argument's rules (`langlib rules <dir>`) as markdown: informal inference rules.

    rules_md.py <dir>          print the markdown for <dir> (argument.json, paragraphs/)

`to_markdown(rules, paragraphs, headings)` is what the Studio and the deslop
UI export. Each rule is drawn natural-deduction style in a code block: the
premises (verbatim quotes, each tagged) above a line, the conclusion below
it, the scheme and kind at the right of the line. A strict rule's line is
solid (───), a defeasible one's dashed (╌╌╌). The tree runs from the root
conclusion up through the rules its premises rest on; rules outside the tree
(opponents, side arguments) follow.
"""
import json, sys, textwrap
from pathlib import Path

TAG = {"fact": "fact", "example": "example", "citation": "citation", "authors": "authors' word",
       "hedge": "hedge", "promise": "promise"}
W = 76


def _wrap(s, indent=""):
    return textwrap.wrap(s, W - len(indent), initial_indent=indent, subsequent_indent=indent + "  ") or [indent]


def rule_block(r, by_id):
    """One rule as text lines: premises, the line, the conclusion."""
    lines = []
    for p in r["premises"]:
        tag = f"from {p['sub']}" if p.get("sub") else TAG.get(p["tag"], p["tag"])
        q = p.get("quote") or p["t"]
        lines += _wrap(f"“{q}”  [{tag}]")
    bar = "─" if r["kind"] == "strict" else "╌"
    right = f" {r['scheme']} ({r['kind']})"
    lines.append(bar * max(12, W - len(right)) + right)
    lines += _wrap(f"“{r.get('quote') or r['concl']}”")
    return lines


def label_of(r):
    s = f"**{r['label']}**"
    if r.get("sceptic") and r["sceptic"] != r["label"]:
        s += f", {r['sceptic']} under the sceptic's questions"
    return s


def rule_md(r, by_id, attacks, depth=0):
    head = f"{'#' * min(6, 3 + depth)} {r['id']}: {r['concl']}" if depth < 3 else f"**{r['id']}: {r['concl']}**"
    out = [head, "", f"{'Opponent position. ' if r['side'] == 'opponent' else ''}Label: {label_of(r)}."
           + (f" Paragraph {r['para']}." if r.get("para") else ""), "", "```", *rule_block(r, by_id), "```", ""]
    att_in = [a for a in attacks if a["tgt"] == r["id"]]
    att_out = [a for a in attacks if a["src"] == r["id"]]
    for a in att_in:
        out.append(f"- attacked by {a['src']} ({a['how']}{', on ' + a['on'] if a.get('on') else ''})"
                   + (f": “{a['quote']}”" if a.get("quote") else ""))
    for a in att_out:
        out.append(f"- {a['how']}s {a['tgt']}" + (f": “{a['quote']}”" if a.get("quote") else ""))
    for t in r.get("thin", []):
        out.append(f"- thin: {t}")
    for c in r.get("cqs", []):
        if c["status"] != "open" or c.get("note"):
            mark = {"answered": "answered", "pressed": "**pressed**", "open": "open"}[c["status"]]
            out.append(f"- CQ{c['i'] + 1} ({c['attack']}, {mark}): {c['q']}" + (f" {c['note']}" if c.get("note") else ""))
    out.append("")
    return out


def to_markdown(rules, paragraphs=None, headings=None):
    rs = rules["rules"]
    by_id = {r["id"]: r for r in rs}
    by_concl = {r["concl"]: r for r in rs}
    attacks = rules.get("attacks", [])
    out = ["## Rules", ""]
    if headings and headings.get("title"):
        out[0] = f"## Rules: {headings['title']}"
    n_in = sum(r["label"] == "in" for r in rs)
    out += [f"{len(rs)} rules ({sum(r['kind'] == 'strict' for r in rs)} strict), {n_in} in under the text's "
            f"own attacks, {sum(r.get('sceptic') == 'in' for r in rs)} in under the sceptic's questions.", ""]
    seen = []

    def walk(r, depth):
        if r["id"] in seen:
            out.append(f"{'  ' * depth}- {r['id']} (above)")
            return
        seen.append(r["id"])
        out.append(f"{'  ' * depth}- **{r['id']}** {r['concl']}: {r['scheme']}, {r['kind']}, {r['label']}"
                   + (f" / sceptic {r['sceptic']}" if r.get("sceptic") else ""))
        for p in r["premises"]:
            if p.get("sub") and p["sub"] in by_id:
                walk(by_id[p["sub"]], depth + 1)

    root = by_concl.get(rules.get("root", ""))
    if root:
        out += ["### The tree", "", "From the conclusion up to the rules it rests on.", ""]
        walk(root, 0)
        out.append("")
    tree = list(seen)
    rest = [r for r in rs if r["id"] not in tree]
    if rest:
        out += ["Outside the tree: " + ", ".join(f"{r['id']} ({r['side']})" for r in rest) + ".", ""]
    out += ["### Each rule", ""]
    for i in tree + [r["id"] for r in rest]:
        out += rule_md(by_id[i], by_id, attacks)
    if rules.get("bare"):
        out += ["### Resting on the authors' word alone", "", "Rules: " + ", ".join(rules["bare"]) + ".", ""]
    if rules.get("bareLeaves"):
        out += ["Premises nothing in the text supports: " + ", ".join(rules["bareLeaves"]) + ".", ""]
    return "\n".join(out)


def load(d):
    d = Path(d)
    paras = {p.stem: p.read_text() for p in sorted((d / "paragraphs").glob("[0-9][0-9].txt"))}
    heads = json.loads((d / "headings.json").read_text()) if (d / "headings.json").exists() else {}
    return paras, heads


if __name__ == "__main__":
    sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "studio"))
    import procs
    d = sys.argv[1]
    r = procs.run(procs.langlib_argv("rules", d))
    if r.returncode:
        sys.exit(r.stderr)
    paras, heads = load(d)
    print(to_markdown(json.loads(r.stdout), paras, heads))
