"""Build the evaluation corpus: paragraphs from Project Gutenberg and from
Kiran's blog, 40-150 words each, written to corpus/<id>.txt."""
import random, re, urllib.request, pathlib

OUT = pathlib.Path(__file__).parent / "corpus"
GUTENBERG = {  # id: (gutenberg number, what it stresses)
    "austen": (1342, "dialogue, free indirect speech"),
    "melville": (2701, "long periodic sentences"),
    "doyle": (1661, "dialogue, quotes in quotes"),
    "twain": (76, "dialect, contractions"),
    "stoker": (345, "diary entries, dates"),
    "dickinson": (12242, "verse, dashes"),
    "shelley": (84, "letters, archaic register"),
    "fitzgerald": (64317, "modern literary prose"),
}
BLOG = pathlib.Path.home() / "Documents/code/kirancodes.me/posts"
PER_SOURCE = 2
rng = random.Random(7)

def body(text):
    s = text.find("*** START OF"); e = text.find("*** END OF")
    text = text[text.find("\n", s) + 1 : e if e > 0 else None]
    return text[len(text) // 10 :]  # skip front matter and contents

def paragraphs(text):
    for p in re.split(r"\n\s*\n", text.replace("\r", "")):
        p = re.sub(r"[ \t]*\n[ \t]*", " ", p.strip()) if "dickinson" not in cur else p.strip()
        n = len(p.split())
        if 40 <= n <= 150 and not p.isupper() and "_" not in p and "[" not in p:
            yield p

def org_paragraphs(text):
    text = re.sub(r"#\+BEGIN_SRC.*?#\+END_SRC", "", text, flags=re.S | re.I)
    text = re.sub(r"#\+BEGIN_\w+.*?#\+END_\w+", "", text, flags=re.S | re.I)
    for p in re.split(r"\n\s*\n", text):
        if any(l.lstrip().startswith(("#", "*", "|", "-", ":")) for l in p.splitlines()):
            continue
        p = re.sub(r"\[\[[^\]]*\]\[([^\]]*)\]\]", r"\1", p)  # [[url][text]] -> text
        p = re.sub(r"\[\[([^\]]*)\]\]", r"\1", p)
        p = re.sub(r"[=~]([^=~\n]+)[=~]", r"\1", p)  # =code= / ~code~
        p = re.sub(r"(?<!\w)[/*]([^/*\n]+)[/*](?!\w)", r"\1", p)  # /italic/ *bold*
        p = " ".join(p.split())
        if 40 <= len(p.split()) <= 150 and "@@" not in p:
            yield p

OUT.mkdir(exist_ok=True)
for cur, (num, why) in GUTENBERG.items():
    url = f"https://www.gutenberg.org/cache/epub/{num}/pg{num}.txt"
    text = urllib.request.urlopen(url, timeout=60).read().decode("utf-8", "replace")
    ps = list(paragraphs(body(text)))
    if cur == "dickinson":  # keep verse line breaks; stanzas are short, take pairs
        ps = [p for p in re.split(r"\n\s*\n", body(text)) if 30 <= len(p.split()) <= 120 and "[" not in p]
    for i, p in enumerate(rng.sample(ps, PER_SOURCE)):
        (OUT / f"{cur}-{i}.txt").write_text(p.strip() + "\n")
    print(cur, len(ps), "candidates")

posts = sorted(BLOG.glob("*.org"))
cands = [(f.stem, p) for f in posts for p in org_paragraphs(f.read_text())]
for i, (stem, p) in enumerate(rng.sample(cands, 4)):
    (OUT / f"kiran-{i}.txt").write_text(p + "\n")
    print("kiran", stem)
