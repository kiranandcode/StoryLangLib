import pathlib, sys
from pygments import highlight
from pygments.lexers import get_lexer_by_name
from pygments.formatters import ImageFormatter
here = pathlib.Path(__file__).parent
for f in sorted((here / "snippets").glob("*.lean")):
    png = highlight(f.read_text(), get_lexer_by_name("lean4"),
                    ImageFormatter(font_name="Menlo", font_size=22, line_numbers=False,
                                   style="friendly", image_pad=28, line_pad=4))
    (here / "out" / f"code-{f.stem}.png").write_bytes(png)
    print(here / "out" / f"code-{f.stem}.png")
