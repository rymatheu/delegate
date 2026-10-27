#!/usr/bin/env python3
"""Pre-highlight Lean code for LaTeX without minted (for Overleaf or any build without shell escape).

    python3 prehighlight.py Contracts.lean --decl delegation --out delegation.tex
    python3 prehighlight.py snippet.lean --out snippet.tex
    python3 prehighlight.py --style-defs leanpyg-defs.tex

Writes a fancyvrb Verbatim block using the Pygments LaTeX macros (prefix PYG). The document needs
    \\usepackage{fancyvrb,xcolor} \\input{leanpyg-defs} \\input{leancolors} \\leanapplycolors
in the preamble and \\input{delegation} where the listing goes. Requires Pygments >= 2.18 (Lean 4 lexer)
and lean4vscode.py in the same directory as this script.
"""
import argparse, pathlib, re, sys
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from pygments import highlight
from pygments.formatters import LatexFormatter
from lean4vscode import CustomLexer

def extract_decl(src: str, name: str) -> str:
    lines = src.splitlines()
    pat = re.compile(r'^(theorem|lemma|def|abbrev|structure|class|instance|inductive|example)\s+' + re.escape(name) + r'\b')
    start = next((i for i, l in enumerate(lines) if pat.match(l)), None)
    if start is None:
        sys.exit(f'declaration {name!r} not found')
    end = start
    while end + 1 < len(lines) and lines[end + 1].strip():
        end += 1
    # include a docstring that ends on the line just above
    doc = start
    if start > 0 and lines[start - 1].rstrip().endswith('-/'):
        doc = start - 1
        while doc > 0 and not lines[doc].lstrip().startswith('/--'):
            doc -= 1
    return '\n'.join(lines[doc:end + 1]) + '\n'

ap = argparse.ArgumentParser()
ap.add_argument('source', nargs='?', help='Lean file')
ap.add_argument('--decl', help='name of one declaration to extract (with its docstring)')
ap.add_argument('--out', help='output .tex file (default: stdout)')
ap.add_argument('--fontsize', default=r'\footnotesize')
ap.add_argument('--style-defs', metavar='FILE', help='write the Pygments LaTeX style macros to FILE and exit')
a = ap.parse_args()

fmt = LatexFormatter(commandprefix='PYG', verboptions=f'fontsize={a.fontsize}')
if a.style_defs:
    pathlib.Path(a.style_defs).write_text(fmt.get_style_defs() + '\n', encoding='utf8'); sys.exit(0)
if not a.source:
    ap.error('a Lean source file is required unless --style-defs is given')
src = pathlib.Path(a.source).read_text(encoding='utf8')
code = extract_decl(src, a.decl) if a.decl else src
tex = highlight(code, CustomLexer(), fmt)
if a.out: pathlib.Path(a.out).write_text(tex, encoding='utf8')
else: sys.stdout.write(tex)
