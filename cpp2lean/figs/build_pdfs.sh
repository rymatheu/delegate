#!/usr/bin/env bash
# Typeset every figure and table of figs/src as a cropped standalone PDF in figs/pdf/<name>.pdf.
#   figures (every src/*.tex except the tables and the data files they input): the standalone class
#     over acmart (sigconf), with the union of the preambles the figures' headers list (tikz with the
#     arrows.meta, calc, positioning, fit and backgrounds libraries; graphicx and amssymb come with
#     acmart; booktabs, array); the PNGs and \input files are found in src/ (graphicspath, input@path);
#     a figure that sizes its image to \linewidth is set in a minipage of 8.2 cm, the width
#     the figures are made for;
#   tables (src/*.tex holding a table float): the same standalone class, with the table float redefined
#     as a box of the sigconf line width (241.14749 pt) in which \caption makes a table caption.
# Usage: figs/build_pdfs.sh [NAME...]   (default: all); needs pdflatex and gs.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
SRC="$HERE/src"; OUT="$HERE/pdf"; B="$HERE/.build"
mkdir -p "$OUT" "$B"
DATA=" oracle-diff-data "                     # inputs of other figures, not figures themselves
names=("$@")
if [ ${#names[@]} -eq 0 ]; then
  for f in "$SRC"/*.tex; do names+=("$(basename "$f" .tex)"); done
fi
fail=0
for n in "${names[@]}"; do
  [[ "$DATA" == *" $n "* ]] && continue
  if grep -q '\\begin{table' "$SRC/$n.tex"; then
    cat > "$B/$n-wrap.tex" <<TEX
\\documentclass[class=acmart,sigconf,border=0pt]{standalone}
\\usepackage{booktabs}
\\usepackage{array}
\\makeatletter\\def\\input@path{{$SRC/}}\\makeatother
% the table float as a box of the sigconf line width; \\caption works there through \\@captype
\\makeatletter\\renewenvironment{table}[1][]{\\begin{minipage}{241.14749pt}\\def\\@captype{table}}{\\end{minipage}}\\makeatother
\\begin{document}
\\input{$n}
\\end{document}
TEX
  else
    body="\\input{$n}"
    if grep -q 'width=\\linewidth' "$SRC/$n.tex"; then body="\\begin{minipage}{8.2cm}\\input{$n}\\end{minipage}"; fi
    cat > "$B/$n-wrap.tex" <<TEX
\\documentclass[class=acmart,sigconf,border=0pt]{standalone}
\\usepackage{tikz}
\\usetikzlibrary{arrows.meta,calc,positioning,fit,backgrounds}
\\usepackage{booktabs}
\\usepackage{array}
\\graphicspath{{$SRC/}}
\\makeatletter\\def\\input@path{{$SRC/}}\\makeatother
\\begin{document}
$body
\\end{document}
TEX
  fi
  (cd "$B" && pdflatex -interaction=nonstopmode "$n-wrap.tex" >/dev/null 2>&1; pdflatex -interaction=nonstopmode "$n-wrap.tex" >/dev/null 2>&1) || true
  errs=$(grep -c '^!' "$B/$n-wrap.log" || true); over=$(grep -c 'Overfull' "$B/$n-wrap.log" || true)
  if [ ! -f "$B/$n-wrap.pdf" ] || [ "$errs" != 0 ]; then echo "$n: FAILED ($errs errors, see $B/$n-wrap.log)"; fail=1; continue; fi
  cp "$B/$n-wrap.pdf" "$OUT/$n.pdf"
  size=$(gs -q -dNODISPLAY -dNOSAFER -c "($OUT/$n.pdf) (r) file runpdfbegin 1 pdfgetpage /MediaBox pget pop == quit" 2>/dev/null \
    | python3 -c "import sys,re;v=[float(x) for x in re.findall(r'-?[\d.]+',sys.stdin.read())];print('%.2f x %.2f cm'%((v[2]-v[0])*2.54/72,(v[3]-v[1])*2.54/72))")
  echo "$n: $size, $errs errors, $over overfull"
done
exit $fail
