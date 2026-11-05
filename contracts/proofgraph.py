#!/usr/bin/env python3
"""Proof-structure figure of the mission theorem, drawn from the axiom audit.

The dependency graph of `Contracts.Mission.mission_contract` is held below as data: lanes,
nodes (with the Lean declarations each node stands for), edges ("is used by", drawn upward)
and short glosses. The status of each node is not written by hand: it is read from the
output of `lake env lean AxiomCheck.lean` (run here, or a saved copy given with --axioms).

  proved   every declaration of the node depends only on propext, Classical.choice, Quot.sound
  open     some declaration of the node depends on sorryAx
  trusted  a hypothesis or a trusted definition (no status is computed)

Declarations of a node that AxiomCheck.lean does not print are queried with one extra
`#print axioms` run through `lake env lean --stdin` (nothing is written to disk); with
--no-lean that query is skipped and missing declarations are an error.

Usage (from cpp2lean/contracts):
  python3 proofgraph.py                          # runs the axiom audit
  python3 proofgraph.py --axioms axioms.txt      # a saved output of AxiomCheck.lean
  python3 proofgraph.py --out some/other.tex

Writes /Users/ryan/Research/delegate/staging/figs/proofgraph.tex by default.

The edges were checked against the Lean terms on 2026-11-05 (transitive closure of the
constants used by `mission_contract`): every solid edge is a use in a proof term, except where
a group node is the source, which means at least one member of the group is used. Members not
on the proof path of `mission_contract`: `step_spec`, `step_unique`, `norm_traj_sub_le`
(Gronwall), `allowance_rule`, `hδ`. They are drawn because they belong to their groups.
"""

from __future__ import annotations

import argparse
import datetime
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_OUT = Path("/Users/ryan/Research/delegate/staging/figs/proofgraph.tex")
CLEAN = {"propext", "Classical.choice", "Quot.sound"}

M = "Contracts.Mission."
P = "Contracts.Plant."
C = "Contracts."


def tt(s: str) -> str:
    """A Lean name in typewriter type, with TeX specials escaped."""
    return r"\texttt{" + s.replace("_", r"\_") + "}"


# ---------------------------------------------------------------------------------------------
#  Lanes, bottom to top: (id, label, y0, y1) in cm. Labels are set rotated in the left gutter.
# ---------------------------------------------------------------------------------------------
LANES = [
    ("trusted", "trusted", 0.00, 1.25),
    ("found", "foundations", 1.33, 3.05),
    ("lemmas", "lemmas", 3.13, 4.55),
    ("contracts", "contracts", 4.63, 6.45),
]
LANE_X0, LANE_X1 = 0.32, 8.20
HYP_X = 0.48          # left channel: the hypotheses, up to the open sub-contracts
SENSE_X = 8.03        # right channel: the sensing ports, up to navA_of_loop
BUS_Y = 4.59          # the hypotheses' bus under the sub-contracts
TROW_Y = 0.80         # the row of trusted definitions and hypotheses
JOIN_Y = 1.17         # where the two hypotheses join, above the trusted row

# ---------------------------------------------------------------------------------------------
#  Nodes. kind: "trusted" (hair gray, no check) or "lemma" (status from the axiom audit).
#  title: the Lean names (TeX); gloss: a short phrase under it (None for none);
#  check: the declarations whose axioms decide the status; big: \footnotesize title.
# ---------------------------------------------------------------------------------------------
NODES = [
    # (1) trusted base and hypotheses
    dict(id="checker", x=4.25, y=0.22, kind="trusted", width=7.20,
         title=r"Lean's type checker", inline=r"trusted checker of every node above", check=[]),
    dict(id="libm", x=1.17, y=0.80, kind="trusted",
         title=tt("LibmSpec"), gloss="C library", check=[]),
    dict(id="world", x=2.58, y=0.80, kind="trusted",
         title=tt("MissionWorld"), gloss="by evaluation", check=[]),
    dict(id="vf", x=4.25, y=0.80, kind="trusted",
         title=tt("vf"), gloss=r"plant ODE over $\mathbb{R}$", check=[]),
    dict(id="lift", x=5.85, y=0.80, kind="trusted",
         title=tt("Lift") + ", " + tt("STL"), gloss="semantics", check=[]),
    dict(id="sense", x=7.15, y=0.80, kind="trusted",
         title=tt("CopterSense"), gloss="sensing ports", check=[]),
    # (2) foundations: plant theorems and the loop (lower), spec facts and algebra (upper)
    dict(id="plant", x=4.45, y=1.75, kind="lemma",
         title=tt("step_spec") + ", " + tt("step_unique") + r",\\" + tt("Mplant_qnormSq") + r", Gr\"onwall",
         gloss="plant theorems",
         check=[P + "step_spec", P + "step_unique", P + "Mplant_qnormSq", P + "norm_traj_sub_le"]),
    dict(id="loop", x=6.70, y=1.75, kind="lemma",
         title=tt("Mctrl") + ", " + tt("Mplant") + r",\\" + tt("Mloop"), gloss="closed loop",
         check=[M + "Mctrl", M + "Mplant", M + "Mloop", M + "mem_Mplant_iff_plant",
                M + "traceValues_posTarget"]),
    dict(id="spec", x=1.62, y=2.62, kind="lemma",
         title=tt("allowance_rule") + r",\\" + tt("span_legs") + r", \texttt{h}$\rho\delta$, \texttt{h}$\delta$",
         gloss="spec facts",
         check=[M + "allowance_rule", M + "span_legs", M + "horizonTicks_eq", M + "hρδ", M + "hδ"]),
    dict(id="algebra", x=4.45, y=2.62, kind="lemma",
         title=tt("chain") + r",\\" + tt("refines_sound"), gloss="contract algebra",
         check=[C + "chain", C + "refines_sound", M + "refines_of_inter_subset"]),
    # (3) lemmas
    dict(id="safe", x=1.70, y=3.47, kind="lemma",
         title=tt("safe_of_parts"), gloss="+ geometry lemmas (4)",
         check=[M + "safe_of_parts", M + "polyDist_le", M + "polyDist_of_inColumn",
                M + "down_of_inSafe", M + "down_of_polyDist"]),
    dict(id="arrive", x=3.90, y=3.47, kind="lemma",
         title=tt("arrive_lemma") + r",\\" + tt("prox_of_sat"), gloss=None,
         check=[M + "arrive_lemma", M + "prox_of_sat"]),
    dict(id="guar", x=3.40, y=4.18, kind="lemma",
         title=tt("mission_of_guarantees"), gloss="guarantees imply mission",
         check=[M + "mission_of_guarantees"]),
    dict(id="navA", x=6.60, y=4.18, kind="lemma", width=2.40,
         title=tt("navA_of_loop"), gloss="+ port, force lemmas (9)",
         check=[M + "navA_of_loop", M + "port32", M + "portP", M + "f32Bd_of", M + "f64Bd_of",
                M + "specForce_bound", M + "accel_bounds", M + "amax_le",
                M + "tickSpecForce_startP", M + "abs_le_of_near"]),
    # (4) the sub-contracts and the assembly
    dict(id="track", x=1.55, y=5.15, kind="lemma", big=True,
         title=tt("track_contract"), gloss="tracking, pacing",
         check=[M + "track_contract"]),
    dict(id="nav", x=3.40, y=5.15, kind="lemma", big=True,
         title=tt("nav_contract"), gloss="controller alone",
         check=[M + "nav_contract"]),
    dict(id="sub", x=6.05, y=5.15, kind="lemma", big=True, width=2.20,
         title=tt("mission_of_sub"), gloss="assembly",
         check=[M + "mission_of_sub"]),
    # (5) the top
    dict(id="mission", x=3.95, y=6.05, kind="lemma", big=True,
         title=tt("mission_contract"), gloss="the mission",
         check=[M + "mission_contract"]),
    dict(id="nonvac", x=6.90, y=6.05, kind="lemma",
         title=tt("mission_nonvacuous"), gloss="a behavior exists",
         check=[M + "mission_nonvacuous"]),
]
LEGEND = (0.62, 6.27, 0.20)   # x, y of the first entry, step down

# ---------------------------------------------------------------------------------------------
#  Edges: (style, TikZ path between node anchors). "use" = is used by (solid, upward);
#  "hyp" = hypothesis of (dashed). Paths name nodes by their ids, prefixed pg.
# ---------------------------------------------------------------------------------------------
EDGES = [
    # trusted -> foundations
    ("use", "(pgvf.north) -- (pgvf.north |- pgplant.south)"),
    ("use", "([xshift=2.5mm]pglift.north) -- ([xshift=2.5mm]pglift.north |- pgloop.south)"),
    # foundations -> lemmas
    ("use", "([xshift=-3mm]pgspec.north) -- ([xshift=-3mm]pgspec.north |- pgsafe.south)"),
    ("use", "(pgspec.east) -| ([xshift=-4.2mm]pgguar.south)"),
    ("use", "([xshift=11.5mm]pgplant.north) -- ([xshift=11.5mm]pgplant.north |- pgnavA.south)"),
    ("use", "(pgloop.north) -- (pgloop.north |- pgnavA.south)"),
    ("use", f"(pgsense.east) -| ({SENSE_X},4.18) -- (pgnavA.east)"),
    # lemmas -> lemmas
    ("use", "(pgsafe.north) |- (pgguar.west)"),
    ("use", "(pgarrive.north) -- (pgarrive.north |- pgguar.south)"),
    # -> the assembly
    ("use", "([xshift=7mm]pgalgebra.north) -- ([xshift=7mm]pgalgebra.north |- pgsub.south)"),
    ("use", "(pgnavA.north) -- (pgnavA.north |- pgsub.south)"),
    ("use", "([xshift=10mm]pgguar.north) |- (pgsub.west)"),
    # -> the mission
    ("use", "([xshift=-6mm]pgsub.north) |- (pgmission.east)"),
    ("use", "(pgnav.north) -- (pgnav.north |- pgmission.south)"),
    ("use", "(pgtrack.north) -- (pgmission.south west)"),
    # hypotheses of the open sub-contracts
    ("hyp", f"(pgworld.north) |- ({HYP_X},{JOIN_Y}) -- ({HYP_X},{BUS_Y}) -| (pgnav.south)"),
    ("hypline", f"(pglibm.north) -- (pglibm.north |- 0,{JOIN_Y})"),
    ("hyp", f"(pgtrack.south |- 0,{BUS_Y}) -- (pgtrack.south)"),
]


# ---------------------------------------------------------------------------------------------
#  Axiom audit
# ---------------------------------------------------------------------------------------------
LINE = re.compile(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")


def parse_axioms(text: str) -> dict[str, set[str]]:
    out: dict[str, set[str]] = {}
    for line in text.splitlines():
        m = LINE.match(line.strip())
        if m:
            out[m.group(1)] = {a.strip() for a in (m.group(2) or "").split(",") if a.strip()}
    return out


def run_lean(args: list[str], stdin: str | None = None) -> str:
    r = subprocess.run(["lake", "env", "lean", *args], cwd=HERE, input=stdin, text=True,
                       capture_output=True)
    if r.returncode != 0 and "error" in (r.stdout + r.stderr):
        sys.exit("lean failed:\n" + r.stdout + r.stderr)
    return r.stdout + r.stderr


def audit(saved: Path | None, use_lean: bool) -> tuple[dict[str, set[str]], str]:
    if saved is not None:
        text, source = saved.read_text(), str(saved)
    else:
        text, source = run_lean(["AxiomCheck.lean"]), "lake env lean AxiomCheck.lean"
    ax = parse_axioms(text)
    wanted = [n for node in NODES for n in node["check"]]
    missing = [n for n in dict.fromkeys(wanted) if n not in ax]
    if missing:
        if not use_lean:
            sys.exit("not in the axiom output: " + ", ".join(missing))
        query = "import Contracts\nimport Contracts.Mission.Theorem\n" + "".join(
            f"#print axioms {n}\n" for n in missing)
        ax.update(parse_axioms(run_lean(["--stdin"], query)))
        still = [n for n in missing if n not in ax]
        if still:
            sys.exit("no axiom report for: " + ", ".join(still))
        source += f" + #print axioms of {len(missing)} more declarations"
    return ax, source


def status(node: dict, ax: dict[str, set[str]]) -> str:
    if node["kind"] == "trusted":
        return "trusted"
    used = set().union(*(ax[n] for n in node["check"]))
    if "sorryAx" in used:
        return "open"
    if used <= CLEAN:
        return "proved"
    sys.exit(f"{node['id']}: unexpected axioms {sorted(used - CLEAN)}")


# ---------------------------------------------------------------------------------------------
#  TikZ
# ---------------------------------------------------------------------------------------------
HEADER = r"""% ==================================================================
%  Proof graph -- the dependency graph of the mission theorem
%  mission_contract (cpp2lean/contracts, Contracts/Mission/Theorem.lean),
%  drawn as lanes from bottom to top: the trusted base and the
%  hypotheses; the foundations (plant theorems, the closed loop Mctrl,
%  Mplant, Mloop, the contract algebra, the spec facts); the lemmas;
%  the contracts (the assembly mission_of_sub and the two sub-contracts
%  nav_contract and track_contract, which mission_contract applies, and
%  mission_nonvacuous). Arrows mean "is used by"; a dashed arrow carries
%  hypotheses. A box stands for its Lean declarations; an arrow from a
%  box of several means that one of them is used.
%  Node status is drawn: white = proved (axioms propext, Classical.choice,
%  Quot.sound only), ochre = open (depends on sorryAx), gray = trusted
%  definition or hypothesis.
%  GENERATED by cpp2lean/contracts/proofgraph.py from the axiom audit;
%  do not edit, rerun the script. Audit read:
%  %%SOURCE%%
%  Status as drawn:
%%STATUS%%
%  one sigconf text width (8.2 cm), placed as a plain figure in one of
%  the two text areas, \input{figs/proofgraph} at natural size (no
%  \resizebox), pdfLaTeX
%  Preamble:  \usepackage{tikz}  \usetikzlibrary{arrows.meta,calc,positioning,fit,backgrounds}
%  (and amssymb for \mathbb outside acmart)
%  TikZ only, no image. Titles \footnotesize, bodies \scriptsize, nothing
%  smaller. Palette shared with figs/translator.tex and figs/harness.tex;
%  style names are prefixed pg so the figures can live in one document.
% ==================================================================
\definecolor{fwInk}{HTML}{22252A}%
\definecolor{fwMute}{HTML}{8A8F96}%
\definecolor{fwHair}{HTML}{C9CCD1}%
\definecolor{fwOchre}{HTML}{C4860F}%
\definecolor{fwBlue}{HTML}{1E3F7C}%
\begin{tikzpicture}[x=1cm, y=1cm, line cap=round, line join=round,
  pgbox/.style={draw=fwInk, line width=0.5pt, rounded corners=2pt, align=center, font=\scriptsize, inner sep=2pt, text=fwInk},
  pgproved/.style={pgbox, fill=white},
  pgopen/.style={pgbox, fill=fwOchre!22, draw=fwOchre!70!fwInk},
  pgtrusted/.style={pgbox, fill=fwHair!55, draw=fwMute},
  pgbig/.style={font=\footnotesize},
  pggloss/.style={font=\scriptsize, text=fwMute},
  pglane/.style={draw=fwHair, fill=fwHair!12, rounded corners=3pt, line width=0.4pt},
  pglanelbl/.style={font=\scriptsize\itshape, text=fwMute, inner sep=1pt, rotate=90},
  pgarr/.style={-{Stealth[length=1.6mm,width=1.3mm]}, line width=0.5pt, draw=fwInk},
  pgharr/.style={pgarr, dashed, draw=fwMute},
  pghline/.style={line width=0.5pt, dashed, draw=fwMute},
  pgnote/.style={font=\scriptsize, text=fwMute, inner sep=1pt},
]
"""


def node_tex(node: dict, st: str) -> str:
    style = "pg" + st + (", pgbig" if node.get("big") else "")
    if node.get("y") == TROW_Y:
        style += ", minimum height=6.2mm"
    if node.get("width"):
        style += f", minimum width={node['width']:.2f}cm"
    body = node["title"]
    if node.get("inline"):
        body += r"\ {\color{fwMute}" + node["inline"] + "}"
    if node.get("gloss"):
        body += r"\\[-1pt]{\scriptsize\color{fwMute}" + node["gloss"] + "}"
    return f"\\node[{style}] (pg{node['id']}) at ({node['x']:.2f},{node['y']:.2f}) {{{body}}};\n"


def legend_tex() -> str:
    x, y, step = LEGEND
    out = []
    for i, (st, label) in enumerate([("proved", "proved"), ("open", r"open (\texttt{sorry})"),
                                     ("trusted", "trusted, hypothesis")]):
        yy = y - i * step
        out.append(f"\\node[pg{st}, minimum width=3mm, minimum height=2mm, inner sep=0pt] at ({x + 0.15:.2f},{yy:.2f}) {{}};\n")
        out.append(f"\\node[pgnote, anchor=west] at ({x + 0.36:.2f},{yy:.2f}) {{{label}}};\n")
    return "".join(out)


def render(ax: dict[str, set[str]], source: str) -> tuple[str, dict[str, str]]:
    stats = {n["id"]: status(n, ax) for n in NODES}
    lines = "".join(
        f"%    {n['id']:<8} {stats[n['id']]:<8} "
        f"{len(n['check']) or '-'} {'declaration' if len(n['check']) == 1 else 'declarations' if n['check'] else ''}\n"
        for n in NODES)
    source += ", " + datetime.date.today().isoformat()
    tex = HEADER.replace("%%SOURCE%%", source).replace("%%STATUS%%\n", lines)
    tex += "% ================= lanes ==========================================\n"
    tex += "\\begin{scope}[on background layer]\n"
    for _, _, y0, y1 in LANES:
        tex += f"\\fill[pglane] ({LANE_X0:.2f},{y0:.2f}) rectangle ({LANE_X1:.2f},{y1:.2f});\n"
    tex += "\\end{scope}\n"
    for _, label, y0, y1 in LANES:
        tex += f"\\node[pglanelbl] at ({LANE_X0 / 2:.2f},{(y0 + y1) / 2:.2f}) {{{label}}};\n"
    tex += "% ================= nodes ==========================================\n"
    for n in NODES:
        tex += node_tex(n, stats[n["id"]])
    tex += "% ================= edges: is used by (solid), hypotheses (dashed) ==\n"
    style = {"use": "pgarr", "hyp": "pgharr", "hypline": "pghline"}
    for kind, path in EDGES:
        tex += f"\\draw[{style[kind]}] {path};\n"
    tex += "% ================= legend =========================================\n"
    tex += legend_tex()
    tex += "\\end{tikzpicture}%\n"
    return tex, stats


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--axioms", type=Path, help="saved output of lake env lean AxiomCheck.lean")
    ap.add_argument("--no-lean", action="store_true", help="never run Lean")
    ap.add_argument("--out", type=Path, default=DEFAULT_OUT)
    a = ap.parse_args()
    if a.no_lean and a.axioms is None:
        sys.exit("--no-lean needs --axioms")
    ax, source = audit(a.axioms, not a.no_lean)
    tex, stats = render(ax, source)
    a.out.write_text(tex)
    for n in NODES:
        print(f"{n['id']:<8} {stats[n['id']]}")
    print("wrote", a.out)


if __name__ == "__main__":
    main()
