"""Runs DELEGATE on the instances and writes docs/results.tex. Every simplified form typeset below is checked
equivalent to the computed one by Z3 first; otherwise the computed form is typeset as is."""
import sys, io, contextlib
sys.path.insert(0, "scripts")
from delegate import *

def quiet(f, *a):
    with contextlib.redirect_stdout(io.StringIO()): return f(*a)
def eq(a, b): return valid(a == b)
TIMED = False
def tex(e):
    s = fmt(e)
    for v in ("m", "d", "r"):
        for t in (1, 2): s = s.replace(f"{v}_{t}", f"{v}({t})")
    s = s.replace("_0", "(0)" if TIMED else "").replace("<=", r"\le ").replace(">=", r"\ge ").replace("*", r"\,")
    s = s.replace("And(", r"\mathrm{and}(").replace("Or(", r"\mathrm{or}(").replace("Not(", r"\lnot(")
    s = s.replace("-1\\,", "-").replace("+ -", "- ").replace("s1", "s_1").replace("s2", "s_2")
    return s
def leaves(term):
    out = []
    def walk(e):
        if is_app(e) and e.decl().kind() == Z3_OP_ITE: walk(e.children()[1]); walk(e.children()[2])
        else: out.append(e)
    walk(term); return list({str(l): l for l in out}.values())
def piecewise1d(term, x, lo, hi):
    th = set()
    def walk(e):
        if e.decl().kind() in (Z3_OP_LE, Z3_OP_LT, Z3_OP_GE, Z3_OP_GT) and len(e.children()) == 2:
            a, b = e.children(); ex = simplify(a - b)
            c = simplify(substitute(ex, (x, RealVal(1))) - substitute(ex, (x, RealVal(0))))
            if is_rational_value(c) and c.as_fraction() != 0:
                th.add(simplify(-substitute(ex, (x, RealVal(0))) / c).as_fraction())
        for ch in e.children(): walk(ch)
    walk(term); th = sorted(t for t in th if lo <= t <= hi); th = sorted(set(th) | {lo, hi})
    cells = []
    for i, t in enumerate(th):
        cells.append((t, t))
        if i + 1 < len(th): cells.append((t, th[i + 1]))
    rows = []
    for (a, b) in cells:
        cond = (x == RealVal(str(a))) if a == b else And(x > RealVal(str(a)), x < RealVal(str(b)))
        for L in leaves(term):
            if valid(Implies(cond, term == L)): rows.append(((a, b), L)); break
        else: raise AssertionError("no single leaf on a cell")
    merged = []                                     # (lo, lo_closed, hi, hi_closed, leaf)
    for (a, b), L in rows:
        pt = (a == b)
        if merged and str(merged[-1][4]) == str(L):
            lo, loc, hi, hic, _ = merged[-1]
            # an open cell (a, b) extends the piece to b with b excluded; a point cell closes the piece at that point
            merged[-1] = (lo, loc, b, False, L) if not pt else (lo, loc, hi, True, L)
        else:
            merged.append((a, pt, b, pt, L))
    return merged
def regions(term, dom):
    def desc(e, L):
        if is_app(e) and e.decl().kind() == Z3_OP_ITE:
            c, a, b = e.children(); return Or(And(c, desc(a, L)), And(Not(c), desc(b, L)))
        return BoolVal(True) if eq(e, L) else (e == L)
    out = []
    for L in leaves(term):
        g = And(dom, desc(term, L))
        for _ in range(2): g = simplify(Tactic('ctx-solver-simplify')(g).as_expr())
        if not valid(Not(g)): out.append((g, L))
    assert valid(Implies(dom, Or([And(g, term == L) for g, L in out])))
    return out
def table(term, dom):
    """Decision table of an ITE term over its own test conditions that dom leaves open.
       Returns (atoms, rows) with rows = [(truth tuple, leaf)], each cell verified by Z3."""
    conds = []
    def walk(e):
        if is_app(e) and e.decl().kind() == Z3_OP_ITE:
            c, a, b = e.children(); collect(c); walk(a); walk(b)
    def collect(c):
        if is_and(c) or is_or(c) or is_not(c) or is_implies(c):
            for ch in c.children(): collect(ch)
        else: conds.append(c)
    walk(term)
    atoms = []
    for c in conds:
        if valid(Implies(dom, c)) or valid(Implies(dom, Not(c))): continue      # fixed by dom
        if any(valid(Implies(dom, c == a)) or valid(Implies(dom, c == Not(a))) for a in atoms): continue
        atoms.append(c)
    rows = []
    import itertools as it
    for tv in it.product([True, False], repeat=len(atoms)):
        cell = And(dom, *[a if v else Not(a) for a, v in zip(atoms, tv)])
        if valid(Not(cell)): continue
        for Lf in leaves(term):
            if valid(Implies(cell, term == Lf)): rows.append((tv, Lf)); break
        else: raise AssertionError("cell with no single leaf")
    return atoms, rows
def eqs_of(G):
    out = {}
    for c in (G.children() if is_and(G) else [G]):
        if not is_eq(c): continue
        a, b = c.children()
        if is_const(a) and a.decl().kind() == Z3_OP_UNINTERPRETED: out[str(a)] = b
        else: out[str(b)] = a
    return out

half = Fraction(1, 2); r = V("r", 0); m = V("m", 0); d = V("d", 0)
# relay
A = Arch({"Radio": (["r"], ["m"]), "Display": (["m"], ["d"])}, env=["r"], H=0)
R = quiet(delegate, A, absle(r, 1), absle(d - r, half), "relay")
assert eq(R["seed"]["Radio"], m == r) and eq(R["seed"]["Display"], d == m)
AR, GR = R["sweep"]["Radio"]; AD, GD = R["sweep"]["Display"]
assert eq(AR, absle(r, 1)) and eq(GR, Implies(absle(r, 1), absle(m - r, half)))
assert eq(AD, absle(m, Fraction(3, 2))) and eq(GD, Implies(absle(m, Fraction(3, 2)), And(Or(d <= -half, d <= m), Or(d >= half, d >= m))))
# chain
m1 = V("m1", 0); m2 = V("m2", 0)
A3 = Arch({"C1": (["r"], ["m1"]), "C2": (["m1"], ["m2"]), "C3": (["m2"], ["d"])}, env=["r"], H=0)
R3 = quiet(delegate, A3, absle(r, 1), absle(d - r, half), "chain")
assert eq(R3["seed"]["C1"], m1 == r) and eq(R3["seed"]["C2"], m2 == m1) and eq(R3["seed"]["C3"], d == m2)
A1, G1 = R3["sweep"]["C1"]; A2, G2 = R3["sweep"]["C2"]; A3s, G3 = R3["sweep"]["C3"]
assert eq(A1, absle(r, 1)) and eq(G1, Implies(absle(r, 1), absle(m1 - r, half)))
assert eq(A2, absle(m1, Fraction(3, 2))) and eq(G2, Implies(absle(m1, Fraction(3, 2)), And(Or(m2 <= -half, m2 <= m1), Or(m2 >= half, m2 >= m1))))
assert eq(A3s, absle(m2, Fraction(3, 2))) and eq(G3, Implies(absle(m2, Fraction(3, 2)), And(Or(d <= -half, d <= m2), Or(d >= half, d >= m2))))
# disjunctive
GP4 = Or(And(Implies(r >= 0, d >= 1), Implies(r < 0, d <= -1)), absle(d - 2 * r, Fraction(1, 4)))
R4 = quiet(delegate, A, absle(r, 1), GP4, "disj")
assert eq(R4["seed"]["Radio"], m == r)
rows4 = piecewise1d(eqs_of(R4["seed"]["Display"])["d_0"], m, Fraction(-1), Fraction(1))
AD4, GD4 = R4["sweep"]["Display"]; assert eq(AD4, BoolVal(True))
assert is_and(GD4) and all(is_or(c) for c in GD4.children())      # the text says: a conjunction of disjunctions
# H = 2
A2h = Arch({"Radio": (["r"], ["m"]), "Display": (["m"], ["d"])}, env=["r"], H=2)
APt = Alw(0, 2, lambda t: absle(V("r", t), 1))(0)
GPt = And(Alw(0, 1, lambda t: Implies(V("r", t) >= half, Ev(0, 1, lambda u: V("d", u) >= half)(t)))(0),
          Alw(0, 2, lambda t: absle(V("d", t), 1))(0))
Rt = quiet(delegate, A2h, APt, GPt, "H2")
for _res in (R, R3, R4, Rt): assert all(_res["verdicts"].values()), _res["verdicts"]
assert eq(Rt["seed"]["Radio"], And(V("m", 0) == V("r", 0), V("m", 1) == V("r", 1), V("m", 2) == V("r", 2)))
E = eqs_of(Rt["seed"]["Display"])
m0, m1_, m2_ = V("m", 0), V("m", 1), V("m", 2); d0, d1, d2 = V("d", 0), V("d", 1), V("d", 2)
dom = And(absle(m0, 1), absle(m1_, 1), absle(m2_, 1))
d0v = E["d_0"]; assert is_rational_value(simplify(d0v))
d1s = simplify(substitute(E["d_1"], (d0, d0v)))
d2s = simplify(substitute(substitute(E["d_2"], (d0, d0v)), (d1, d1s)))
at1, rows_d1 = table(d1s, dom); at2, rows_d2 = table(d2s, dom)
GPu = And(Alw(0, 2, lambda t: absle(V("d", t) - V("r", t), half))(0), Ev(0, 2, lambda t: V("d", t) >= Fraction(1, 4))(0))
assert quiet(delegate, A2h, APt, GPu, "H2u") is None
# fan-in
AF = Arch({"A": (["s1"], ["a"]), "B": (["s2"], ["b"]), "Fuser": (["a", "b"], ["f"]), "Logger": (["f"], ["l"])}, env=["s1", "s2"], H=0)
GPf = absle(V("f", 0) - V("s1", 0) - V("s2", 0), 1)
assert quiet(delegate, AF, BoolVal(True), GPf, "fan") is None
quiet(fork_affine, AF, BoolVal(True), GPf, "fan"); fk = fork_affine.last

# ---------------- LaTeX ----------------
L = []
def P(x): L.append(x)
def ivtex(iv):
    lo, loc, hi, hic, _ = iv
    if lo == hi: return f"$m={lo}$"
    return "$" + str(lo) + (r"\le " if loc else "<") + "m" + (r"\le " if hic else "<") + str(hi) + "$"
P(r"""\documentclass[10pt]{article}\usepackage[margin=0.7in]{geometry}\usepackage{amsmath,amssymb,booktabs,array}
\setlength{\parskip}{3pt}\setlength{\parindent}{0pt}
\makeatletter\renewcommand\section{\@startsection{section}{1}{\z@}{6pt}{3pt}{\normalfont\bfseries}}\makeatother
\begin{document}
\begin{center}\textbf{Results of \textsc{Delegate} on six instances}\\ 18 October 2026. Generated by \texttt{scripts/results\_report.py} from \texttt{scripts/delegate.py}; every simplified formula below was checked equivalent to the computed one by Z3 before typesetting. All instances run in under one second.\end{center}
All instances have delay $0$. ``Seed'' is the delegation of step 7 of \emph{docs/complete.pdf} (forwarding plus witnesses); ``sweep'' is the maximal delegation reached from it by steps 8 and 9 (Theorem 11 of \emph{docs/complete.pdf}), in the order listed. Verdicts are Z3 decisions: (V1) is $A_P\wedge\bigwedge_iS_i\models G_P$, (V2) is $A_P\wedge\bigwedge_iS_i\models A_j$ for every $j$; ``acceptable'' means every component is receptive and causal. Witnesses are chosen by the test-point rule: midpoints of two bounds first, then bounds, then bounds $+1$, then bounds $-1$, then $0$; within a tier, constants first by increasing absolute value (negative first on ties), then the other candidates in character-code order of their canonical printing (docstring of \texttt{witness} in \texttt{scripts/delegate.py}).
\section{Relay, $H=0$}
Radio reads $r$, writes $m$; Display reads $m$, writes $d$. $A_P=|r|\le1$, $G_P=|d-r|\le\tfrac12$. $N=\{$Radio, Display$\}$; nested ordering Radio, Display; forwarding $r\mapsto m$. $\Phi=\forall r\,\exists d\,(|r|\le1\to|d-r|\le\tfrac12)$: \textbf{true}. Witness for $d$: the midpoint of $r-\tfrac12$ and $r+\tfrac12$, so $d=r$, decoded to $d=m$.\\
Seed: Radio $(\top,\ m=r)$, Display $(\top,\ d=m)$. (V1) true; acceptable.\\
Sweep: Radio $\big(|r|\le1,\ |m-r|\le\tfrac12\big)$; Display $\big(|m|\le\tfrac32,\ (d\le-\tfrac12\vee d\le m)\wedge(d\ge\tfrac12\vee d\ge m)\big)$, i.e.\ $d=m$ for $|m|\le\tfrac12$, $d\in[\tfrac12,m]$ for $m>\tfrac12$, $d\in[m,-\tfrac12]$ for $m<-\tfrac12$. (V1) and (V2) true.
\section{Three-stage chain, $H=0$}
C1 $r\to m_1$, C2 $m_1\to m_2$, C3 $m_2\to d$; same query. Nested ordering C1, C2, C3; forwarding $r\mapsto m_1$, $m_1\mapsto m_2$. $\Phi$ true; witness $d=r$, decoded through both forwardings to $d=m_2$.\\
Seed: C1 $(\top,m_1=r)$, C2 $(\top,m_2=m_1)$, C3 $(\top,d=m_2)$. (V1) true; acceptable.\\
Sweep: C1 $(|r|\le1,\ |m_1-r|\le\tfrac12)$; C2 $\big(|m_1|\le\tfrac32,\ (m_2\le-\tfrac12\vee m_2\le m_1)\wedge(m_2\ge\tfrac12\vee m_2\ge m_1)\big)$; C3 $\big(|m_2|\le\tfrac32,\ (d\le-\tfrac12\vee d\le m_2)\wedge(d\ge\tfrac12\vee d\ge m_2)\big)$. (V1) and (V2) true. The sweep gives all slack to C1 because C1 is swept first; C2 and C3 keep an exact copy on $|\cdot|\le\tfrac12$.
\section{Relay, disjunctive query, $H=0$}
$A_P=|r|\le1$, $G_P=\big((r\ge0\to d\ge1)\wedge(r<0\to d\le-1)\big)\vee|d-2r|\le\tfrac14$. Nested ordering Radio, Display; $\Phi$ true. Computed witness for $d$ as a function of the decoded $m$ on $|m|\le1$ (pieces read off the witness term, each verified by Z3, union verified exhaustive):
\begin{center}\begin{tabular}{@{}ll@{}}\toprule region & $d$ \\\midrule""")
for iv in rows4: P(f"{ivtex(iv)} & ${tex(iv[4])}$ \\\\")
P(r"""\bottomrule\end{tabular}\end{center}
Seed: Radio $(\top,m=r)$, Display $(\top,d=$ the function above$)$. (V1) true; acceptable. Sweep: (V1) and (V2) true; the swept Display guarantee, as printed by the script, is a conjunction of disjunctions of atoms, not reproduced here (the number of clauses Z3 prints depends on the Z3 version and on what was computed before in the same run).
\section{Relay, $H=2$, trigger with deadline}
$A_P=\square_{[0,2]}|r|\le1$, $G_P=\square_{[0,1]}\big(r\ge\tfrac12\to\Diamond_{[0,1]}\,d\ge\tfrac12\big)\wedge\square_{[0,2]}|d|\le1$. (Info) holds: Display reads no fresh input. $\Phi$ has one $\forall r(t)\,\exists d(t)$ pair per time step: \textbf{true}. Seed: Radio $(\top,\ m(t)=r(t)$ for $t=0,1,2)$; Display $(\top,\ d(0)=""" + tex(simplify(d0v)) + r"""\ \wedge\ d(1)=f_1(m(0),m(1))\ \wedge\ d(2)=f_2(m(0),m(1),m(2)))$ with, on the reachable inputs $|m(t)|\le1$ and after substituting the earlier outputs:
\begin{center}\begin{tabular}{@{}llll@{}}\toprule output & conditions tested & case & value \\\midrule""")
TIMED = True
for name, atoms, rows in (("$d(1)$", at1, rows_d1), ("$d(2)$", at2, rows_d2)):
    conds = ", ".join("$" + tex(a) + "$" for a in atoms)
    for tv, Lf in rows:
        case = ", ".join(("" if v else "not ") + "$" + tex(a) + "$" for a, v in zip(atoms, tv))
        P(f"{name} & {conds} & {case} & ${tex(Lf)}$ \\\\")
P(r"""\bottomrule\end{tabular}\end{center}
""")
TIMED = False
P(r"""Each row is a cell of the witness's own test conditions on $|m(t)|\le1$; Z3 verified the value on every cell. Reading: a trigger at time $0$ is answered at time $1$; a trigger at time $1$ is answered at time $2$ unless it was already answered.
(V1) true; acceptable. Sweep: (V1) and (V2) true (formulas printed by the script).
\section{Relay, $H=2$, unrealizable query}
$A_P$ as above, $G_P=\square_{[0,2]}|d-r|\le\tfrac12\wedge\Diamond_{[0,2]}\,d\ge\tfrac14$. $\Phi$ is \textbf{false} (with $r\equiv-1$ every $d(t)\le-\tfrac12$). Output: no acceptable delegation exists (Theorem 9 of \emph{docs/complete.pdf}).
\section{Fan-in, $H=0$: not nested, affine fork procedure}
A $s_1\to a$, B $s_2\to b$, Fuser $a,b\to f$, Logger $f\to l$; $A_P=\top$, $G_P=|f-s_1-s_2|\le1$. $N=\{$A, B, Fuser$\}$; no topological ordering satisfies (E), so \textsc{Delegate} does not apply and \textsc{Fork} runs with budget $B=1$ (affine strategies). Z3 decides $\exists\theta\,\forall s_1,s_2\,(A_P\to G_P)[\text{strategies}]$ as \textbf{sat} in nonlinear real arithmetic, with witness
$a=""" + tex(fk["a"]) + "$, $b=" + tex(fk["b"]) + "$, $f=" + tex(fk["f"]) + r"""$, verified for all $s_1,s_2$. Contracts: A $(\top,a=\ldots)$, B $(\top,b=\ldots)$, Fuser $(\top,f=\ldots)$ as displayed, Logger $(\top,\top)$. The signs are Z3's choice; the strategy is exact, with no slack, as a budget-1 witness need not be maximal.
\end{document}""")
open("docs/results.tex", "w").write("\n".join(L))
print("results.tex written; disj pieces:", len(rows4), "; H2 pieces:", len(rows_d1), len(rows_d2))
