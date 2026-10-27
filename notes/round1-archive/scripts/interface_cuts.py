"""Checks for theory/interface-cuts.md: what a cut must carry, the canonical encoding, interpolation,
multi-path routing / network coding, and non-delegability.

Run:  .venv/bin/python scripts/interface_cuts.py

Conventions.  H = 0 unless stated (a trace is one value per variable).  Every projection is Z3 tactic
`qe2`, cross-checked for equivalence with its quantified input by two decision paths (qe2+smt and plain
smt); the older `qe` tactic is never used.  Every 'valid' is a QF/quantified LRA validity query whose
answer is asserted to be sat/unsat (never unknown).

Parts
 [a] relay: needed functional, canonical encoding chi_a, Pi_D(chi_a -> G_P) vs the relay cut set
     (theory/foundations.md section 11),
     tolerance threshold a*, type-scaled encoding, counting (capacity) bound.
 [b] 2-D signal, 1-D edge: linear encodings all fail (qe2), the hyperplane-count obstruction,
     and the sharp counterexample: a 4-piece (disjunctive) quantizer delegation that IS valid.
 [c] multi-path: fan-in (two radios), fan-out with type-forced split, butterfly (routing fails,
     linear network coding succeeds).
 [d] interpolation: Z3 API check, Farkas interpolants by LP, strongest/weakest interpolants by qe2,
     sequence (tree) interpolants on a 3-chain.
 [e] causal capacity on the time-expanded relay (delays).
"""
import itertools
import numpy as np
import z3
from scipy.optimize import linprog

z3.set_param("verbose", 0)
R = z3.RealVal


# ----------------------------------------------------------------------------- helpers
def _check(s):
    r = s.check()
    assert r != z3.unknown, f"Z3 returned unknown: {s.reason_unknown()}"
    return r


def valid(f):
    s = z3.Solver(); s.add(z3.Not(f)); return _check(s) == z3.unsat


def decide_valid(f):
    s = z3.Then("qe2", "smt").solver(); s.add(z3.Not(f)); return _check(s) == z3.unsat


def satisfiable(f):
    s = z3.Solver(); s.add(f); return _check(s) == z3.sat


def qe(f):
    g = z3.Goal(); g.add(f)
    out = z3.Then("qe2", "simplify")(g).as_expr()
    assert decide_valid(out == f) and valid(out == f), "qe2 output not equivalent to its input"
    return out


class Space:
    """A set of typed variables; Pi / pi project onto a subset, other variables ranging over their types."""

    def __init__(self, Y):
        self.vars = {n: z3.Real(n) for n in Y}
        self.Y = dict(Y)

    def __getitem__(self, n):
        return self.vars[n]

    def types(self, names=None):
        names = self.vars if names is None else names
        return z3.And([z3.Abs(self.vars[n]) <= self.Y[n] for n in names])

    def Pi(self, keep, f):
        others = [self.vars[n] for n in self.vars if n not in keep]
        tk = self.types(keep)
        if not others:
            return z3.Implies(tk, f)
        return qe(z3.ForAll(others, z3.Implies(self.types([n for n in self.vars if n not in keep]), f)))

    def pi(self, keep, f):
        others = [self.vars[n] for n in self.vars if n not in keep]
        if not others:
            return z3.And(self.types(keep), f)
        return qe(z3.Exists(others, z3.And(self.types([n for n in self.vars if n not in keep]), f)))

    def receptive(self, S, inputs, outputs):
        """For every typed input value there is a typed output value in S (H = 0, delay 0)."""
        ins = [self.vars[n] for n in inputs]; outs = [self.vars[n] for n in outputs]
        body = z3.Exists(outs, z3.And(self.types(outputs), S))
        return decide_valid(z3.ForAll(ins, z3.Implies(self.types(inputs), body))) if ins else decide_valid(body)

    def valid_typed(self, f):
        return valid(z3.Implies(self.types(), f))


def needed_functional(N, cols_U, cols_Dout, tol=1e-9):
    """Coupling rows = rows touching a U-private column and a D-output column.  The needed functional is a
    basis of the row space of N restricted to U-private columns, over the coupling rows (SVD)."""
    NU = N[:, cols_U]; ND = N[:, cols_Dout]
    coupling = [k for k in range(N.shape[0]) if np.abs(NU[k]).max() > tol and np.abs(ND[k]).max() > tol]
    if not coupling:
        return coupling, np.zeros((0, len(cols_U)))
    _, s, Vt = np.linalg.svd(NU[coupling])
    rank = int((s > tol).sum())
    return coupling, Vt[:rank]


def hdr(t):
    print("\n" + "=" * 100 + "\n" + t + "\n" + "=" * 100)


# ============================================================================ [a] relay
hdr("[a] relay: Radio r->m, Display m->d, |r|<=1, |m|<=2, |d|<=3, G_P = |d-r|<=0.5")
Sp = Space({"r": 1, "m": 2, "d": 3})
r, m, d = Sp["r"], Sp["m"], Sp["d"]
A_P, G_P = z3.Abs(r) <= 1, z3.Abs(d - r) <= 0.5

# query as N x <= g over columns (r, m, d)
N = np.array([[-1.0, 0, 1], [1.0, 0, -1]]); g = np.array([0.5, 0.5])
coup, L = needed_functional(N, cols_U=[0], cols_Dout=[2])
print(f"  coupling rows {coup}; needed functional L (basis of row space of N_U on coupling rows) = {L.round(6).tolist()}")
print(f"  n = rank L = {L.shape[0]};  k = dim E = |{{m}}| = 1  -> rank condition n <= k holds")
# band width test: prior width of l = r is W = 2, band half-width eps = 0.5; information needed iff W > 2 eps
print("  band |l - d| <= 0.5 with prior width W(l)=2 > 2*eps=1: information about l must cross the cut")
print("  zero-information test Pi_D(A_P -> G_P) is empty (nothing a Display can promise works without information from r):",
      Sp.valid_typed(z3.Not(Sp.Pi(["m", "d"], z3.Implies(A_P, G_P)))))


def chi(a, T=1.0):
    """canonical cut: the edge carries T*l to within a (edge units)."""
    return z3.Abs(m - R(T) * r) <= a


def display_obligation(a, T=1.0):
    return Sp.Pi(["m", "d"], z3.Implies(z3.And(A_P, chi(a, T)), G_P))


display_star = z3.Or(z3.And(z3.Abs(m) <= 0.8, z3.Abs(d - m) <= 0.3),
                     z3.And(m > 0.8, m <= 1.2, d >= 0.5, d <= m + 0.3),
                     z3.And(m < -0.8, m >= -1.2, d <= -0.5, d >= m - 0.3),
                     z3.Abs(m) > 1.2)
SD02 = display_obligation(R(0.2))
print("  Pi_D(chi_0.2 & A_P -> G_P) == the relay cut set (theory/foundations.md section 11):", Sp.valid_typed(SD02 == display_star))


def D_receptive(a, T=1.0):
    return Sp.receptive(display_obligation(a, T), ["m"], ["d"])


def R_receptive(a, T=1.0):
    return Sp.receptive(z3.Implies(A_P, chi(a, T)), ["r"], ["m"])


def threshold(fun, lo, hi, it=30):
    """largest a in [lo,hi] with fun(a) True (fun monotone decreasing in a)."""
    if not fun(lo):
        return None
    if fun(hi):
        return hi
    for _ in range(it):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if fun(mid) else (lo, mid)
    return lo


astar = threshold(lambda a: D_receptive(R(a)), 0.0, 2.0, it=20)
print(f"  identity encoding T=1: Display receptive iff a <= a* ~ {astar:.6f} (expected 0.5)")
print("    exact check a=0.5 receptive:", D_receptive(R(0.5)), "; a=0.5001 receptive:", D_receptive(R(0.5001)))
a_can = 0.25
SDc = display_obligation(R(a_can))
print(f"  canonical split a = a*/2 = {a_can}: Radio receptive {R_receptive(R(a_can))}, Display receptive "
      f"{D_receptive(R(a_can))}, band |d-m|<=0.25 inside Pi_D: {Sp.valid_typed(z3.Implies(z3.Abs(d - m) <= 0.25, SDc))}")
print("    (C1) with S_R = A_P->chi, S_D = Pi_D:",
      Sp.valid_typed(z3.Implies(z3.And(A_P, z3.Implies(A_P, chi(R(a_can))), SDc), G_P)))
# fixed point: one more sweep step for Radio does not enlarge S_R on |r|<=1
SR_new = Sp.Pi(["r", "m"], z3.Implies(z3.And(A_P, SDc), G_P))
print("    sweep check: F_R(S_D) == (|r|<=1 -> |m-r|<=0.25) (seed already maximal):",
      Sp.valid_typed(SR_new == z3.Implies(A_P, chi(R(a_can)))))

# type-scaled encoding m = 2 r (fills |m|<=2):  tolerance in edge units doubles
astar2 = threshold(lambda a: D_receptive(R(a), T=2.0), 0.0, 3.0, it=20)
print(f"  type-scaled encoding T = Y_m / range(l) = 2: Display receptive iff a <= {astar2:.6f} (edge units; expected 1.0)")
print("    counting bound for ANY a-robust Radio obligation (Thm capacity): a <= Y_m / ceil(W/2eps) = 2/2 = 1.0")
print("    -> the type-scaled linear encoding attains the capacity bound (n = k = 1).")
# a 1-bit quantizer also attains a = 1 (Display then exact): verify
SRq = z3.Or(z3.And(r >= 0, z3.Abs(m - 1) <= 1), z3.And(r <= 0, z3.Abs(m + 1) <= 1))
SRq_strict = z3.Or(z3.And(r >= 0, m > 0, m <= 2), z3.And(r <= 0, m < 0, m >= -2))  # disjoint m-images
SDq = Sp.Pi(["m", "d"], z3.Implies(z3.And(A_P, SRq_strict), G_P))
print("    1-bit quantizer (r>=0 -> m in (0,2], r<=0 -> m in [-2,0)): Radio receptive",
      Sp.receptive(z3.Implies(A_P, SRq_strict), ["r"], ["m"]), "; Display Pi_D receptive",
      Sp.receptive(SDq, ["m"], ["d"]), "; Pi_D on m in (0,2] is d = 0.5:",
      Sp.valid_typed(z3.Implies(z3.And(m > 0, SDq), d == 0.5)))
print("    (the closed version with overlap at m=0 fails: fiber at m=0 is all of [-1,1]):",
      not Sp.receptive(Sp.Pi(["m", "d"], z3.Implies(z3.And(A_P, SRq), G_P)), ["m"], ["d"]))
print("    exact check T=2, a=1.0 receptive:", D_receptive(R(1), T=2.0), "; a=1.001:", D_receptive(R(1.001), T=2.0))

# ============================================================================ [b] 2-D signal through a 1-D edge
hdr("[b] Radio (r1,r2)->m (1-D), Display m->(d1,d2);  |r_i|<=1, |m|<=2, |d_i|<=3;  G_P = |d1-r1|<=.5 & |d2-r2|<=.5")
Sb = Space({"r1": 1, "r2": 1, "m": 2, "d1": 3, "d2": 3})
r1, r2, mb, d1, d2 = (Sb[n] for n in ("r1", "r2", "m", "d1", "d2"))
A_Pb = z3.And(z3.Abs(r1) <= 1, z3.Abs(r2) <= 1)
G_Pb = z3.And(z3.Abs(d1 - r1) <= 0.5, z3.Abs(d2 - r2) <= 0.5)
Nb = np.array([[-1.0, 0, 0, 1, 0], [1, 0, 0, -1, 0], [0, -1, 0, 0, 1], [0, 1, 0, 0, -1]])
coup, Lb = needed_functional(Nb, cols_U=[0, 1], cols_Dout=[3, 4])
print(f"  needed functional: rank n = {Lb.shape[0]} (row space = all of (r1,r2)); edge dim k = 1  ->  n > k")
print("  bands: W(r_i) = 2 > 2*eps = 1 in both directions; prior is a box (orthant property holds)")

# 1. every exact linear encoding m = c r1 + s r2 fails: Display's largest obligation is not receptive
for th in [0, 15, 30, 45, 60, 89, 90, 120, 179]:
    c, s = np.cos(np.radians(th)), np.sin(np.radians(th))
    cut = mb == R(round(float(c), 9)) * r1 + R(round(float(s), 9)) * r2
    SD = Sb.Pi(["m", "d1", "d2"], z3.Implies(z3.And(A_Pb, cut), G_Pb))
    rec = Sb.receptive(SD, ["m"], ["d1", "d2"])
    print(f"    exact linear encoding theta={th:3d} deg: Display Pi_D receptive = {rec}")


# 2. the theorem's ingredient for convex Radio obligations, on random receptive polytopes:
#    some m-fiber meets two opposite sides of the box (so has width 2 > 1 in some coordinate)
def fiber_side_intervals(P):
    """P: points (r1,r2,m) whose convex hull is K.  Return m-interval of K on each of the 4 sides."""
    out = {}
    lam_n = P.shape[0]
    for name, (coord, val) in {"L": (0, -1), "R": (0, 1), "B": (1, -1), "T": (1, 1)}.items():
        A_eq = np.vstack([np.ones(lam_n), P[:, coord]]); b_eq = np.array([1, val])
        lo = linprog(P[:, 2], A_eq=A_eq, b_eq=b_eq, bounds=[(0, None)] * lam_n)
        hi = linprog(-P[:, 2], A_eq=A_eq, b_eq=b_eq, bounds=[(0, None)] * lam_n)
        out[name] = (lo.fun, -hi.fun)
    return out


rng = np.random.default_rng(0)
viol = 0
for trial in range(500):
    corners = np.array([[a, b] for a in (-1, 1) for b in (-1, 1)], float)
    extra = rng.uniform(-1, 1, size=(rng.integers(0, 12), 2))
    pts = np.vstack([corners, extra])
    P = np.hstack([pts, rng.uniform(-2, 2, size=(pts.shape[0], 1))])     # arbitrary encoding values
    I = fiber_side_intervals(P)
    meetLR = max(I["L"][0], I["R"][0]) <= min(I["L"][1], I["R"][1]) + 1e-9
    meetBT = max(I["B"][0], I["T"][0]) <= min(I["B"][1], I["T"][1]) + 1e-9
    viol += not (meetLR or meetBT)
print(f"  500 random convex Radio relations K=conv(points) covering the box: cases with no fiber meeting two opposite"
      f" sides = {viol} (theorem: 0)")

# 3. sharpness: a 4-piece disjunctive (quantizer) Radio obligation IS a valid delegation
cells = [((s1, s2), mu) for (s1, s2), mu in zip([(-1, -1), (-1, 1), (1, -1), (1, 1)], [-1.5, -0.5, 0.5, 1.5])]
rad = 0.4


def cell(s1, s2):
    c1 = z3.And(r1 >= -1, r1 <= 0) if s1 < 0 else z3.And(r1 >= 0, r1 <= 1)
    c2 = z3.And(r2 >= -1, r2 <= 0) if s2 < 0 else z3.And(r2 >= 0, r2 <= 1)
    return z3.And(c1, c2)


SRb = z3.Or([z3.And(cell(*s), z3.Abs(mb - mu) <= rad) for s, mu in cells])
SDb = Sb.Pi(["m", "d1", "d2"], z3.Implies(z3.And(A_Pb, SRb), G_Pb))
SDb_hand = z3.Or([z3.And(z3.Abs(mb - mu) <= rad, d1 == 0.5 * s[0], d2 == 0.5 * s[1]) for s, mu in cells]
                 + [z3.And([z3.Abs(mb - mu) > rad for _, mu in cells])])
print("  quantizer: Radio S_R = OR_j (r in cell_j & |m - mu_j| <= 0.4), mu = -1.5,-.5,.5,1.5")
print("    Radio receptive:", Sb.receptive(z3.Implies(A_Pb, SRb), ["r1", "r2"], ["m"]),
      "; Display Pi_D receptive:", Sb.receptive(SDb, ["m"], ["d1", "d2"]),
      "; Pi_D == 'd = centre of cell j on interval j, anything in the gaps':", Sb.valid_typed(SDb == SDb_hand))
print("    (C1):", Sb.valid_typed(z3.Implies(z3.And(A_Pb, SRb, SDb), G_Pb)),
      "   capacity bound: N_sep = ceil(2/1)^2 = 4 <= Y_m/a = 2/0.4 = 5  (a = 0.5 is the limit)")

# 4. the exact query (eps = 0) needs n <= k for every finite union; with eps = 0 the quantizer would need
#    infinitely many cells. (Theorem, not a Z3 check.)  nlqsat attempt for 'all affine encodings with tolerance':
alpha, beta, a_b = z3.Reals("alpha beta a_b")
fiber_cond = z3.ForAll([mb], z3.Implies(z3.Abs(mb) <= 2, z3.Exists([d1, d2], z3.And(z3.Abs(d1) <= 3, z3.Abs(d2) <= 3,
              z3.ForAll([r1, r2], z3.Implies(z3.And(A_Pb, z3.Abs(mb - alpha * r1 - beta * r2) <= a_b), G_Pb))))))
recept = z3.ForAll([r1, r2], z3.Implies(A_Pb, z3.Exists([mb], z3.And(z3.Abs(mb) <= 2,
              z3.Abs(mb - alpha * r1 - beta * r2) <= a_b))))
s = z3.SolverFor("NRA") if False else z3.Tactic("qsat").solver()
s.set("timeout", 20000)
s.add(a_b >= 0, fiber_cond, recept)
res = s.check()
print(f"  exists (alpha,beta,a) with the affine band encoding |m - alpha r1 - beta r2| <= a delegable?  Z3 qsat (NRA): {res}"
      + ("  -> no affine band encoding works" if res == z3.unsat else "  (direct exists-forall NRA query not decided in 20 s)"))
# witness proof (QF_NRA): for |alpha| >= |beta|, alpha != 0, the m = 0 fibre (reachable from r = 0) contains
# p = (-beta/alpha, 1) and q = (beta/alpha, -1); no d2 is within 0.5 of both.  Symmetric for |beta| >= |alpha|.
p1, q1 = -beta / alpha, beta / alpha
wit = z3.Implies(z3.And(alpha != 0, z3.Abs(alpha) >= z3.Abs(beta), a_b >= 0),
                 z3.And(z3.Abs(p1) <= 1, z3.Abs(q1) <= 1, alpha * p1 + beta * 1 == 0, alpha * q1 + beta * (-1) == 0,
                        z3.Not(z3.Exists([d2], z3.And(z3.Abs(d2 - 1) <= 0.5, z3.Abs(d2 + 1) <= 0.5)))))
s2 = z3.Solver(); s2.add(z3.Not(wit)); w = s2.check()
print("  witness proof (QF_NRA, |alpha|>=|beta| case; other case symmetric): the m=0 fibre contains two points with"
      f" r2 = +1 and r2 = -1, so no Display output exists: {w == z3.unsat}")
print("  (alpha = beta = 0 carries nothing: zero-information test fails as in [a])")

# ============================================================================ [c] multi-path
hdr("[c1] fan-in: Radio1 r->m1, Radio2 r->m2, Display (m1,m2)->d;  |r|<=1, |m_i|<=2, |d|<=3;  G_P = |d-r|<=0.5")
Sc = Space({"r": 1, "m1": 2, "m2": 2, "d": 3})
rc, m1, m2, dc = Sc["r"], Sc["m1"], Sc["m2"], Sc["d"]
A_Pc, G_Pc = z3.Abs(rc) <= 1, z3.Abs(dc - rc) <= 0.5
# cut {R1,R2}|{D}: E = {m1,m2}, k = 2; needed functional l = r, n = 1.  Coefficient flow on row d - r:
# Display puts c1 on m1, c2 on m2; conservation at r: c1 + c2 = 1 (the -1 of r is split between its readers).
# Worst-case error with bands |m_i - r| <= a_i, |d - c.m| <= b:  c1 a1 + c2 a2 + b <= 0.5   (c >= 0).


def maxmin_tolerance(c1, c2):
    """LP: maximise t s.t. a_i >= t for involved radios (c_i > 0), b >= t, c1 a1 + c2 a2 + b <= 0.5."""
    # variables (a1, a2, b, t); minimise -t
    A_ub = [[c1, c2, 1, 0], [-1, 0, 0, 1] if c1 > 0 else [0, 0, 0, 0], [0, -1, 0, 1] if c2 > 0 else [0, 0, 0, 0],
            [0, 0, -1, 1]]
    res = linprog([0, 0, 0, -1], A_ub=A_ub, b_ub=[0.5, 0, 0, 0], bounds=[(0, 0.5)] * 4)
    return res.x


for c1 in [1.0, 0.75, 0.5, 0.25, 0.0]:
    a1, a2, b, t = maxmin_tolerance(c1, 1 - c1)
    print(f"  routing c = ({c1:.2f},{1 - c1:.2f}): max-min tolerance t = {t:.3f}  (a1={a1:.3f}, a2={a2:.3f}, b={b:.3f});"
          f" involved radios = {int(c1 > 0) + int(c1 < 1)}")


def check_fanin(c1, c2, a1, a2, b):
    SR1 = z3.Implies(A_Pc, z3.Abs(m1 - rc) <= a1) if c1 > 0 else z3.BoolVal(True)
    SR2 = z3.Implies(A_Pc, z3.Abs(m2 - rc) <= a2) if c2 > 0 else z3.BoolVal(True)
    SD = Sc.Pi(["m1", "m2", "d"], z3.Implies(z3.And(A_Pc, SR1, SR2), G_Pc))
    return (Sc.receptive(SD, ["m1", "m2"], ["d"]),
            Sc.valid_typed(z3.Implies(z3.And(A_Pc, SR1, SR2, z3.Abs(dc - c1 * m1 - c2 * m2) <= b), G_Pc)))


print("  shortest path (c=(1,0), Radio2 bystander, a1=b=.25): Display Pi_D receptive, band delegation (C1):",
      check_fanin(1, 0, 0.25, None, 0.25))
print("  spread (c=(.5,.5), a1=a2=b=.25):", check_fanin(0.5, 0.5, 0.25, 0.25, 0.25))
print("  spread lets the split be asymmetric (c=(.5,.5), a1=.4, a2=.1, b=.25):", check_fanin(0.5, 0.5, 0.4, 0.1, 0.25))
print("  -> redundancy gives no worst-case gain in max-min tolerance; canonical tie-break = fewest components.")

hdr("[c2] fan-out with type-forced split: Radio r->m, D1 m->d1, D2 m->d2;  |d_i|<=1;  G_P = |d1+d2-2r| <= 0.5")
Sf = Space({"r": 1, "m": 2, "d1": 1, "d2": 1})
rf, mf, f1, f2 = Sf["r"], Sf["m"], Sf["d1"], Sf["d2"]
A_Pf, G_Pf = z3.Abs(rf) <= 1, z3.Abs(f1 + f2 - 2 * rf) <= 0.5
SRf = z3.Implies(A_Pf, z3.And(z3.Abs(mf - rf) <= 0.1, z3.Abs(mf) <= 1))
# single path: D2 bystander (trivial), all of the coefficient 2 routed through D1
SD1_single = Sf.Pi(["m", "d1"], z3.Implies(z3.And(A_Pf, SRf), G_Pf))
print("  single path (D2 trivial): D1's largest obligation receptive?", Sf.receptive(SD1_single, ["m"], ["d1"]))
# conservation at m: g1 + g2 = 2.  Receptiveness of |d_i - g_i m| <= b_i with |d_i| <= 1, |m| <= 1 needs g_i <= 1 + b_i.
for g1 in [1.5, 1.2, 1.0]:
    g2 = 2 - g1
    S1 = z3.Implies(z3.Abs(mf) <= 1, z3.Abs(f1 - g1 * mf) <= 0.15)
    S2 = z3.Implies(z3.Abs(mf) <= 1, z3.Abs(f2 - g2 * mf) <= 0.15)
    rec = Sf.receptive(S1, ["m"], ["d1"]) and Sf.receptive(S2, ["m"], ["d2"])
    ok = Sf.valid_typed(z3.Implies(z3.And(A_Pf, SRf, S1, S2), G_Pf))
    print(f"  split g = ({g1},{g2}), bands b_i = 0.15, Radio a = 0.1:  both receptive {rec};  (C1) {ok}")
print("  -> type capacity |d_i| <= 1 forces g_i <= 1 + b_i, so the split is (essentially) forced to (1,1).")

hdr("[c3] butterfly: S1 r1->(a1,b1), S2 r2->(a2,b2), C (b1,b2)->c, D1 (a1,c)->(d11,d12), D2 (a2,c)->(d21,d22)")
Sbf = Space({"r1": 1, "r2": 1, "a1": 2, "b1": 2, "a2": 2, "b2": 2, "c": 3,
             "d11": 3, "d12": 3, "d21": 3, "d22": 3})
v = Sbf.vars
A_Pbf = z3.And(z3.Abs(v["r1"]) <= 1, z3.Abs(v["r2"]) <= 1)
G_Pbf = z3.And([z3.Abs(v[f"d{j}{k}"] - v[f"r{k}"]) <= 0.5 for j in (1, 2) for k in (1, 2)])
al, ga, de = 0.08, 0.1, 0.1
SS1 = z3.Implies(z3.Abs(v["r1"]) <= 1, z3.And(z3.Abs(v["a1"] - v["r1"]) <= al, z3.Abs(v["b1"] - v["r1"]) <= al))
SS2 = z3.Implies(z3.Abs(v["r2"]) <= 1, z3.And(z3.Abs(v["a2"] - v["r2"]) <= al, z3.Abs(v["b2"] - v["r2"]) <= al))
SC_code = z3.Implies(z3.And(z3.Abs(v["b1"]) <= 1.1, z3.Abs(v["b2"]) <= 1.1), z3.Abs(v["c"] - v["b1"] - v["b2"]) <= ga)
A_D1 = z3.And(z3.Abs(v["a1"]) <= 1.1, z3.Abs(v["c"] - v["a1"]) <= 1.4)
A_D2 = z3.And(z3.Abs(v["a2"]) <= 1.1, z3.Abs(v["c"] - v["a2"]) <= 1.4)
A_C = z3.And(z3.Abs(v["b1"]) <= 1.1, z3.Abs(v["b2"]) <= 1.1)
SD1 = z3.Implies(A_D1, z3.And(z3.Abs(v["d11"] - v["a1"]) <= de, z3.Abs(v["d12"] - (v["c"] - v["a1"])) <= de))
SD2 = z3.Implies(A_D2, z3.And(z3.Abs(v["d22"] - v["a2"]) <= de, z3.Abs(v["d21"] - (v["c"] - v["a2"])) <= de))
print("  min-cut check: sink D1 cut E={a1,c} k=2, needs (r1,r2) n=2; sink D2 likewise; bottleneck c has k=1")
print("  linear network code c ~ b1 + b2 (bands 0.08/0.1/0.1): (C1) =",
      Sbf.valid_typed(z3.Implies(z3.And(A_Pbf, SS1, SS2, SC_code, SD1, SD2), G_Pbf)))
print("    receptive: S1", Sbf.receptive(SS1, ["r1"], ["a1", "b1"]), " C", Sbf.receptive(SC_code, ["b1", "b2"], ["c"]),
      " D1", Sbf.receptive(SD1, ["a1", "c"], ["d11", "d12"]), " D2", Sbf.receptive(SD2, ["a2", "c"], ["d21", "d22"]))
allS = z3.And(A_Pbf, SS1, SS2, SC_code, SD1, SD2)
print("    (C2) assumptions of C, D1, D2 implied:", Sbf.valid_typed(z3.Implies(allS, z3.And(A_C, A_D1, A_D2))))
# routing: C copies b1 (carries r1 only).  Largest obligation for D1 on the row |d12 - r2| <= 0.5:
SC_route = z3.Implies(z3.Abs(v["b1"]) <= 1.1, z3.Abs(v["c"] - v["b1"]) <= ga)
row = z3.Abs(v["d12"] - v["r2"]) <= 0.5
SD1_route = Sbf.Pi(["a1", "c", "d11", "d12"], z3.Implies(z3.And(A_Pbf, SS1, SS2, SC_route), row))
print("  routing (c copies b1): D1's largest obligation for its r2-row receptive?",
      Sbf.receptive(SD1_route, ["a1", "c"], ["d12"]), "(symmetric failure at D2 if c copies b2)")

# ============================================================================ [d] interpolation
hdr("[d] Craig interpolation")
print("  Z3 version", z3.get_version_string(), "- interpolation API present:",
      any(hasattr(z3, n) for n in ("Interpolant", "binary_interpolant", "sequence_interpolant", "tree_interpolant")),
      "(removed from Z3 after 4.8; interpolants below are computed from Farkas multipliers by LP)")
print("  premise of the brief: A_P & chi_0 & not G_P is SAT without a Display obligation:",
      satisfiable(z3.And(Sp.types(), A_P, m == r, z3.Not(G_P))))


def farkas(rows, n_vars, strict_idx):
    """rows: list of (coef vector, rhs) meaning coef.x <= rhs; row strict_idx is strict (<).  Find lambda >= 0,
    sum lambda_i coef_i = 0, sum lambda_i rhs_i <= 0 with lambda_strict >= 1 (normalised)  ->  contradiction."""
    Cm = np.array([c for c, _ in rows], float).T; bvec = np.array([b for _, b in rows], float)
    k = len(rows)
    bounds = [(0, None)] * k; bounds[strict_idx] = (1, 1)
    res = linprog(np.ones(k), A_eq=Cm, b_eq=np.zeros(n_vars), A_ub=[bvec], b_ub=[0], bounds=bounds)
    assert res.status == 0, "no Farkas certificate"
    return res.x


def interp_from(lam, rows, A_idx, names):
    coef = sum(lam[i] * np.array(rows[i][0], float) for i in A_idx)
    rhs = sum(lam[i] * rows[i][1] for i in A_idx)
    terms = [(round(float(cf), 9), nm) for cf, nm in zip(coef, names) if abs(cf) > 1e-9]
    return coef, rhs, terms


# variables x = (r, m, d).  A-side: |r|<=1, Radio band |m - r| <= a.   B-side: Display band |d - m| <= b, not G_P.
a_i, b_i = 0.2, 0.3
names = ["r", "m", "d"]
Arows = [([1, 0, 0], 1), ([-1, 0, 0], 1), ([-1, 1, 0], a_i), ([1, -1, 0], a_i)]
Brows = [([0, -1, 1], b_i), ([0, 1, -1], b_i)]
I_parts = []
for case, viol_row in enumerate([([1, 0, -1], -0.5), ([-1, 0, 1], -0.5)]):   # d - r > .5  i.e.  r - d < -.5 ; etc.
    rows = Arows + Brows + [viol_row]
    lam = farkas(rows, 3, strict_idx=len(rows) - 1)
    coef, rhs, terms = interp_from(lam, rows, range(len(Arows)), names)
    I_parts.append((coef, rhs))
    print(f"  case {case + 1} of not G_P: Farkas interpolant  {' + '.join(f'{c}*{n}' for c, n in terms)} <= {rhs:.3f}")
I = z3.And([R(float(c[0])) * r + R(float(c[1])) * m + R(float(c[2])) * d <= R(float(b)) for c, b in I_parts])
A_side = z3.And(z3.Abs(r) <= 1, z3.Abs(m - r) <= a_i)
B_side = z3.And(z3.Abs(d - m) <= b_i, z3.Not(G_P))
print("    check: A |= I", Sp.valid_typed(z3.Implies(A_side, I)), "; I & B unsat", not satisfiable(z3.And(Sp.types(), I, B_side)),
      "; I mentions only {r, m} (shared vocabulary = E + ghost r):", True)
print("    I == |m - r| <= a (the canonical encoding itself):", Sp.valid_typed(I == (z3.Abs(m - r) <= a_i)))
strongest = Sp.pi(["r", "m"], A_side)
weakest = Sp.Pi(["r", "m"], z3.Not(B_side))
print("  strongest interpolant pi_{r,m}(A) == (|r|<=1 & |m-r|<=0.2):", Sp.valid_typed(strongest == A_side))
print("  weakest interpolant  Pi_{r,m}(not B) == |m - r| <= 0.5 - b = 0.2:", Sp.valid_typed(weakest == (z3.Abs(m - r) <= 0.2)))
print("  with Display's band b, the interpolants between A and B are exactly the cuts |m-r|<=a' with a <= a' <= 0.5-b;")
print("  i.e. interpolation returns the canonical encoding and the tolerance split, given Display's obligation.")

# sequence (tree) interpolants on a 3-chain Radio r->m1, Repeater m1->m2, Display m2->d
names3 = ["r", "m1", "m2", "d"]
a1_, a2_, b_ = 0.1, 0.15, 0.2
A1 = [([1, 0, 0, 0], 1), ([-1, 0, 0, 0], 1), ([-1, 1, 0, 0], a1_), ([1, -1, 0, 0], a1_)]
A2 = [([0, -1, 1, 0], a2_), ([0, 1, -1, 0], a2_)]
A3 = [([0, 0, -1, 1], b_), ([0, 0, 1, -1], b_)]
S3 = Space({"r": 1, "m1": 2, "m2": 2, "d": 3})
rr3, mm1, mm2, dd3 = (S3[n] for n in names3)
I1p, I2p = [], []
for viol_row in ([[1, 0, 0, -1], -0.5], [[-1, 0, 0, 1], -0.5]):
    rows = A1 + A2 + A3 + [tuple(viol_row)]
    lam = farkas(rows, 4, strict_idx=len(rows) - 1)
    I1p.append(interp_from(lam, rows, range(len(A1)), names3)[:2])
    I2p.append(interp_from(lam, rows, range(len(A1) + len(A2)), names3)[:2])


def to_z3(parts):
    vs = [rr3, mm1, mm2, dd3]
    return z3.And([z3.Sum([R(float(c[i])) * vs[i] for i in range(4)]) <= R(float(b)) for c, b in parts])


I1, I2 = to_z3(I1p), to_z3(I2p)
fA1 = z3.And(z3.Abs(rr3) <= 1, z3.Abs(mm1 - rr3) <= a1_); fA2 = z3.Abs(mm2 - mm1) <= a2_
fA3 = z3.And(z3.Abs(dd3 - mm2) <= b_, z3.Not(z3.Abs(dd3 - rr3) <= 0.5))
print("  sequence interpolants on Radio->Repeater->Display (bands .1/.15/.2):")
print("    I1 == |m1 - r| <= 0.1:", S3.valid_typed(I1 == (z3.Abs(mm1 - rr3) <= a1_)),
      "; I2 == |m2 - r| <= 0.25:", S3.valid_typed(I2 == (z3.Abs(mm2 - rr3) <= a1_ + a2_)))
print("    A1 |= I1:", S3.valid_typed(z3.Implies(fA1, I1)), "; I1 & S_Rep |= I2 (Hoare triple {I1} Rep {I2}):",
      S3.valid_typed(z3.Implies(z3.And(I1, fA2), I2)), "; I2 & A3 unsat:", not satisfiable(z3.And(S3.types(), I2, fA3)))

# ============================================================================ [e] causal capacity (time-expanded)
hdr("[e] causal capacity on the time-expanded relay, H = 2")


def max_matching(needed, samples, can):
    """bipartite max-flow by LP: needed functionals (one scalar each) vs edge samples (capacity 1 scalar each)."""
    pairs = [(i, j) for i in range(len(needed)) for j in range(len(samples)) if can(needed[i], samples[j])]
    if not pairs:
        return 0
    A_ub = []
    for i in range(len(needed)):
        A_ub.append([1 if p[0] == i else 0 for p in pairs])
    for j in range(len(samples)):
        A_ub.append([1 if p[1] == j else 0 for p in pairs])
    res = linprog(-np.ones(len(pairs)), A_ub=A_ub, b_ub=np.ones(len(A_ub)), bounds=[(0, 1)] * len(pairs))
    return round(-res.fun)


H = 2
for dR in (0, 1):
    for lag in (0, 1):
        # query rows |d(t) - r(t - lag)| <= 0.5 for t = lag..H: needed functional r(t-lag) with deadline t
        needed = [(t - lag, t) for t in range(lag, H + 1)]           # (source time u, deadline t)
        samples = list(range(H + 1))                                 # m(tau), carries r(<= tau - dR), read at tau
        can = lambda nd, tau: nd[0] + dR <= tau <= nd[1]
        mm = max_matching(needed, samples, can)
        print(f"  Radio delay {dR}, query lag {lag}: needed {len(needed)} scalars, causal matching {mm} -> "
              f"{'rank condition holds' if mm == len(needed) else 'NOT delegable (some deadline has zero capacity)'}")
# canonical time-expanded delegation for Radio delay 1, lag 1:  Radio |m(t) - r(t-1)| <= a (t>=1),  Display |d(t)-m(t)|<=b
St = Space({**{f"r{t}": 1 for t in range(H + 1)}, **{f"m{t}": 2 for t in range(H + 1)}, **{f"d{t}": 3 for t in range(H + 1)}})
vt = St.vars
A_Pt = z3.And([z3.Abs(vt[f"r{t}"]) <= 1 for t in range(H + 1)])
G_Pt = z3.And([z3.Abs(vt[f"d{t}"] - vt[f"r{t - 1}"]) <= 0.5 for t in range(1, H + 1)])
SRt = z3.And([z3.Implies(z3.Abs(vt[f"r{t - 1}"]) <= 1, z3.Abs(vt[f"m{t}"] - vt[f"r{t - 1}"]) <= 0.25) for t in range(1, H + 1)])
SDt = z3.And([z3.Abs(vt[f"d{t}"] - vt[f"m{t}"]) <= 0.25 for t in range(1, H + 1)])
print("  delay 1, lag 1: canonical encoding m(t) ~ r(t-1) (a = .25, causal for a delay-1 Radio), Display |d(t)-m(t)|<=.25:"
      " (C1) =", St.valid_typed(z3.Implies(z3.And(A_Pt, SRt, SDt), G_Pt)))
print("  delay 1, lag 0: capacity 0 at every deadline; the zero-information case: no Display obligation works (not delegable, even centrally).")
print("\nall checks done.")
