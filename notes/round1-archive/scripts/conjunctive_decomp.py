"""Constructive decomposition of a conjunctive (band) PolySTL query over an architecture graph.

theory/conjunctive-decomposition.md is the companion; section numbers below refer to it.

Pipeline (Algorithm DECOMPOSE, section 6):
  1. time-unroll: columns c = (v, t); writer, readers, type box, A_P box (env columns only).
  2. per query band k  (|N_k z - kappa_k| <= g_k):  cone of influence C_k (time-expanded column graph,
     delays + memory edges), candidate components COI_k, head column h(i,k) per candidate.
  3. band LP (Theorem 1): one band row per involved component, supported on causal columns of ports(i):
         kappa_i - w_i <= c_i z_h + beta_i . z <= kappa_i + w_i
     leaky flow:  N_k = sum_i n_{i,k} + rho_k,  sum_c leakcost_c(+-rho) + sum_i (+-kappa_i + w_i) <= g_k +- kappa_k
     receptiveness over the input box (Theorem 3):  |c_i| Y_h + w_i -+ kappa_i - h_X(-+beta_i) >= 0.
  4. choice rule R* (section 5):  support by extended leximin of shares (uninvolved = +inf),
     shares by water-filling, gains by water-filling of receptiveness margins, uniqueness certificate.
  5. assumptions by existential projection (Z3 qe2, cross-checked), full-horizon and time-sliced.
  6. Z3 verdicts: (C1) for the G's, (C1) and (C2) for the handed-out contracts, receptiveness+causality
     as the alternating quantifier formula, decided by qe2+smt and by the default engine.
"""
import itertools
import math
import sys
import time
from collections import defaultdict
from fractions import Fraction

import numpy as np
import z3
from scipy.optimize import linprog

INF = float("inf")
FTOL = 1e-9        # constraint slack used when freezing levels
LEVEL_TOL = 1e-7   # "cannot be raised above the level" test


# =============================================================================== small LP modeller
class LP:
    def __init__(self):
        self.lb, self.ub, self.names = [], [], []
        self.rows = []          # (dict idx->coef, lo, hi)

    def var(self, name, lb=-INF, ub=INF):
        self.lb.append(lb); self.ub.append(ub); self.names.append(name)
        return len(self.lb) - 1

    def add(self, expr, lo=-INF, hi=INF):
        self.rows.append((dict(expr), lo, hi))

    def copy(self):
        o = LP(); o.lb, o.ub, o.names = list(self.lb), list(self.ub), list(self.names)
        o.rows = list(self.rows); return o

    def solve(self, obj, maximize=False):
        n = len(self.lb)
        c = np.zeros(n)
        for j, a in obj.items():
            c[j] += a
        if maximize:
            c = -c
        Aub, bub, Aeq, beq = [], [], [], []
        for e, lo, hi in self.rows:
            r = np.zeros(n)
            for j, a in e.items():
                r[j] += a
            if lo == hi:
                Aeq.append(r); beq.append(lo)
            else:
                if hi < INF:
                    Aub.append(r); bub.append(hi)
                if lo > -INF:
                    Aub.append(-r); bub.append(-lo)
        res = linprog(c, A_ub=np.array(Aub) if Aub else None, b_ub=np.array(bub) if bub else None,
                      A_eq=np.array(Aeq) if Aeq else None, b_eq=np.array(beq) if beq else None,
                      bounds=list(zip([None if b == -INF else b for b in self.lb],
                                      [None if b == INF else b for b in self.ub])), method="highs")
        if res.status != 0:
            return None, None
        val = -res.fun if maximize else res.fun
        return res.x, val


def lin(*terms):
    """lin((coef, idx_or_dict), ...) -> dict"""
    out = defaultdict(float)
    for a, e in terms:
        if isinstance(e, dict):
            for j, b in e.items():
                out[j] += a * b
        else:
            out[e] += a
    return dict(out)


def leximax(lp, funcs):
    """Water-filling (progressive filling) leximin maximisation of the affine functions funcs[name] over lp.
    Returns (levels: name -> value, lp with the levels imposed as lower bounds)."""
    lp = lp.copy()
    free, levels = set(funcs), {}
    while free:
        q = lp.copy(); t = q.var("_t")
        for j in free:
            q.add(lin((1, funcs[j]), (-1, t)), lo=0)
        x, tstar = q.solve({t: 1}, maximize=True)
        if x is None:
            raise RuntimeError("leximax: infeasible")
        blocked = []
        for j in sorted(free):
            q2 = lp.copy()
            for jj in free:
                q2.add(funcs[jj], lo=tstar - FTOL)
            x2, v = q2.solve(funcs[j], maximize=True)
            if v is None or v <= tstar + LEVEL_TOL:
                blocked.append(j)
        if not blocked:                     # numerical guard; theory says some coordinate is blocked
            blocked = [min(free)]
        for j in free:                      # every free coordinate is at least the level
            lp.add(funcs[j], lo=tstar - FTOL)
        for j in blocked:
            levels[j] = tstar
            free.discard(j)
    return levels, lp


# =============================================================================== architecture
class System:
    def __init__(self, name):
        self.name = name
        self.cols = {}            # (v,t) -> dict(Y, lo, hi, writer)
        self.comps = {}           # name -> dict(ins, outs, d)
        self.bands = []           # dict(N, kappa, g, name)
        self.fixed = {}           # comp -> function(band, head) -> dict col->coef (normal up to positive scale)
        self.sign_override = {}   # (comp, band name) -> -1: gauge sign of an internal head coefficient
        self.fix_head = {}        # (comp, band name) -> value of the head coefficient c (ties shared heads)

    def var(self, v, Y, times, ap=None):
        for t in times:
            lo, hi = -Y, Y
            if ap is not None:
                lo, hi = max(lo, -ap), min(hi, ap)
            self.cols[(v, t)] = dict(Y=Y, lo=lo, hi=hi, writer=None)

    def comp(self, name, reads, writes, d=0):
        for c in writes:
            assert self.cols[c]["writer"] is None, c
            self.cols[c]["writer"] = name
            Y = self.cols[c]["Y"]; self.cols[c]["lo"], self.cols[c]["hi"] = -Y, Y   # A_P never constrains outputs
        self.comps[name] = dict(ins=set(reads), outs=set(writes), d=d)

    def band(self, N, g, kappa=0.0, name=None):
        self.bands.append(dict(N=dict(N), g=g, kappa=kappa, name=name or str(N)))

    # ---- time-expanded column graph
    def preds(self):
        P = defaultdict(set)
        for i, C in self.comps.items():
            for h in C["outs"]:
                for c in C["ins"]:
                    if c != h and c[1] <= h[1] - C["d"]:
                        P[h].add(c)
                for c in C["outs"]:
                    if c[1] < h[1]:
                        P[h].add(c)            # memory edge: own past output
        return P

    def back_closure(self, cols):
        P, seen, todo = self.preds(), set(cols), list(cols)
        while todo:
            c = todo.pop()
            for p in P[c]:
                if p not in seen:
                    seen.add(p); todo.append(p)
        return seen

    def forward_reach(self, src, removed):
        S = defaultdict(set)
        for h, ps in self.preds().items():
            for p in ps:
                S[p].add(h)
        seen, todo = {src}, [src]
        while todo:
            c = todo.pop()
            for s in S[c]:
                if s not in seen and s not in removed:
                    seen.add(s); todo.append(s)
        return seen

    def env(self, c):
        return self.cols[c]["writer"] is None

    def box(self, c):
        return self.cols[c]["lo"], self.cols[c]["hi"]

    # ---- per band structure
    def band_structure(self, band):
        Ck = self.back_closure(set(band["N"]))
        coi, heads, allowed = [], {}, {}
        for i, C in self.comps.items():
            outs = [c for c in C["outs"] if c in Ck]
            if not outs:
                continue
            tmax = max(c[1] for c in outs)
            hs = [c for c in outs if c[1] == tmax]
            if len(hs) > 1:
                raise NotImplementedError(f"{i}: several output columns at the head time (multi-head row)")
            h = hs[0]
            al = sorted({c for c in C["ins"] if c != h and c[1] <= h[1] - C["d"]} |
                        {c for c in C["outs"] if c[1] < h[1]})
            coi.append(i); heads[i] = h; allowed[i] = al
        return Ck, coi, heads, allowed

    def dominator_necessary(self, band):
        """Theorem 2(c): i is necessary for band k if some query column c (env, or an output of i) cannot reach
        the other query columns once i's other outputs are removed, and halfrange(c)*|N[c]| > g."""
        N, g = band["N"], band["g"]
        nec = set()
        for i, C in self.comps.items():
            for c, a in N.items():
                if not (self.env(c) or c in C["outs"]):
                    continue
                removed = set(C["outs"]) - {c}
                reach = self.forward_reach(c, removed)
                lo, hi = self.box(c)
                if not (reach & (set(N) - {c})) and abs(a) * (hi - lo) / 2 > g + 1e-12:
                    nec.add(i)
        return nec


# =============================================================================== the band LP
class BandLP:
    """LP of Theorem 1 for one query band and one support set."""

    def __init__(self, S, band, support, recept=True, boxes=None, no_recept=()):
        self.S, self.band, self.support = S, band, list(support)
        Ck, coi, heads, allowed = S.band_structure(band)
        self.Ck, self.heads, self.allowed = Ck, heads, allowed
        N, g, kq = band["N"], band["g"], band["kappa"]
        lp = LP(); self.lp = lp
        self.coef = {}            # (i, col) -> linear expr
        self.c_var, self.kap, self.w, self.lam, self.mplus, self.mminus = {}, {}, {}, {}, {}, {}
        self.decision = []        # indices of decision variables (for the uniqueness certificate)
        self.sigma = {}
        for i in self.support:
            h = heads[i]
            sig = (1 if N[h] > 0 else -1) if h in N else S.sign_override.get((i, band["name"]), 1)   # gauge
            self.sigma[i] = sig
            if i in S.fixed:
                nhat = S.fixed[i](band, h)
                lam = lp.var(f"lam[{i}]", 0, INF); self.lam[i] = lam; self.decision.append(lam)
                for col in [h] + allowed[i]:
                    if nhat.get(col, 0) != 0:
                        self.coef[(i, col)] = {lam: nhat[col]}
                assert nhat[h] * sig > 0, "fixed normal must have the head sign of the template"
            else:
                cv = lp.var(f"c[{i}]", 0 if sig > 0 else -INF, INF if sig > 0 else 0)
                if (i, band["name"]) in S.fix_head:
                    v = S.fix_head[(i, band["name"])]; lp.add({cv: 1.0}, lo=v, hi=v)
                self.coef[(i, h)] = {cv: 1.0}; self.decision.append(cv)
                for col in allowed[i]:
                    b = lp.var(f"beta[{i},{col}]"); self.coef[(i, col)] = {b: 1.0}; self.decision.append(b)
            self.kap[i] = lp.var(f"kappa[{i}]"); self.w[i] = lp.var(f"w[{i}]", 0, INF)
            self.decision += [self.kap[i], self.w[i]]
        # leaky flow
        cost_p, cost_m = {}, {}
        self.rho = {}
        for col in sorted(Ck):
            rho = lin((N.get(col, 0.0), {}))
            rho = defaultdict(float)
            touch = False
            for i in self.support:
                if (i, col) in self.coef:
                    touch = True
                    for j, a in self.coef[(i, col)].items():
                        rho[j] -= a
            if not touch and N.get(col, 0.0) == 0:
                continue
            lo, hi = S.box(col)
            tp, tm = lp.var(f"tp[{col}]"), lp.var(f"tm[{col}]")
            r = dict(rho)                  # rho = N[col] + r . x
            n0 = N.get(col, 0.0)
            # tp >= rho*hi, tp >= rho*lo ; tm >= -rho*hi, tm >= -rho*lo
            lp.add(lin((1, tp), (-hi, r)), lo=n0 * hi)
            lp.add(lin((1, tp), (-lo, r)), lo=n0 * lo)
            lp.add(lin((1, tm), (hi, r)), lo=-n0 * hi)
            lp.add(lin((1, tm), (lo, r)), lo=-n0 * lo)
            cost_p[tp] = 1.0; cost_m[tm] = 1.0
            self.rho[col] = (n0, r)
        bp = lin((1, cost_p), *[(1, self.kap[i]) for i in self.support], *[(1, self.w[i]) for i in self.support])
        bm = lin((1, cost_m), *[(-1, self.kap[i]) for i in self.support], *[(1, self.w[i]) for i in self.support])
        lp.add(bp, hi=kq + g)
        lp.add(bm, hi=g - kq)
        # receptiveness over the input box (Theorem 3, band template)
        for i in self.support:
            h = heads[i]; Yh = S.cols[h]["Y"]
            hp, hm = {}, {}
            for col in allowed[i]:
                if (i, col) not in self.coef:
                    continue
                lo, hi = (boxes or {}).get((i, col), S.box(col))
                e = self.coef[(i, col)]
                ap, am = lp.var(f"hp[{i},{col}]"), lp.var(f"hm[{i},{col}]")
                lp.add(lin((1, ap), (-hi, e)), lo=0); lp.add(lin((1, ap), (-lo, e)), lo=0)     # ap >= beta*hi, beta*lo
                lp.add(lin((1, am), (hi, e)), lo=0); lp.add(lin((1, am), (lo, e)), lo=0)       # am >= -beta*hi, -beta*lo
                hp[ap] = 1.0; hm[am] = 1.0
            cY = lin((self.sigma[i] * Yh, self.coef[(i, h)]))
            self.mplus[i] = lin((1, cY), (1, self.w[i]), (-1, self.kap[i]), (-1, hm))
            self.mminus[i] = lin((1, cY), (1, self.w[i]), (1, self.kap[i]), (-1, hp))
            if recept and i not in no_recept:
                lp.add(self.mplus[i], lo=0); lp.add(self.mminus[i], lo=0)

    def feasible(self):
        x, _ = self.lp.solve({})
        return x is not None

    def value(self, x, i, col):
        return sum(a * x[j] for j, a in self.coef.get((i, col), {}).items())


# =============================================================================== the choice rule
def sorted_ext(vec):
    return sorted(vec)


def lex_better(a, b, tol=1e-7):
    for x, y in zip(a, b):
        if x > y + tol:
            return True
        if x < y - tol:
            return False
    return False


def lex_equal(a, b, tol=1e-7):
    return all(abs(x - y) <= tol or (x == y) for x, y in zip(a, b))


def choose(S, band, rule="lean", recept=True, boxes=None, no_recept=(), log=print):
    """Return dict with support, shares, margins, the final LP point and diagnostics."""
    Ck, coi, heads, allowed = S.band_structure(band)
    out = dict(band=band, coi=coi, heads=heads)
    full = BandLP(S, band, coi, recept, boxes, no_recept)
    if not full.feasible():
        out["infeasible"] = True
        return out
    # claims: max individual share with everybody available
    out["claims"] = {i: full.lp.solve({full.w[i]: 1}, maximize=True)[1] for i in coi}
    # necessary components (LP) and by domination (Theorem 2)
    nec = [i for i in coi if not BandLP(S, band, [j for j in coi if j != i], recept, boxes, no_recept).feasible()]
    out["nec_lp"], out["nec_dom"] = nec, sorted(S.dominator_necessary(band) & set(coi))
    optional = [i for i in coi if i not in nec]
    cands = []
    if rule == "lean":
        subsets = [set(nec) | set(T) for r in range(len(optional) + 1) for T in itertools.combinations(optional, r)]
    elif rule == "egal":
        subsets = [set(coi)]
    else:
        raise ValueError(rule)
    for I in subsets:
        blp = BandLP(S, band, sorted(I), recept, boxes, no_recept)
        if not blp.feasible():
            continue
        levels, _ = leximax(blp.lp, {i: {blp.w[i]: 1.0} for i in blp.support})
        ext = sorted_ext([levels[i] for i in blp.support] + [INF] * (len(coi) - len(I)))
        cands.append((sorted(I), levels, ext))
    best = cands[0]
    for c in cands[1:]:
        if lex_better(c[2], best[2]):
            best = c
    ties = [c[0] for c in cands if lex_equal(c[2], best[2]) and c[0] != best[0]]
    out["candidates"] = [(c[0], {k: round(v, 6) for k, v in c[1].items()}) for c in cands]
    out["support"], out["shares"], out["support_ties"] = best[0], best[1], ties
    blp = BandLP(S, band, best[0], recept, boxes, no_recept)
    lp = blp.lp.copy()
    for i, v in best[1].items():
        lp.add({blp.w[i]: 1.0}, lo=v - FTOL)          # leximax-blocked: cannot rise above v
    margin_funcs = {}
    for i in blp.support:
        if i in no_recept:
            continue
        margin_funcs[(i, "+")] = blp.mplus[i]; margin_funcs[(i, "-")] = blp.mminus[i]
    mlev, lp = leximax(lp, margin_funcs) if margin_funcs else ({}, lp)
    out["margins"] = mlev
    # uniqueness certificate on the optimal face
    spread = 0.0
    face = {}
    for j in blp.decision:
        _, lo = lp.solve({j: 1.0}); _, hi = lp.solve({j: 1.0}, maximize=True)
        if lo is None or hi is None:
            raise RuntimeError(f"face LP failed for {blp.lp.names[j]}")
        face[blp.lp.names[j]] = (lo, hi); spread = max(spread, hi - lo)
    out["face"], out["spread"] = face, spread
    # representative: minimum l1 norm of the decision variables on the face (deterministic; = the point if unique)
    q = lp.copy(); obj = {}
    for j in blp.decision:
        a = q.var("_abs"); q.add({a: 1.0, j: -1.0}, lo=0); q.add({a: 1.0, j: 1.0}, lo=0); obj[a] = 1.0
    x, _ = q.solve(obj)
    out["x"], out["blp"] = x, blp
    return out


def extract_rows(res):
    """Per involved component: band row as (dict col->coef, kappa, w), after the positive-gain gauge flip."""
    blp, x = res["blp"], res["x"]
    S, band = blp.S, blp.band
    rows = {}
    for i in blp.support:
        cols = [blp.heads[i]] + blp.allowed[i]
        n = {c: blp.value(x, i, c) for c in cols}
        n = {c: v for c, v in n.items() if abs(v) > 1e-10}
        rows[i] = [n, x[blp.kap[i]], x[blp.w[i]]]
    # gauge flip (sign of an internal head column is a pure symmetry, Prop. 5.3): make the dominant gain positive
    for i in sorted(blp.support, key=lambda i: blp.heads[i][1]):
        h = blp.heads[i]
        lo, hi = S.box(h)
        if h in band["N"] or abs(lo + hi) > 1e-12:
            continue
        n, kap, w = rows[i]
        gains = {c: -v / n[h] for c, v in n.items() if c != h} if n.get(h) else {}
        if not gains:
            continue
        cd = max(sorted(gains), key=lambda c: abs(gains[c]))
        if gains[cd] < 0:
            for j in rows:
                if h in rows[j][0]:
                    rows[j][0][h] = -rows[j][0][h]
            n, kap, w = rows[i]
            if n[h] < 0:
                rows[i] = [{c: -v for c, v in n.items()}, -kap, w]
    return rows


def rat(v, den=10**6):
    return Fraction(v).limit_denominator(den)


# =============================================================================== Z3 stage
def valid(f):
    s = z3.Solver(); s.add(z3.Not(f)); r = s.check()
    assert r != z3.unknown, "Z3 returned unknown"
    return r == z3.unsat


def decide_valid(f):
    s = z3.Then("qe2", "smt").solver(); s.add(z3.Not(f)); r = s.check()
    assert r != z3.unknown, "Z3 returned unknown"
    return r == z3.unsat


def both_valid(f):
    a, b = decide_valid(f), valid(f)
    assert a == b, f"decision paths disagree: qe2+smt {a}, default {b}"
    return a


def qe_exists(vs, f):
    """Existential projection by qe2, cross-checked for equivalence with the quantified input (two decision paths)."""
    if not vs:
        return f
    src = z3.Exists(vs, f)
    g = z3.Goal(); g.add(src)
    out = z3.Then("qe2", "simplify")(g).as_expr()
    assert decide_valid(out == src) and valid(out == src), "qe2 output not equivalent to its input"
    return out


class Z3View:
    def __init__(self, S):
        self.S = S
        self.z = {c: z3.Real(f"{c[0]}_{c[1]}") for c in S.cols}
        self.types = z3.And([z3.And(self.z[c] >= -S.cols[c]["Y"], self.z[c] <= S.cols[c]["Y"]) for c in S.cols])
        self.AP = z3.And([z3.And(self.z[c] >= S.cols[c]["lo"], self.z[c] <= S.cols[c]["hi"])
                          for c in S.cols if S.env(c)] or [z3.BoolVal(True)])
        self.GP = z3.And([self.bandf(b["N"], rat(b["kappa"]), rat(b["g"])) for b in S.bands])

    def expr(self, n):
        return z3.Sum([z3.RealVal(rat(a)) * self.z[c] for c, a in n.items()]) if n else z3.RealVal(0)

    def bandf(self, n, kap, w):
        e = self.expr(n)
        return z3.And(e >= z3.RealVal(kap) - z3.RealVal(w), e <= z3.RealVal(kap) + z3.RealVal(w))

    def typed(self, cols):
        return z3.And([z3.And(self.z[c] >= -self.S.cols[c]["Y"], self.z[c] <= self.S.cols[c]["Y"]) for c in cols] or
                      [z3.BoolVal(True)])


def handout_and_verify(S, results, log=print):
    """results: list of choose() outputs, one per band.  Builds G_i, A_i (full and time-sliced), runs all checks."""
    Z = Z3View(S)
    rows = defaultdict(list)          # comp -> list of (head, n, kappa, w)
    for res in results:
        for i, (n, kap, w) in extract_rows(res).items():
            rows[i].append((res["blp"].heads[i], {c: rat(a) for c, a in n.items() if rat(a) != 0}, rat(kap), rat(w)))
    involved = sorted(rows)
    G = {i: z3.And([Z.bandf(n, kap, w) for _, n, kap, w in rows[i]]) for i in involved}
    for i in S.comps:
        G.setdefault(i, z3.BoolVal(True))
    verdict = {}
    base = z3.And(Z.types, Z.AP)
    verdict["nonvacuous: A_P & types & all G sat"] = z3.Solver().check(z3.And(base, *G.values())) == z3.sat
    verdict["(C1) for the guarantees: A_P & all G_i -> G_P"] = both_valid(z3.Implies(z3.And(base, *G.values()), Z.GP))
    # ---------- full-horizon assumptions
    A = {}
    for i in S.comps:
        if i not in involved:
            A[i] = z3.BoolVal(True); continue
        keep = S.comps[i]["ins"]
        elim = [Z.z[c] for c in S.cols if c not in keep]
        A[i] = qe_exists(elim, z3.And(base, *[G[j] for j in S.comps if j != i]))
    Sfull = {i: z3.Implies(A[i], G[i]) for i in S.comps}
    allS = z3.And(base, *Sfull.values())
    verdict["(C1) full-horizon contracts: A_P & all (A_i -> G_i) -> G_P"] = both_valid(z3.Implies(allS, Z.GP))
    if not verdict["(C1) full-horizon contracts: A_P & all (A_i -> G_i) -> G_P"]:
        sol = z3.Solver(); sol.add(allS, z3.Not(Z.GP)); assert sol.check() == z3.sat
        mdl = sol.model()
        ev = lambda c: mdl.eval(Z.z[c], model_completion=True)
        verdict["  counterexample trace (full horizon)"] = {f"{c[0]}({c[1]})": str(ev(c)) for c in sorted(S.cols)}
        verdict["  which assumptions fail on it"] = [i for i in S.comps if z3.is_false(z3.simplify(z3.substitute(A[i], *[(Z.z[c], ev(c)) for c in S.cols])))]
    verdict["(C2) full-horizon: A_P & all S_i -> A_j for all j"] = all(both_valid(z3.Implies(allS, A[j])) for j in S.comps)
    # ---------- time-sliced assumptions:  S_i^ts = AND_h ( A_i^h -> rows_h ),  A_i^h over inputs up to time(h)-d_i
    Ats, Sts = {}, {}
    for i in S.comps:
        if i not in involved:
            Ats[i], Sts[i] = {}, z3.BoolVal(True); continue
        d = S.comps[i]["d"]; parts = []; Ats[i] = {}
        for (h, n, kap, w) in rows[i]:
            keep = {c for c in S.comps[i]["ins"] if c[1] <= h[1] - d}
            own_before = [Z.bandf(n2, k2, w2) for (h2, n2, k2, w2) in rows[i] if h2[1] < h[1]]
            elim = [Z.z[c] for c in S.cols if c not in keep]
            Ah = qe_exists(elim, z3.And(base, *[G[j] for j in S.comps if j != i], *own_before))
            Ats[i][h] = Ah
            parts.append(z3.Implies(Ah, Z.bandf(n, kap, w)))
        Sts[i] = z3.And(parts)
    allT = z3.And(base, *Sts.values())
    verdict["(C1) time-sliced contracts -> G_P"] = both_valid(z3.Implies(allT, Z.GP))
    verdict["(C2) time-sliced: -> every A_i^h"] = all(both_valid(z3.Implies(allT, Ah)) for i in Ats for Ah in Ats[i].values())
    # ---------- receptiveness + causality: forall in(0) exists out(d) forall in(1) ... S_i
    def rc(i, Si):
        C = S.comps[i]
        ins = sorted(c for c in C["ins"] if c not in C["outs"])
        outs = sorted(C["outs"])
        slots = [((c[1], 0), "A", c) for c in ins] + [((c[1] - C["d"], 1), "E", c) for c in outs]
        slots.sort()
        blocks = []
        for _, q, c in slots:
            if blocks and blocks[-1][0] == q:
                blocks[-1][1].append(c)
            else:
                blocks.append([q, [c]])
        body = Si
        for q, cs in reversed(blocks):
            vs = [Z.z[c] for c in cs]
            body = z3.Exists(vs, z3.And(Z.typed(cs), body)) if q == "E" else z3.ForAll(vs, z3.Implies(Z.typed(cs), body))
        return both_valid(body)
    verdict["receptive+causal (full-horizon S_i), involved comps"] = {i: rc(i, Sfull[i]) for i in involved}
    verdict["receptive+causal (time-sliced S_i), involved comps"] = {i: rc(i, Sts[i]) for i in involved}
    verdict["receptive+causal (bare G_i over typed inputs), involved comps"] = {i: rc(i, G[i]) for i in involved}
    return dict(rows=rows, G=G, A=A, Ats=Ats, verdict=verdict, involved=involved)


# =============================================================================== reporting
def fmt(v):
    f = rat(v, 1000)
    if abs(float(f) - v) < 1e-9:
        return str(f) if f.denominator != 1 else str(f.numerator)
    return f"{v:.6g}"


def show_band_row(n, kap, w, head):
    c = n[head]
    terms = []
    for col, a in sorted(n.items(), key=lambda kv: (kv[0] != head, kv[0])):
        if col == head:
            continue
        g = -a / c
        terms.append(f"{fmt(abs(g))}*{col[0]}({col[1]})" if abs(abs(g) - 1) > 1e-12 else f"{col[0]}({col[1]})")
        terms[-1] = ("+ " if g > 0 else "- ") + terms[-1]
    centre = kap / c
    rhs = " ".join(terms).lstrip("+ ").strip() if terms else "0"
    if terms and terms[0].startswith("- "):
        rhs = "-" + rhs[2:] if rhs.startswith("- ") else rhs
    cen = f" {'+' if centre >= 0 else '-'} {fmt(abs(centre))}" if abs(centre) > 1e-12 else ""
    return f"|{head[0]}({head[1]}) - ({rhs}{cen})| <= {fmt(w / abs(c))}    [budget units: c={fmt(c)}, share w={fmt(w)}]"


def report(S, results, ver, log=print):
    log(f"\n=== {S.name}")
    for res in results:
        b = res["band"]
        log(f"  band {b['name']}:  |N z - {fmt(b['kappa'])}| <= {fmt(b['g'])}")
        if res.get("infeasible"):
            log("    INFEASIBLE"); continue
        log(f"    COI_k = {res['coi']};  heads = { {i: res['heads'][i] for i in res['coi']} }")
        log(f"    claims (max single share) = { {i: fmt(v) for i, v in res['claims'].items()} }")
        log(f"    necessary: by LP {res['nec_lp']}, by domination (Thm 2) {res['nec_dom']}")
        log(f"    candidate supports and their water-filling shares: {res['candidates']}")
        log(f"    chosen support {res['support']}  shares { {i: fmt(v) for i, v in res['shares'].items()} }"
            f"  support ties: {res['support_ties'] or 'none'}")
        log(f"    margins (leximin) { {k: fmt(v) for k, v in res['margins'].items()} }")
        log(f"    uniqueness certificate: max spread of any decision variable on the optimal face = {res['spread']:.2e}")
    if ver is None:
        return
    log("  delegated contracts (G_i rows normalised by the head coefficient):")
    for i in S.comps:
        if i not in ver["involved"]:
            log(f"    {i:11s}: (true, true)")
            continue
        for (h, n, kap, w) in ver["rows"][i]:
            log(f"    {i:11s}: G row  {show_band_row({c: float(a) for c, a in n.items()}, float(kap), float(w), h)}")
        log(f"    {'':11s}  A (full horizon) = {z3.simplify(ver['A'][i])}")
    log("  Z3 verdicts:")
    for k, v in ver["verdict"].items():
        log(f"    {k}: {v}")


# =============================================================================== examples
def relay():
    S = System("(a) relay  r -> Radio -> m -> Display -> d,  H=0")
    S.var("r", 1, [0], ap=1); S.var("m", 2, [0]); S.var("d", 3, [0])
    S.comp("Radio", [("r", 0)], [("m", 0)]); S.comp("Display", [("m", 0)], [("d", 0)])
    S.band({("d", 0): 1, ("r", 0): -1}, 0.5, name="d-r")
    return S


def chain():
    S = System("(b) 3-stage chain  r -> Radio -> m1 -> Relay -> m2 -> Display -> d,  H=0")
    S.var("r", 1, [0], ap=1); S.var("m1", 2, [0]); S.var("m2", 2, [0]); S.var("d", 3, [0])
    S.comp("Radio", [("r", 0)], [("m1", 0)]); S.comp("Relay", [("m1", 0)], [("m2", 0)])
    S.comp("Display", [("m2", 0)], [("d", 0)])
    S.band({("d", 0): 1, ("r", 0): -1}, 0.5, name="d-r")
    return S


def fanin():
    S = System("(c) fan-in  s1 -> A -> a, s2 -> B -> b, (a,b) -> Fuser -> f, f -> Logger -> log,  H=0")
    S.var("s1", 1, [0], ap=1); S.var("s2", 1, [0], ap=1)
    S.var("a", 2, [0]); S.var("b", 2, [0]); S.var("f", 3, [0]); S.var("log", 3, [0])
    S.comp("A", [("s1", 0)], [("a", 0)]); S.comp("B", [("s2", 0)], [("b", 0)])
    S.comp("Fuser", [("a", 0), ("b", 0)], [("f", 0)]); S.comp("Logger", [("f", 0)], [("log", 0)])
    S.band({("f", 0): 1, ("s1", 0): -1, ("s2", 0): -1}, 1.0, name="f-s1-s2")
    return S


def loop(H=2, physics=False):
    S = System(f"(d) tracking loop, H={H}, Plant delay 1" + (", Plant normal fixed to x(t+1)-x(t)-u(t)-w(t)" if physics else ""))
    S.var("x", 5, range(H + 1))
    S.cols[("x", 0)]["lo"], S.cols[("x", 0)]["hi"] = -1, 1          # A_P: |x(0)| <= 1 (x(0) is the env initial state)
    S.var("u", 5, range(H)); S.var("xh", 5, range(H))
    S.var("w", 0.2, range(H), ap=0.2); S.var("r", 1, range(H), ap=1)
    S.comp("Plant", [("x", t) for t in range(H)] + [("u", t) for t in range(H)] + [("w", t) for t in range(H)],
           [("x", t) for t in range(1, H + 1)], d=1)
    S.comp("Perception", [("x", t) for t in range(H)], [("xh", t) for t in range(H)], d=0)
    S.comp("Controller", [("xh", t) for t in range(H)] + [("r", t) for t in range(H)], [("u", t) for t in range(H)], d=0)
    for t in range(H):
        S.band({("x", t + 1): 1, ("r", t): -1}, 0.5, name=f"x({t+1})-r({t})")
    if physics:
        S.fixed["Plant"] = lambda band, h: {h: 1.0, ("x", h[1] - 1): -1.0, ("u", h[1] - 1): -1.0, ("w", h[1] - 1): -1.0}
    return S


def fanout(flip=False, Yd2=3, tie=None):
    S = System(f"(e) fan-out  r -> Radio -> m -> {{D1 -> d1, D2 -> d2}};  |d2|<={Yd2};  bands |d1 - r|, |d2 + r| <= 1/2" +
               ("  [band-2 gauge sign of Radio's head flipped]" if flip else "") +
               (f"  [Radio's head coefficient tied to c={tie} in both bands]" if tie is not None else ""))
    S.var("r", 1, [0], ap=1); S.var("m", 2, [0]); S.var("d1", 3, [0]); S.var("d2", Yd2, [0])
    if tie is not None:
        S.fix_head[("Radio", "d1-r")] = tie; S.fix_head[("Radio", "d2+r")] = tie
    S.comp("Radio", [("r", 0)], [("m", 0)]); S.comp("D1", [("m", 0)], [("d1", 0)]); S.comp("D2", [("m", 0)], [("d2", 0)])
    S.band({("d1", 0): 1, ("r", 0): -1}, 0.5, name="d1-r")
    S.band({("d2", 0): 1, ("r", 0): 1}, 0.5, name="d2+r")
    if flip:
        S.sign_override[("Radio", "d2+r")] = -1
    return S


def induced_boxes(S):
    """Receptiveness boxes shrunk to what A_P, the types and the query bands that are settled before the head imply
    (section 4, Remark 4.4).  Returns {(comp, col): (lo, hi)}."""
    boxes = {}
    P = S.preds()
    for band in S.bands:
        Ck, coi, heads, allowed = S.band_structure(band)
        for i in coi:
            h = heads[i]
            anc = S.back_closure({h}) - {h}
            settled = []
            for b2 in S.bands:
                C2 = S.back_closure(set(b2["N"]))
                if all(S.env(c) or c in anc or c[1] < h[1] for c in C2) and all(c in anc or c[1] < h[1] or S.env(c) for c in b2["N"]):
                    settled.append(b2)
            for col in allowed[i]:
                if S.env(col) or not settled:
                    continue
                lp = LP(); idx = {c: lp.var(str(c), S.box(c)[0], S.box(c)[1]) for c in S.cols}
                for b2 in settled:
                    e = {idx[c]: a for c, a in b2["N"].items()}
                    lp.add(e, lo=b2["kappa"] - b2["g"], hi=b2["kappa"] + b2["g"])
                _, lo = lp.solve({idx[col]: 1.0}); _, hi = lp.solve({idx[col]: 1.0}, maximize=True)
                boxes[(i, col)] = (lo, hi)
    return boxes


# =============================================================================== relay: rule comparison
def relay_rules(log=print):
    S = relay(); band = S.bands[0]
    log("\n=== rule comparison on the relay (shares w in budget units; Radio width = w_R/c, gain = 1/c)")
    rows = []
    # R*: lean (= egalitarian here, both necessary)
    res = choose(S, band, "lean")
    blp, x = res["blp"], res["x"]
    c = x[list(blp.coef[("Radio", ("m", 0))])[0]]
    rows.append(("R* lean-egalitarian + margin-centred gains", res["shares"]["Radio"], res["shares"]["Display"], c))
    # proportional to type, gains fixed at the R* gains: w_i = theta * c_i * Y_head
    for name, fixc in (("proportional-to-type, gains of R*", c), ("proportional-to-type, free gains", None)):
        def feas(theta):
            b = BandLP(S, band, ["Radio", "Display"])
            cR = list(b.coef[("Radio", ("m", 0))])[0]; cD = list(b.coef[("Display", ("d", 0))])[0]
            if fixc is not None:
                b.lp.add({cR: 1.0}, lo=fixc, hi=fixc)
            b.lp.add({b.w["Radio"]: 1.0, cR: -theta * 2}, lo=0)
            b.lp.add({b.w["Display"]: 1.0, cD: -theta * 3}, lo=0)
            x, _ = b.lp.solve({})
            return (x, b, cR) if x is not None else None
        lo, hi = 0.0, 1.0
        for _ in range(60):
            mid = (lo + hi) / 2
            (lo, hi) = (mid, hi) if feas(mid) else (lo, mid)
        lo = lo * (1 - 1e-7)
        x2, b2, cR = feas(lo)
        # among the theta-optimal points maximise the minimum margin (same tie-break as R*)
        lp = b2.lp.copy()
        lev, lp = leximax(lp, {"R+": b2.mplus["Radio"], "R-": b2.mminus["Radio"], "D+": b2.mplus["Display"], "D-": b2.mminus["Display"]})
        x3, _ = lp.solve({})
        rows.append((name + f" (theta={lo:.4f})", x3[b2.w["Radio"]], x3[b2.w["Display"]], x3[cR]))
    # sweep-style: slack to the first component (fixed-point sweep, theory/foundations.md section 9)
    for first, second in (("Radio", "Display"), ("Display", "Radio")):
        b = BandLP(S, band, ["Radio", "Display"])
        lev1 = b.lp.solve({b.w[first]: 1.0}, maximize=True)[1]
        b.lp.add({b.w[first]: 1.0}, lo=lev1 - FTOL)
        lev, lp = leximax(b.lp, {"R+": b.mplus["Radio"], "R-": b.mminus["Radio"], "D+": b.mplus["Display"], "D-": b.mminus["Display"]})
        x4, _ = lp.solve({})
        cR = list(b.coef[("Radio", ("m", 0))])[0]
        rows.append((f"slack-to-first ({first} first; = sweep from the copy seed)", x4[b.w["Radio"]], x4[b.w["Display"]], x4[cR]))
    log(f"    {'rule':62s} {'w_Radio':>8s} {'w_Disp':>8s} {'c':>7s}  Radio obligation        Display obligation")
    for name, wR, wD, c in rows:
        log(f"    {name:62s} {wR:8.4f} {wD:8.4f} {c:7.4f}  |m - {1/c:.4f} r| <= {wR/c:.4f}   |d - {c:.4f} m| <= {wD:.4f}")
    return rows


# =============================================================================== Theorem 1(c): non-convexity witness
def nonconvexity_check(log=print):
    """Two rows of one component on the same head y with a free head coefficient on the second row:
         y <= b1,   -c*y <= b2,  |y| <= 10.   Receptive (exists y) at (c,b1,b2) = (1,-1,1) and (3,1,-3), not at the midpoint."""
    y = z3.Real("y")
    def rec(c, b1, b2):
        return both_valid(z3.Exists([y], z3.And(y >= -10, y <= 10, y <= b1, -c * y <= b2)))
    p, q = (1, -1, 1), (3, 1, -3)
    mid = tuple(Fraction(a + b, 2) for a, b in zip(p, q))
    log("\n=== Theorem 1(c) witness: receptive set of a shared head with free coefficient ratio is not convex")
    log(f"    receptive at {p}: {rec(*p)};  at {q}: {rec(*q)};  at midpoint {tuple(map(str, mid))}: {rec(*mid)}")


# =============================================================================== main
def shared_heads(S):
    seen, shared = {}, []
    for b in S.bands:
        Ck, coi, heads, allowed = S.band_structure(b)
        for i in coi:
            key = (i, heads[i])
            if key in seen:
                shared.append((i, heads[i], seen[key], b["name"]))
            seen[key] = b["name"]
    return shared


def run(S, rule="lean", recept=True, boxes=None, no_recept=(), log=print, verify=True):
    t0 = time.time()
    for (i, h, b1, b2) in shared_heads(S):
        log(f"  WARNING {S.name}: {i} has head {h} in bands {b1} and {b2}: joint receptiveness across bands is "
            f"bilinear (Thm 1(c)) and is NOT enforced by the per-band LP; Z3 decides afterwards")
    results = [choose(S, b, rule, recept, boxes, no_recept) for b in S.bands]
    t1 = time.time()
    ver = None
    if verify and all(not r.get("infeasible") for r in results):
        ver = handout_and_verify(S, results)
    t2 = time.time()
    report(S, results, ver, log)
    log(f"  time: LP stage {t1-t0:.2f}s, projection+Z3 stage {t2-t1:.2f}s")
    return results, ver


if __name__ == "__main__":
    which = sys.argv[1:] or ["a", "rules", "b", "c", "d", "e"]
    if "a" in which:
        run(relay())
    if "rules" in which:
        relay_rules()
    if "b" in which:
        run(chain())
    if "c" in which:
        run(fanin())
        print("\n  (c') same fan-in under the egalitarian-over-COI rule:")
        run(fanin(), rule="egal", verify=False)
    if "e" in which:
        nonconvexity_check()
        run(fanout(False))
        run(fanout(False, Yd2=1.2))
        run(fanout(False, Yd2=1.2, tie=1.0))
        run(fanout(False, Yd2=1.2, tie=0.55))
    if "d" in which:
        run(loop(2))
        print("\n  (d') same loop, egalitarian-over-COI rule (forces Perception in):")
        run(loop(2), rule="egal")
        Sp = loop(2, physics=True)
        print("\n  (d'') Plant normal fixed to the physics; receptiveness boxes induced by settled query bands;"
              " the fixed Plant row is not required to be box-receptive (checked by Z3 afterwards):")
        run(Sp, boxes=induced_boxes(Sp), no_recept=("Plant",))
