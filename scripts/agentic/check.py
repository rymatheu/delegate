#!/usr/bin/env python
"""Mechanical checker for delegate proposals of the two-component stack (planner M1, controller M2).

    .venv/bin/python scripts/agentic/check.py <proposal.py> [--phase2] [--timeout S] [--only D1,D3,...]

Phase 1 (always): D1 A <= A1, D2 G1 <= A2, D3 A & G1 & A2 & G2 <= G, R (for all u in A1 some w with G1(u, w)),
each by Z3; R in two ways (quantified query, and the proposal's witness(u)), plus a sampled non-vacuity rate.
Phase 2 (--phase2): C1 planner revisions R1..R4 of scripts/vcore.py against (A1, G1), u symbolic, by path
enumeration of the planner code; C2 controller M2 of scripts/vcore.py against (A2, G2) over H = 8 ticks, w, p0 and
dt free, by exhaustive path enumeration of the controller code. Every verdict is PASS, FAIL (with a counterexample
replayed exactly on the proposal's functions), UNKNOWN or TIMEOUT. Exit status 0 iff every check that ran passed.
See scripts/agentic/README.md.
"""
import argparse, importlib.util, os, random, sys, time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))
import z3
import proposal as PR
from proposal import U, W, E, Ticks, Recorder, recording, flat_u, flat_w, mk_u, mk_w, H
import contract
import vcore
from vcore import explore, controller, planner
import validate                                    # reused: simp, tcheck (step-2 / planner-check machinery)

SPLIT_BUDGET = 512          # max number of parts a query is split into (top-level disjunctions)


# ------------------------------------------------------------------ loading and symbols
def load(path):
    spec = importlib.util.spec_from_file_location('proposal_under_check', path)
    mod = importlib.util.module_from_spec(spec)
    sys.path.insert(0, os.path.dirname(os.path.abspath(path)))
    spec.loader.exec_module(mod)
    for f in ('A1', 'G1', 'A2', 'G2'):
        if not callable(getattr(mod, f, None)):
            raise SystemExit('proposal %s does not define %s' % (path, f))
    return mod


def R_(n): return z3.Real(n)
def sym_u(p=''): return U(R_(p + 's'), (R_(p + 'hx'), R_(p + 'hy')), (R_(p + 'gx'), R_(p + 'gy')))
def sym_w(p=''): return W((R_(p + 'w1x'), R_(p + 'w1y')), (R_(p + 'w2x'), R_(p + 'w2y')))
def sym_p0(p=''): return (R_(p + 'px'), R_(p + 'py'))
def sym_dts(n, p=''): return Ticks([R_(p + 'dt%d' % t) for t in range(n)], 'dts')
def sym_y(n, p=''): return Ticks([(R_(p + 'y%dx' % t), R_(p + 'y%dy' % t)) for t in range(n)], 'y')


def as_w(x):
    if isinstance(x, W): return x
    if len(x) == 2: return W(tuple(x[0]), tuple(x[1]))
    return mk_w(tuple(x))


# ------------------------------------------------------------------ formula analysis
def nonlinear_atoms(f, limit=3):
    """Return up to `limit` atoms of f that contain a product of two non-constant terms (or a division by one)."""
    out, seen = [], set()
    def nl(t):
        if z3.is_mul(t) and sum(1 for c in t.children() if not z3.is_rational_value(c) and not z3.is_algebraic_value(c)) >= 2:
            return True
        if (z3.is_div(t) or z3.is_idiv(t)) and not z3.is_rational_value(t.children()[1]): return True
        if z3.is_app_of(t, z3.Z3_OP_POWER): return True
        return any(nl(c) for c in t.children())
    def walk(t):
        if t.get_id() in seen or len(out) >= limit: return
        seen.add(t.get_id())
        if z3.is_bool(t) and t.num_args() and not z3.is_bool(t.children()[0]) and not z3.is_app_of(t, z3.Z3_OP_ITE):
            if nl(t): out.append(t)
            return
        for c in t.children(): walk(c)
    if isinstance(f, z3.ExprRef): walk(f)
    return out


def existential_count(f, ops):
    """Number of distinct temporal operators per sequence that are existential after negation normal form
    (Diamond in positive, Box in negative position). By the pointwise lemma this many ticks suffice."""
    seen, cnt = set(), {}
    def walk(t, pol):
        key = (t.get_id(), pol)
        if key in seen: return
        seen.add(key)
        if t.get_id() in ops:
            kind, name, _ = ops[t.get_id()]
            if (kind == 'Diamond') == (pol > 0): cnt[name] = cnt.get(name, 0) + 1
            return
        if z3.is_and(t) or z3.is_or(t):
            for c in t.children(): walk(c, pol)
        elif z3.is_not(t): walk(t.children()[0], -pol)
        elif z3.is_implies(t): walk(t.children()[0], -pol); walk(t.children()[1], pol)
        elif z3.is_app_of(t, z3.Z3_OP_ITE) and z3.is_bool(t):
            c, a, b = t.children(); walk(c, 1); walk(c, -1); walk(a, pol); walk(b, pol)
        else:
            for c in t.children():
                if isinstance(c, z3.ExprRef): walk(c, 1); walk(c, -1)
    walk(f, 1)
    return cnt


def _disj(f):
    """Disjuncts of f if f is a top-level disjunction, else None."""
    if z3.is_or(f): return list(f.children())
    if z3.is_implies(f): return [z3.Not(f.children()[0]), f.children()[1]]
    if z3.is_not(f):
        a = f.children()[0]
        if z3.is_and(a): return [z3.Not(c) for c in a.children()]
        if z3.is_not(a): return _disj(a.children()[0])
    return None


def _flat(fs):
    out = []
    for f in fs:
        if isinstance(f, bool): f = z3.BoolVal(f)
        if z3.is_and(f): out.extend(_flat(f.children()))
        elif z3.is_not(f) and z3.is_or(f.children()[0]): out.extend(_flat([z3.Not(c) for c in f.children()[0].children()]))
        elif z3.is_not(f) and z3.is_not(f.children()[0]): out.extend(_flat([f.children()[0].children()[0]]))
        elif z3.is_not(f) and z3.is_implies(f.children()[0]):
            a, b = f.children()[0].children(); out.extend(_flat([a, z3.Not(b)]))
        else: out.append(f)
    return out


def split_parts(conj, budget=SPLIT_BUDGET):
    """Yield conjunction lists whose disjunction is equivalent to And(conj): top-level disjunctions are split, the
    first one found first (put the negated property first), while the product of the splits stays within budget."""
    flat = _flat(conj)
    if budget >= 2:
        for i, f in enumerate(flat):
            ds = _disj(f)
            if ds is not None and 2 <= len(ds) <= budget:
                rest = flat[:i] + flat[i + 1:]
                for d in ds: yield from split_parts(rest + [d], max(1, budget // len(ds)))
                return
    yield flat


def lift_ite(f):
    """Equivalent formula without arithmetic if-then-else (cofactoring each atom), for the quantified route."""
    memo = {}
    def find_ite(t):
        if z3.is_app_of(t, z3.Z3_OP_ITE) and not z3.is_bool(t): return t
        for c in t.children():
            r = find_ite(c)
            if r is not None: return r
        return None
    def go(t):
        k = t.get_id()
        if k in memo: return memo[k]
        if z3.is_and(t): r = z3.And(*[go(c) for c in t.children()])
        elif z3.is_or(t): r = z3.Or(*[go(c) for c in t.children()])
        elif z3.is_not(t): r = z3.Not(go(t.children()[0]))
        elif z3.is_implies(t): r = z3.Implies(go(t.children()[0]), go(t.children()[1]))
        elif z3.is_app_of(t, z3.Z3_OP_ITE) and z3.is_bool(t):
            c, a, b = [go(x) for x in t.children()]; r = z3.Or(z3.And(c, a), z3.And(z3.Not(c), b))
        else:
            it = find_ite(t)
            if it is None: r = t
            else:
                c, a, b = it.children()
                r = z3.Or(z3.And(go(c), go(z3.substitute(t, (it, a)))), z3.And(z3.Not(go(c)), go(z3.substitute(t, (it, b)))))
        memo[k] = r
        return r
    return go(f)


# ------------------------------------------------------------------ solving
def mode_of(fs):
    nl = any(nonlinear_atoms(f, 1) for f in fs)
    return ('nonlinear', 'QF_NRA (nlsat)') if nl else ('linear', 'QF_LRA')


def mk_solver(fs, deadline):
    kind, _ = mode_of(fs)
    s = z3.SolverFor('QF_NRA') if kind == 'nonlinear' else z3.SolverFor('QF_LRA')
    rem = deadline - time.time()
    s.set('timeout', max(1, int(rem * 1000)))
    return s


def _is_nl(t):
    if z3.is_mul(t) and sum(1 for c in t.children() if not z3.is_rational_value(c) and not z3.is_algebraic_value(c)) >= 2:
        return True
    if (z3.is_div(t) or z3.is_idiv(t)) and not z3.is_rational_value(t.children()[1]): return True
    if z3.is_app_of(t, z3.Z3_OP_POWER): return True
    return False


def abstract_products(fs):
    """Linear relaxation: every product of two non-constant terms becomes a fresh real (squares also get >= 0).
    Satisfiable whenever the original is, so 'unsat' of the relaxation proves 'unsat' of the original."""
    found, seen = {}, set()
    def walk(t):
        if t.get_id() in seen: return
        seen.add(t.get_id())
        if not z3.is_bool(t) and _is_nl(t):
            found[t.get_id()] = t; return
        for c in t.children(): walk(c)
    for f in fs: walk(f)
    pairs, lem = [], []
    for k, t in found.items():
        v = z3.FreshReal('nl'); pairs.append((t, v))
        ch = t.children()
        if z3.is_mul(t) and len(ch) == 2 and ch[0].eq(ch[1]): lem.append(v >= 0)
    if not pairs: return list(fs)
    return [z3.substitute(f, *pairs) for f in fs] + lem


def _exact_sqrt(k):
    import math
    if not z3.is_rational_value(k): return None
    n, d = k.numerator_as_long(), k.denominator_as_long()
    if n < 0: return None
    a, b = math.isqrt(n), math.isqrt(d)
    return Fraction(a, b) if a * a == n and b * b == d else None


OCT = Fraction(7071, 10000)        # < 1/sqrt(2): |v|_2 >= (|v_x| + |v_y|) / sqrt(2) >= OCT (|v_x| + |v_y|)


def metric_relax(fs, dist):
    """Sound linear handling of Euclidean distances built with dist_sq: each distance |a - b| gets a real d_ab >= 0;
    atoms dist_sq(a, b) ~ k with k a square of a rational become d_ab ~ sqrt(k) (equivalent); added valid lemmas:
    |a-b|_inf <= d_ab <= |a-b|_1, d_ab >= 0.7071 |a-b|_1, and the triangle inequality for every triple of points
    whose three distances occur. Returns (rewritten formulas, lemmas); every model of fs extends to one of both."""
    if not dist: return list(fs), []
    key = lambda p: tuple(x.get_id() if isinstance(x, z3.ExprRef) else ('c', str(x)) for x in p)
    pts, pair, tvar, lem = {}, {}, {}, []
    for tid, (a, b, t) in dist.items():
        ka, kb = key(a), key(b)
        if ka == kb: continue
        pts[ka], pts[kb] = a, b
        k = frozenset([ka, kb])
        if k not in pair:
            d = z3.FreshReal('dist'); pair[k] = d
            dx, dy = a[0] - b[0], a[1] - b[1]
            ab = lambda x: z3.If(x >= 0, x, -x)
            lem += [d >= 0, d >= dx, d >= -dx, d >= dy, d >= -dy, d <= ab(dx) + ab(dy),
                    d >= OCT * (dx + dy), d >= OCT * (dx - dy), d >= OCT * (-dx + dy), d >= OCT * (-dx - dy)]
        tvar[tid] = pair[k]
    ks = list(pts)
    for i in range(len(ks)):
        for j in range(len(ks)):
            for l in range(len(ks)):
                if len({i, j, l}) < 3 or i > l: continue
                a, b, c = ks[i], ks[j], ks[l]
                p1, p2, p3 = frozenset([a, b]), frozenset([b, c]), frozenset([a, c])
                if p1 in pair and p2 in pair and p3 in pair: lem.append(pair[p3] <= pair[p1] + pair[p2])
    ops = {z3.Z3_OP_LE: lambda x, y: x <= y, z3.Z3_OP_LT: lambda x, y: x < y,
           z3.Z3_OP_GE: lambda x, y: x >= y, z3.Z3_OP_GT: lambda x, y: x > y}
    memo = {}
    def go(t):
        if t.get_id() in memo: return memo[t.get_id()]
        r = t
        if z3.is_and(t) or z3.is_or(t) or z3.is_not(t) or z3.is_implies(t):
            ch = [go(c) for c in t.children()]
            r = z3.And(*ch) if z3.is_and(t) else z3.Or(*ch) if z3.is_or(t) else z3.Not(ch[0]) if z3.is_not(t) else z3.Implies(*ch)
        elif t.num_args() == 2 and t.decl().kind() in ops:
            x, y = t.children(); op = ops[t.decl().kind()]
            if x.get_id() in tvar and _exact_sqrt(y) is not None: r = op(tvar[x.get_id()], z3.RealVal(_exact_sqrt(y)))
            elif y.get_id() in tvar and _exact_sqrt(x) is not None: r = op(z3.RealVal(_exact_sqrt(x)), tvar[y.get_id()])
        memo[t.get_id()] = r
        return r
    return [go(f) for f in fs], lem


def _sqrt_bounds(k, strict_lo=False):
    """Rational lo <= sqrt(k) <= hi (equal when k is the square of a rational)."""
    import math
    r = _exact_sqrt(k)
    if r is not None: return r, r
    kf = Fraction(k.numerator_as_long(), k.denominator_as_long())
    x = math.sqrt(float(kf)); lo = Fraction(x * (1 - 1e-9)).limit_denominator(10 ** 9); hi = Fraction(x * (1 + 1e-9)).limit_denominator(10 ** 9)
    while lo * lo > kf: lo *= Fraction(999999, 1000000)
    while hi * hi < kf: hi *= Fraction(1000001, 1000000)
    return lo, hi


def polygon(n, k, inner, strict):
    """Half-planes (c, s, a), c vx + s vy <= a, of a regular n-gon with rational data: inner = inside the disc
    |v|^2 <= k (strictly inside when strict), outer = containing it. Checked exactly with Fractions."""
    import math
    lo, hi = _sqrt_bounds(k)
    q = 10 ** 6
    nrm = [(Fraction(round(math.cos(2 * math.pi * (j + .5) / n) * q), q), Fraction(round(math.sin(2 * math.pi * (j + .5) / n) * q), q))
           for j in range(n)]
    if not inner:
        out = []
        for c, s_ in nrm:
            a = Fraction(math.ceil(float(hi) * math.sqrt(float(c * c + s_ * s_)) * (1 + 1e-6) * q) + 1, q)
            assert a > 0 and a * a >= hi * hi * (c * c + s_ * s_)
            out.append((c, s_, a))
        return out
    a = Fraction(math.floor(float(lo) * math.cos(math.pi / n) * (1 - 1e-6) * q), q)
    for _ in range(60):
        ok = True
        for j in range(n):
            (c1, s1), (c2, s2) = nrm[j], nrm[(j + 1) % n]
            det = c1 * s2 - c2 * s1
            vx, vy = (a * s2 - s1 * a) / det, (c1 * a - c2 * a) / det
            v2 = vx * vx + vy * vy
            if v2 > lo * lo or (strict and v2 >= lo * lo): ok = False; break
        if ok: return [(c, s_, a) for c, s_ in nrm]
        a *= Fraction(999, 1000)
    raise RuntimeError('inner polygon construction failed')


def bracket(f, dist, inner, n):
    """Linear inner (inner=True, a subset of f) or outer (a superset) approximation of f: every atom
    dist_sq(a, b) <= k / < k / >= k / > k with k a nonnegative constant is replaced, according to its polarity, by
    a regular n-gon around b. Returns None if f has another nonlinear atom or such an atom in mixed polarity."""
    if dist is None: return None
    disc = {}
    for tid, (a, b, t) in dist.items(): disc[tid] = (a, b)
    memo = {}
    fail = [False]
    def poly(tid, k, strict, want_inner):
        a, b = disc[tid]; v = (a[0] - b[0], a[1] - b[1])
        return z3.And(*[z3.RealVal(c) * v[0] + z3.RealVal(s_) * v[1] <= z3.RealVal(aa) for c, s_, aa in polygon(n, k, want_inner, strict)])
    def go(t, pol):
        key = (t.get_id(), pol)
        if key in memo: return memo[key]
        if z3.is_and(t): r = z3.And(*[go(c, pol) for c in t.children()])
        elif z3.is_or(t): r = z3.Or(*[go(c, pol) for c in t.children()])
        elif z3.is_not(t): r = z3.Not(go(t.children()[0], -pol))
        elif z3.is_implies(t): r = z3.Implies(go(t.children()[0], -pol), go(t.children()[1], pol))
        elif not nonlinear_atoms(t, 1): r = t
        elif t.num_args() == 2 and t.decl().kind() in (z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_GE, z3.Z3_OP_GT):
            x, y = t.children(); kd = t.decl().kind()
            if y.get_id() in disc and z3.is_rational_value(x):       # k op t  ->  t op' k
                x, y = y, x; kd = {z3.Z3_OP_LE: z3.Z3_OP_GE, z3.Z3_OP_LT: z3.Z3_OP_GT, z3.Z3_OP_GE: z3.Z3_OP_LE, z3.Z3_OP_GT: z3.Z3_OP_LT}[kd]
            if x.get_id() not in disc or not z3.is_rational_value(y) or y.numerator_as_long() < 0:
                fail[0] = True; r = t
            else:
                # D = (t <= k) or (t < k); t >= k is not (t < k); t > k is not (t <= k)
                strict = kd in (z3.Z3_OP_LT, z3.Z3_OP_GE)
                pos = kd in (z3.Z3_OP_LE, z3.Z3_OP_LT)
                p = pol if pos else -pol
                want_inner = (p > 0) == inner
                D = poly(x.get_id(), y, strict, want_inner)
                r = D if pos else z3.Not(D)
        else:
            fail[0] = True; r = t
        memo[key] = r
        return r
    r = go(f, 1)
    return None if fail[0] else r


def _atoms_all_nl(f):
    """True iff f is a Boolean combination of atoms that all contain a nonlinear product."""
    if z3.is_and(f) or z3.is_or(f) or z3.is_not(f) or z3.is_implies(f):
        return all(_atoms_all_nl(c) for c in f.children())
    return bool(nonlinear_atoms(f, 1))


def _check(fs, deadline, cap=None, linear=False):
    s = z3.SolverFor('QF_LRA') if linear else z3.SolverFor('QF_NRA')
    rem = deadline - time.time()
    if cap is not None: rem = min(rem, cap)
    s.set('timeout', max(1, int(rem * 1000)))
    s.add(*fs)
    return s.check(), s


def solve_part(part, deadline, dist=None):
    """One conjunction. Linear: one QF_LRA call. Nonlinear: a ladder of relaxations, each a sound refutation
    (linear product abstraction; the purely nonlinear conjuncts; the conjuncts with a nonlinear atom), then the
    full part in QF_NRA (nlsat) with the remaining time, which is the only step that can report 'sat'."""
    if mode_of(part)[0] == 'linear':
        r, s = _check(part, deadline, linear=True)
        return r, s, 'linear'
    mf, lem = metric_relax(part, dist)
    r, s = _check(abstract_products(mf + lem), deadline, cap=5, linear=True)
    if r == z3.unsat: return r, s, 'linear relaxation' + (' with distance lemmas' if lem else '')
    pure = [f for f in part if _atoms_all_nl(f)]
    if pure and len(pure) < len(part):
        r, s = _check(pure, deadline, cap=5)
        if r == z3.unsat: return r, s, 'nonlinear conjuncts only'
    some = [f for f in part if nonlinear_atoms(f, 1)]
    if some and len(pure) < len(some) < len(part):
        r, s = _check(some, deadline, cap=5)
        if r == z3.unsat: return r, s, 'conjuncts with nonlinear atoms'
    r, s = _check(part, deadline)
    return r, s, 'full part'


def solve(conj, deadline, budget=SPLIT_BUDGET, dist=None):
    """Decide satisfiability of And(conj). Returns (status, model, info): status 'sat'|'unsat'|'unknown'|'timeout'."""
    nparts = nunk = 0; reasons = set(); how = {}
    for part in split_parts(conj, budget):
        if time.time() >= deadline: return 'timeout', None, dict(parts=nparts, unknown=nunk, how=how)
        nparts += 1
        r, s, h = solve_part(part, deadline, dist)
        how[h] = how.get(h, 0) + 1
        if r == z3.sat: return 'sat', s.model(), dict(parts=nparts, unknown=nunk, how=how)
        if r == z3.unknown:
            nunk += 1; reasons.add(s.reason_unknown())
            if time.time() >= deadline: return 'timeout', None, dict(parts=nparts, unknown=nunk, how=how)
    if nunk: return 'unknown', None, dict(parts=nparts, unknown=nunk, reasons=sorted(reasons), how=how)
    return 'unsat', None, dict(parts=nparts, unknown=0, how=how)


def mval(m, v):
    """Exact value of v in model m (Fraction); algebraic numbers are rounded to 30 digits (reported in the output)."""
    e = m.eval(v, model_completion=True)
    if z3.is_rational_value(e): return Fraction(e.numerator_as_long(), e.denominator_as_long()), True
    if z3.is_algebraic_value(e):
        a = e.approx(30); return Fraction(a.numerator_as_long(), a.denominator_as_long()), False
    return Fraction(str(e)), True


def zq(x): return z3.RealVal(x) if not isinstance(x, z3.ExprRef) else x


def truth(f):
    """Truth value of a variable-free formula (exact, by Z3 simplification)."""
    if isinstance(f, bool): return f
    r = z3.simplify(f)
    if z3.is_true(r): return True
    if z3.is_false(r): return False
    return None


def fnum(x):
    x = float(x)
    return ('%.4f' % x).rstrip('0').rstrip('.') if abs(x) < 1e6 else '%.4g' % x


def fpt(p): return '(%s, %s)' % (fnum(p[0]), fnum(p[1]))


def show_cex(c):
    out = []
    if 'u' in c: out.append('u: s=%s h=%s g=%s' % (fnum(c['u'][0]), fpt(c['u'][1:3]), fpt(c['u'][3:5])))
    if 'w' in c: out.append('w: w1=%s w2=%s' % (fpt(c['w'][0:2]), fpt(c['w'][2:4])))
    if 'p0' in c: out.append('e: p0=%s dts=[%s]' % (fpt(c['p0']), ', '.join(fnum(d) for d in c['dts'])))
    if 'y' in c: out.append('y: [%s]' % ', '.join(fpt(y) for y in c['y']))
    for k in ('note', 'replay'):
        if k in c: out.append('%s: %s' % (k, c[k]))
    return out


# ------------------------------------------------------------------ the checks
class Ctx:
    def __init__(self, prop, timeout, full=False):
        self.p, self.tmo, self.full = prop, timeout, full


def build(ctx, ny, ndt, parts):
    """Build the named formulas over fresh symbols with ny targets and ndt tick lengths, recording tick usage."""
    u, w, p0 = sym_u(), sym_w(), sym_p0()
    dts, y = sym_dts(ndt), sym_y(ny)
    e = E(p0, dts)
    rec = Recorder()
    f = {}
    with recording(rec):
        for name in parts:
            if name == 'A': f[name] = contract.A(u, e)
            elif name == 'G': f[name] = contract.G(u, e, y)
            elif name == 'A1': f[name] = ctx.p.A1(u)
            elif name == 'G1': f[name] = ctx.p.G1(u, w)
            elif name == 'A2': f[name] = ctx.p.A2(w)
            elif name == 'G2': f[name] = ctx.p.G2(w, e, y)
    for k in f:
        if isinstance(f[k], bool): f[k] = z3.BoolVal(f[k])
    return dict(u=u, w=w, p0=p0, dts=dts, y=y, e=e, f=f, rec=rec)


def horizon(ctx, parts, query_of):
    """Pick the horizon for a query over `parts`: reduced by the pointwise lemma when every formula is pointwise
    in a sequence, the full H otherwise. Returns (ny, ndt, explanation)."""
    if ctx.full:
        return H + 1, H, ['y: full %d ticks, dts: full %d ticks (forced by --full-horizon)' % (H + 1, H)]
    B = build(ctx, H + 1, H, parts)
    q = query_of(B['f'])
    cnt = existential_count(z3.And(*q), B['rec'].ops)
    why = []
    res = {}
    for name, full in (('y', H + 1), ('dts', H)):
        bad = B['rec'].reasons.get(name, []) + B['rec'].reasons.get('?', [])
        used = name in {n for (_, n, _) in B['rec'].ops.values()} or name in B['rec'].reasons
        if not used:
            res[name] = 1
            continue
        if bad:
            res[name] = full
            why.append('%s: full %d ticks (not pointwise: %s)' % (name, full, '; '.join(bad)))
        else:
            k = max(1, min(full, cnt.get(name, 0)))
            res[name] = k
            why.append('%s: %d of %d ticks (pointwise class, %d existential temporal operator(s) in the query)'
                       % (name, k, full, cnt.get(name, 0)))
    return res['y'], res['dts'], why


def extend(seq, n):
    seq = list(seq)
    return seq + [seq[-1]] * (n - len(seq))


def replay_D3(ctx, c):
    """Evaluate A, G1, A2, G2, G exactly on the counterexample extended to the full horizon H."""
    u = mk_u([z3.RealVal(x) for x in c['u']]); w = mk_w([z3.RealVal(x) for x in c['w']])
    p0 = tuple(z3.RealVal(x) for x in c['p0'])
    dts = Ticks([z3.RealVal(x) for x in extend(c['dts'], H)], 'dts')
    y = Ticks([tuple(z3.RealVal(x) for x in yt) for yt in extend(c['y'], H + 1)], 'y')
    e = E(p0, dts)
    v = dict(A=truth(contract.A(u, e)), G1=truth(ctx.p.G1(u, w)), A2=truth(ctx.p.A2(w)), G2=truth(ctx.p.G2(w, e, y)),
             G=truth(contract.G(u, e, y)))
    ok = v['A'] and v['G1'] and v['A2'] and v['G2'] and v['G'] is False
    return ok, v


def model_of(m, B, keys):
    c, exact = {}, True
    def get(v):
        nonlocal exact
        x, ex = mval(m, v); exact &= ex; return x
    if 'u' in keys: c['u'] = [get(v) for v in flat_u(B['u'])]
    if 'w' in keys: c['w'] = [get(v) for v in flat_w(B['w'])]
    if 'e' in keys:
        c['p0'] = [get(v) for v in B['p0']]; c['dts'] = [get(v) for v in B['dts']._items]
    if 'y' in keys: c['y'] = [[get(v) for v in yt] for yt in B['y']._items]
    if not exact: c['note'] = 'irrational model value(s) rounded to 30 digits'
    return c


def result(status, t0, **kw):
    d = dict(status=status, time=time.time() - t0); d.update(kw); return d


def run_static(ctx, name, parts, query_of, keys, replay):
    t0 = time.time(); deadline = t0 + ctx.tmo
    ny, ndt, why = horizon(ctx, parts, query_of)
    B = build(ctx, ny, ndt, parts)
    q = query_of(B['f'])
    kind, mode = mode_of(q)
    st, m, info = solve(q, deadline, dist=B['rec'].dist)
    extra = dict(horizon=why, mode='%s, %s' % (kind, mode), parts='%d, decided by %s' % (info['parts'], info['how']))
    if st == 'unsat': return result('PASS', t0, **extra)
    if st == 'sat':
        c = model_of(m, B, keys)
        ok, v = replay(c, B)
        c['replay'] = ('confirmed exactly' if ok else 'NOT confirmed') + ' on the full horizon: ' + \
            ', '.join('%s=%s' % kv for kv in v.items())
        if ny < H + 1 and 'y' in keys: c['note'] = (c.get('note', '') + ' y repeated from the last solved tick to %d ticks' % (H + 1)).strip()
        if ndt < H and 'e' in keys: c['dts'] = extend(c['dts'], H)
        if 'y' in keys: c['y'] = extend(c['y'], H + 1)
        return result('FAIL', t0, cex=c, **extra)
    return result('TIMEOUT' if st == 'timeout' else 'UNKNOWN', t0, info=info.get('reasons'), **extra)


def check_D1(ctx):
    def rp(c, B):
        u = mk_u([z3.RealVal(x) for x in c['u']])
        e = E(tuple(z3.RealVal(x) for x in c['p0']), Ticks([z3.RealVal(x) for x in extend(c['dts'], H)], 'dts'))
        v = dict(A=truth(contract.A(u, e)), A1=truth(ctx.p.A1(u))); return v['A'] and v['A1'] is False, v
    return run_static(ctx, 'D1', ['A', 'A1'], lambda f: [z3.Not(f['A1']), f['A']], ['u', 'e'], rp)


def check_D2(ctx):
    def rp(c, B):
        u = mk_u([z3.RealVal(x) for x in c['u']]); w = mk_w([z3.RealVal(x) for x in c['w']])
        v = dict(G1=truth(ctx.p.G1(u, w)), A2=truth(ctx.p.A2(w))); return v['G1'] and v['A2'] is False, v
    return run_static(ctx, 'D2', ['G1', 'A2'], lambda f: [z3.Not(f['A2']), f['G1']], ['u', 'w'], rp)


def check_D3(ctx):
    return run_static(ctx, 'D3', ['A', 'G1', 'A2', 'G2', 'G'],
                      lambda f: [z3.Not(f['G']), f['A'], f['G1'], f['A2'], f['G2']], ['u', 'w', 'e', 'y'],
                      lambda c, B: replay_D3(ctx, c))


def g1_exists_fixed_u(ctx, uval, deadline):
    """Is there a w with G1(u, w) for this fixed u (u rational)? Returns ('sat', w) / ('unsat', None) / ..."""
    u = mk_u([z3.RealVal(x) for x in uval]); w = sym_w('q_')
    g = ctx.p.G1(u, w)
    st, m, _ = solve([g if not isinstance(g, bool) else z3.BoolVal(g)], deadline)
    return st, ([mval(m, v)[0] for v in flat_w(w)] if st == 'sat' else None)


def check_R_quant(ctx):
    """Route (a): A1(u) and forall w. not G1(u, w), u free (existential); unsat iff R holds. Linear proposals: one
    LRA query (qsat). Nonlinear proposals whose nonlinear atoms are all Euclidean distance bounds: linear inner and
    outer polygon approximations of G1 (n = 8, 32, 128 sides; inner unsat proves R, outer sat refutes it), then the
    exact NRA query (nlqsat) with the remaining time."""
    t0 = time.time(); deadline = t0 + ctx.tmo
    u, w = sym_u(), sym_w()
    rec = Recorder()
    with recording(rec):
        a1, g1 = ctx.p.A1(u), ctx.p.G1(u, w)
    a1 = z3.BoolVal(a1) if isinstance(a1, bool) else a1
    g1 = z3.BoolVal(g1) if isinstance(g1, bool) else g1
    kind, _ = mode_of([a1, g1])
    W_ = list(flat_w(w))
    def qcheck(a1x, g1x, logic, cap=None):
        s = z3.SolverFor(logic)
        rem = deadline - time.time()
        if cap: rem = min(rem, cap)
        s.set('timeout', max(1, int(rem * 1000)))
        s.add(z3.And(lift_ite(a1x), z3.ForAll(W_, lift_ite(z3.Not(g1x)))))
        return s.check(), s
    def fail_with(m, how):
        uval = [mval(m, v)[0] for v in flat_u(u)]
        st, _ = g1_exists_fixed_u(ctx, uval, time.time() + 30)
        a1v = truth(ctx.p.A1(mk_u([z3.RealVal(x) for x in uval])))
        c = dict(u=uval, replay='fixed-u query "exists w. G1(u, w)": %s%s; A1(u)=%s' % (
            st, ' (confirmed: no mission)' if st == 'unsat' else '', a1v))
        return result('FAIL', t0, cex=c, mode=how)
    if kind == 'linear':
        how = 'linear, LRA (qsat) with a universal quantifier over w (if-then-else terms cofactored)'
        r, s = qcheck(a1, g1, 'LRA')
        if r == z3.unsat: return result('PASS', t0, mode=how)
        if r == z3.sat: return fail_with(s.model(), how)
        return result('TIMEOUT' if time.time() >= deadline - 0.05 else 'UNKNOWN', t0, mode=how, info=s.reason_unknown())
    tried = []
    for n in (8, 32, 128):
        gi, go_ = bracket(g1, rec.dist, True, n), bracket(g1, rec.dist, False, n)
        ai, ao = bracket(a1, rec.dist, True, n), bracket(a1, rec.dist, False, n)
        if None in (gi, go_, ai, ao): break
        r, s = qcheck(ao, gi, 'LRA', cap=max(1, (deadline - time.time()) / 4))
        tried.append('n=%d inner %s' % (n, r))
        if r == z3.unsat:
            return result('PASS', t0, mode='nonlinear G1/A1 bracketed by linear %d-gons: inner approximation of G1 realizable '
                          '(LRA, qsat): it is a subset of G1, so R holds' % n)
        r, s = qcheck(ai, go_, 'LRA', cap=max(1, (deadline - time.time()) / 4))
        tried.append('n=%d outer %s' % (n, r))
        if r == z3.sat:
            return fail_with(s.model(), 'nonlinear G1 bracketed by linear %d-gons: outer approximation of G1 (a superset) '
                             'has no mission at this u (LRA, qsat)' % n)
        if time.time() >= deadline: break
    how = 'nonlinear, NRA (nlqsat) with a universal quantifier over w (if-then-else terms cofactored)' + \
        ('; polygon brackets inconclusive: %s' % ', '.join(tried) if tried else '')
    if time.time() >= deadline: return result('TIMEOUT', t0, mode=how)
    r, s = qcheck(a1, g1, 'NRA')
    if r == z3.unsat: return result('PASS', t0, mode=how)
    if r == z3.sat: return fail_with(s.model(), how)
    why = s.reason_unknown()
    return result('TIMEOUT' if ('timeout' in why or 'cancel' in why) else 'UNKNOWN', t0, mode=how, info=why)


def check_R_witness(ctx):
    """Route (b): forall u. A1(u) -> G1(u, witness(u)), u symbolic, quantifier-free."""
    t0 = time.time(); deadline = t0 + ctx.tmo
    if not callable(getattr(ctx.p, 'witness', None)): return result('SKIPPED', t0, info='proposal has no witness(u)')
    u = sym_u()
    rec = Recorder()
    with recording(rec):
        wt = as_w(ctx.p.witness(u))
        a1, g1 = ctx.p.A1(u), ctx.p.G1(u, wt)
    q = [z3.Not(g1) if not isinstance(g1, bool) else z3.BoolVal(not g1), a1 if not isinstance(a1, bool) else z3.BoolVal(a1)]
    kind, mode = mode_of(q)
    st, m, info = solve(q, deadline, dist=rec.dist)
    extra = dict(mode='%s, %s' % (kind, mode), parts='%d, decided by %s' % (info['parts'], info['how']))
    if st == 'unsat': return result('PASS', t0, **extra)
    if st == 'sat':
        uval = [mval(m, v)[0] for v in flat_u(u)]
        uz = mk_u([z3.RealVal(x) for x in uval])
        wz = as_w(ctx.p.witness(uz))
        wval = [Fraction(str(z3.simplify(x).as_fraction())) for x in flat_w(wz)]
        v = dict(A1=truth(ctx.p.A1(uz)), G1=truth(ctx.p.G1(uz, mk_w([z3.RealVal(x) for x in wval]))))
        c = dict(u=uval, w=wval, replay='witness(u) evaluated exactly: ' + ', '.join('%s=%s' % kv for kv in v.items()))
        return result('FAIL', t0, cex=c, **extra)
    return result('TIMEOUT' if st == 'timeout' else 'UNKNOWN', t0, info=info.get('reasons'), **extra)


def sample_u(rng, wide):
    if wide:
        return (rng.uniform(0, 100), rng.uniform(-110, 110), rng.uniform(-110, 110), rng.uniform(-110, 110), rng.uniform(-110, 110))
    s = rng.uniform(25, 50); a, b = s - 3, s + 0.5
    return (s, rng.uniform(-a, a), rng.uniform(-a, a), rng.uniform(-b, b), rng.uniform(-b, b))


def check_sample(ctx, n=10000, seed=20261027):
    """Non-vacuity: fraction of random u in A1 with a witness, by concrete evaluation (floats)."""
    t0 = time.time(); rng = random.Random(seed)
    out = {}
    has_w = callable(getattr(ctx.p, 'witness', None))
    for label, wide in (('u drawn from the u-part of A', False), ('u drawn from a wide box, kept if in A1', True)):
        inA1 = good = 0; bad_ex = None
        draws = n if has_w else 300
        for _ in range(draws):
            uf = sample_u(rng, wide); u = mk_u(uf)
            if not ctx.p.A1(u): continue
            inA1 += 1
            if has_w:
                if ctx.p.G1(u, as_w(ctx.p.witness(u))): good += 1
                elif bad_ex is None: bad_ex = uf
            else:
                st, _ = g1_exists_fixed_u(ctx, [Fraction(x).limit_denominator(10 ** 6) for x in uf], time.time() + 10)
                if st == 'sat': good += 1
                elif bad_ex is None: bad_ex = uf
        out[label] = (draws, inA1, good, bad_ex)
    return result('INFO', t0, table=out, route='witness(u), concrete floats' if has_w else
                  'no witness(u): per-u Z3 query "exists w. G1(u, w)" on 300 draws')


# ------------------------------------------------------------------ phase 2
def check_C1(ctx, rev):
    """Planner revision rev against (A1, G1): explore the planner code with u symbolic under A1; on every feasible
    path ask whether not G1(u, M1(u)) is satisfiable. Generalises validate.planner_check to any G1."""
    t0 = time.time(); deadline = t0 + ctx.tmo
    m = getattr(ctx.p, 'PLANNER_MARGIN', 1)
    u = sym_u(); uu = list(flat_u(u))
    a1 = ctx.p.A1(u); a1 = z3.BoolVal(a1) if isinstance(a1, bool) else a1
    npaths = 0; mode = set()
    try:
        for pc, wv, s in explore([a1], lambda op: planner(rev, uu, op, m), deadline=deadline):
            npaths += 1
            w = mk_w([validate.simp(x) for x in wv])
            rec = Recorder()
            with recording(rec): g1 = ctx.p.G1(u, w)
            q = [z3.Not(g1) if not isinstance(g1, bool) else z3.BoolVal(not g1)]
            mode.add(mode_of(q)[0])
            for part in split_parts(q, 64):
                s.push(); s.add(*part); r = validate.tcheck(s, deadline)
                if r == z3.sat:
                    mm = s.model(); uval = [mval(mm, v)[0] for v in uu]
                    wval = planner(rev, uval, vcore.Num(), m)
                    wval = [Fraction(x) for x in wval]
                    v = truth(ctx.p.G1(mk_u([z3.RealVal(x) for x in uval]), mk_w([z3.RealVal(x) for x in wval])))
                    return result('FAIL', t0, paths=npaths, cex=dict(u=uval, w=wval, replay='G1(u, M1(u)) evaluated exactly: %s' % v),
                                  mode=', '.join(sorted(mode)))
                s.pop()
                if r == z3.unknown:          # second opinion: relaxation ladder on a fresh solver
                    r2, _, _ = solve_part([a1] + list(pc) + list(part), deadline, rec.dist)
                    if r2 != z3.unsat: return result('UNKNOWN', t0, paths=npaths, info='path query unknown')
    except TimeoutError:
        return result('TIMEOUT', t0, paths=npaths)
    if npaths == 0: return result('VACUOUS', t0, paths=0, info='A1 is empty')
    return result('PASS', t0, paths=npaths, margin=m, mode=', '.join(sorted(mode)) + ' atoms; default Z3 solver, incremental on each path condition')


def check_C2(ctx):
    """Controller M2 against (A2, G2) over H ticks: explore the controller code with w, p0, dt free under A2 (and
    under not-E, where E is the disjunction of the y-free disjuncts of G2, which make G2 true on their own); on
    every feasible path ask whether the remaining disjuncts of G2 can all be false. Generalises validate.certify_check."""
    t0 = time.time(); deadline = t0 + ctx.tmo
    w, p0 = sym_w(), sym_p0(); dts = sym_dts(H); ywit = sym_y(H + 1, 'free_')
    e = E(p0, dts)
    a2 = ctx.p.A2(w); a2 = z3.BoolVal(a2) if isinstance(a2, bool) else a2
    yv = set().union(*[PR._vars(yt) for yt in ywit._items])
    g2free = ctx.p.G2(w, e, ywit)
    ds = _disj(g2free) if isinstance(g2free, z3.ExprRef) else None
    env_idx = [i for i, d in enumerate(ds or []) if not (PR._vars(d) & yv)]
    env = [ds[i] for i in env_idx]
    base = [a2] + ([z3.Not(z3.Or(*env))] if env else [])
    note = ('runs restricted to not E, E = the %d disjunct(s) of G2 that do not mention y (G2 holds whenever E does)'
            % len(env)) if env else 'G2 has no y-free disjunct: every environment is explored'
    wl, dl = list(flat_w(w)), list(dts._items)
    npaths = nq = 0; cache = set(); mode = set()
    try:
        for pc, ys, s in explore(base, lambda op: controller(wl, p0, dl, op), deadline=deadline):
            npaths += 1
            Y = Ticks([(validate.simp(a), validate.simp(b)) for a, b in ys], 'y')
            rec = Recorder()
            with recording(rec): g2 = ctx.p.G2(w, e, Y)
            pd = _disj(g2) if env and isinstance(g2, z3.ExprRef) else None
            if pd is not None and len(pd) == len(ds):     # same Or structure: drop E (false under the base)
                rest = [d for i, d in enumerate(pd) if i not in env_idx]
                q = [z3.Not(z3.Or(*rest))] if rest else [z3.BoolVal(False)]
            else:
                q = [z3.Not(g2) if not isinstance(g2, bool) else z3.BoolVal(not g2)]
            mode.add(mode_of(q)[0])
            for part in split_parts(q, 32):
                key = z3.And(*part).sexpr() if len(part) > 1 else part[0].sexpr()
                key = (key, tuple(x.sexpr() for x in pc))
                if key in cache: continue
                cache.add(key)
                s.push(); s.add(*part); r = validate.tcheck(s, deadline); nq += 1
                if r == z3.sat:
                    mm = s.model()
                    wval = [mval(mm, v)[0] for v in wl]; pv = [mval(mm, v)[0] for v in p0]; dv = [mval(mm, v)[0] for v in dl]
                    yc = controller(wval, pv, dv, vcore.Num())
                    yc = [[Fraction(a), Fraction(b)] for a, b in yc]
                    ez = E(tuple(z3.RealVal(x) for x in pv), Ticks([z3.RealVal(x) for x in dv], 'dts'))
                    v = truth(ctx.p.G2(mk_w([z3.RealVal(x) for x in wval]), ez, Ticks([tuple(z3.RealVal(c) for c in yt) for yt in yc], 'y')))
                    return result('FAIL', t0, paths=npaths, queries=nq, note=note,
                                  cex=dict(w=wval, p0=pv, dts=dv, y=yc, replay='controller re-run on these values, G2 evaluated exactly: %s' % v))
                s.pop()
                if r == z3.unknown:          # second opinion: relaxation ladder on a fresh solver
                    r2, _, _ = solve_part(list(base) + list(pc) + list(part), deadline, rec.dist)
                    if r2 != z3.unsat: return result('UNKNOWN', t0, paths=npaths, queries=nq, info='path query unknown', note=note)
    except TimeoutError:
        return result('TIMEOUT', t0, paths=npaths, queries=nq, note=note)
    if npaths == 0: return result('VACUOUS', t0, paths=0, note=note)
    return result('PASS', t0, paths=npaths, queries=nq, note=note, mode=', '.join(sorted(mode)) + ' atoms; default Z3 solver, incremental on each path condition')


# ------------------------------------------------------------------ report
def atoms_report(ctx):
    B = build(ctx, 2, 1, ['A', 'G', 'A1', 'G1', 'A2', 'G2'])
    lines, nl_prop = [], []
    for k in ('A1', 'G1', 'A2', 'G2', 'A', 'G'):
        at = nonlinear_atoms(B['f'][k], 2)
        src = 'proposal' if k in ('A1', 'G1', 'A2', 'G2') else 'top-level contract'
        if at:
            ex = str(at[0]).replace('\n', ' ')
            lines.append('  %-3s NONLINEAR (%s), e.g. %s' % (k, src, ex[:110] + ('...' if len(ex) > 110 else '')))
            if src == 'proposal': nl_prop.append(k)
        else:
            lines.append('  %-3s linear' % k)
    return lines, nl_prop


def line(label, r):
    st = r['status']
    s = '%-40s %-8s %8.2f s' % (label, st, r['time'])
    out = [s]
    for k in ('mode', 'parts', 'paths', 'queries', 'margin', 'note', 'info'):
        if k in r and r[k] not in (None, [], ''):
            out.append('    %s: %s' % (k, r[k]))
    for h in r.get('horizon', []): out.append('    horizon: %s' % h)
    if 'cex' in r:
        out.append('    counterexample:')
        out += ['      ' + x for x in show_cex(r['cex'])]
    return out


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('proposal')
    ap.add_argument('--phase2', action='store_true', help='also run C1 (planner revisions R1..R4) and C2 (controller)')
    ap.add_argument('--timeout', type=float, default=120, help='seconds per check (default 120)')
    ap.add_argument('--full-horizon', action='store_true', help='unroll D1/D3 over all H ticks even in the pointwise class')
    ap.add_argument('--only', default='', help='comma list among D1,D2,D3,R,S,C1,C2 (default: all of the phase)')
    a = ap.parse_args(argv)
    T0 = time.time()
    ctx = Ctx(load(a.proposal), a.timeout, a.full_horizon)
    only = set(x.strip() for x in a.only.split(',') if x.strip())
    want = lambda k: (not only) or k in only
    print('proposal  %s  (%s)' % (a.proposal, getattr(ctx.p, 'NAME', '-')))
    print('instance  H = %d, (A, G) of scripts/validate.py, controller and planners of scripts/vcore.py, Z3 %s, %g s per check'
          % (H, z3.get_version_string(), a.timeout))
    al, nl = atoms_report(ctx)
    print('atoms')
    for l in al: print(l)
    if nl:
        print('  WARNING: the proposal has nonlinear atoms in %s; queries with them run in nonlinear real arithmetic'
              ' (QF_NRA, nlsat; NRA with nlqsat for the quantified R route), which is slower and may return UNKNOWN.'
              ' Infinity-norm atoms (inf_le, inf_ge, ...) keep a part linear.' % ', '.join(nl))
    verdicts = {}
    rows = []
    def show(key, label, r, counts=True):
        for l in line(label, r): print(l)
        sys.stdout.flush()
        if counts: verdicts[key] = r['status']
        rows.append((label, r['status'], r['time']))
    print('\nphase 1')
    if want('D1'): show('D1', 'D1  A <= A1', check_D1(ctx))
    if want('D2'): show('D2', 'D2  G1 <= A2', check_D2(ctx))
    if want('D3'): show('D3', 'D3  A & G1 & A2 & G2 <= G', check_D3(ctx))
    if want('R'):
        ra = check_R_quant(ctx); show('Ra', 'R   (a) quantified: A1 & forall w. ~G1', ra, counts=False)
        rb = check_R_witness(ctx); show('Rb', 'R   (b) witness: A1(u) -> G1(u, witness(u))', rb, counts=False)
        if 'PASS' in (ra['status'], rb['status']): rv = 'PASS'
        elif ra['status'] == 'FAIL': rv = 'FAIL'
        elif rb['status'] == 'FAIL' and ra['status'] != 'PASS': rv = 'UNKNOWN'
        else: rv = 'UNKNOWN'
        verdicts['R'] = rv
        print('%-40s %-8s (PASS if either route proves it; FAIL only on a quantified counterexample u;'
              ' a failing witness alone leaves R open)' % ('R   verdict', rv))
    if want('S'):
        r = check_sample(ctx)
        print('%-40s %-8s %8.2f s   (%s)' % ('S   non-vacuity sample', 'INFO', r['time'], r['route']))
        for lab, (n, ina, good, bad) in r['table'].items():
            fr_ = good / ina if ina else float('nan')
            print('    %s: %d draws, %d in A1, %d with a witness (%.4f)%s' % (lab, n, ina, good, fr_,
                  '' if bad is None else '; first without: s=%s h=%s g=%s' % (fnum(bad[0]), fpt(bad[1:3]), fpt(bad[3:5]))))
        rows.append(('S', 'INFO', r['time']))
    if a.phase2:
        print('\nphase 2')
        dep = getattr(ctx.p, 'PLANNER_REVISION', 4)
        if want('C1'):
            for rev in (1, 2, 3, 4):
                r = check_C1(ctx, rev)
                tag = 'deployed' if rev == dep else 'informational'
                show('C1-R%d' % rev, 'C1  planner R%d against (A1, G1) [%s]' % (rev, tag), r, counts=(rev == dep))
        if want('C2'): show('C2', 'C2  controller M2 against (A2, G2), H=%d' % H, check_C2(ctx))
    ok = all(v == 'PASS' for v in verdicts.values())
    print('\nsummary: %s   total %.1f s   (%s)' % ('ALL PASS' if ok else 'NOT ALL PASS', time.time() - T0,
          ', '.join('%s %s' % kv for kv in verdicts.items())))
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
