#!/usr/bin/env python
"""Experimental validation of the delegation algorithm of docs/delegation-algorithm.tex.

    .venv/bin/python scripts/validate.py            # same as --full
    .venv/bin/python scripts/validate.py --quick    # small subset (about 2 minutes)

Writes docs/figs/validation/*.pdf, notes/validation/results.json and results.md (the quick subset writes
docs/figs/validation/quick/*.pdf and results-quick.*); exits 0 iff every soundness check passes.
`--plot-only` (alias `--figures-only`) redraws every figure and results.md from an existing results.json. Models (controller M2, planner revisions M1, closed-form G1) live in scripts/vcore.py.
"""
import argparse, json, math, os, sys, time, random
import multiprocessing as mp
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import z3
from vcore import (CTRL, TOP, Num, Sym, Fork, Infeasible, explore, controller, planner, le_inf, lt_inf,
                   inorm, A1, Vw, G1, bad_closed, fr, fr_exact, Q)

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FIG = os.path.join(ROOT, 'docs', 'figs', 'validation')
OUT = os.path.join(ROOT, 'notes', 'validation')
SEED = 20261027
ETA = Fr(1, 2)
EPS, DELTA = TOP['eps'], TOP['delta']


def zv(x):
    """Z3 numeral for a Fraction/int, identity on Z3 terms."""
    if isinstance(x, Fr): return z3.Q(x.numerator, x.denominator)
    if isinstance(x, int): return z3.RealVal(x)
    return x


def tcheck(s, deadline):
    rem = deadline - time.time()
    if rem <= 0: raise TimeoutError()
    s.set('timeout', max(1, int(rem * 1000)))
    r = s.check()
    if r == z3.unknown and time.time() >= deadline: raise TimeoutError()
    return r


def simp(e):
    return z3.simplify(e, som=True) if isinstance(e, z3.ExprRef) else zv(Fr(e))


# ------------------------------------------------------------------ vocabulary read from the controller (step 1)
def V_f(w, op):
    d2 = (w[2] - w[0], w[3] - w[1])
    return op.And(op.Not(lt_inf(d2, CTRL['lmin'], op)), le_inf(d2, CTRL['lmax'], op), le_inf(w[:2], CTRL['B'], op),
                  le_inf(w[2:], CTRL['B'], op))


def P_f(w, p0, dts, op):
    d1 = (w[0] - p0[0], w[1] - p0[1])
    lo, hi = fr_exact(CTRL['dtmin']), fr_exact(CTRL['dtmax'])
    return op.And(op.Not(lt_inf(d1, CTRL['lmin'], op)), le_inf(d1, CTRL['lmax'], op), le_inf(p0, CTRL['B'], op),
                  *[op.And(zv(lo) <= d, d <= zv(hi)) for d in dts])


def tube_seg(y, a, b, r):
    """y within inf-distance r of segment [a,b]: bounding box grown by r, and |(y-a) x (b-a)| <= r(|dx|+|dy|)."""
    ab = lambda x: z3.If(x >= 0, x, -x)
    mn = lambda p, q: z3.If(p <= q, p, q); mx = lambda p, q: z3.If(p >= q, p, q)
    d = (b[0] - a[0], b[1] - a[1]); z = (y[0] - a[0], y[1] - a[1]); cr = z[0] * d[1] - z[1] * d[0]
    return z3.And(mn(a[0], b[0]) - r <= y[0], y[0] <= mx(a[0], b[0]) + r, mn(a[1], b[1]) - r <= y[1],
                  y[1] <= mx(a[1], b[1]) + r, ab(cr) <= r * (ab(d[0]) + ab(d[1])))


def tube(y, p0, w, r):
    return z3.Or(tube_seg(y, p0, (w[0], w[1]), r), tube_seg(y, (w[0], w[1]), (w[2], w[3]), r))


def d2(y, c):
    return (y[0] - c[0]) * (y[0] - c[0]) + (y[1] - c[1]) * (y[1] - c[1])


def inf_dist_seg(z, a, b):
    """Exact inf-norm distance from point z to segment [a,b] (numpy floats): convex piecewise-linear in lambda."""
    d = b - a; q = z - a
    cand = [0.0, 1.0]
    for sgn in (1, -1):
        den = d[0] - sgn * d[1]
        if abs(den) > 1e-15: cand.append((q[0] - sgn * q[1]) / den)
    for k in (0, 1):
        if abs(d[k]) > 1e-15: cand.append(q[k] / d[k])
    best = 1e18
    for lam in cand:
        lam = min(max(lam, 0.0), 1.0); e = q - lam * d; best = min(best, max(abs(e[0]), abs(e[1])))
    return best


def poly_dev(ys, p0, w):
    p0 = np.asarray(p0, float); w1 = np.asarray(w[:2], float); w2 = np.asarray(w[2:], float)
    return max(min(inf_dist_seg(np.asarray(y, float), p0, w1), inf_dist_seg(np.asarray(y, float), w1, w2)) for y in ys)


def symbols(H, pre=''):
    w = [z3.Real(pre + 'w%d' % i) for i in range(4)]
    p0 = [z3.Real(pre + 'px'), z3.Real(pre + 'py')]
    dts = [z3.Real(pre + 'dt%d' % t) for t in range(H)]
    return w, p0, dts


# ------------------------------------------------------------------ step 1: rho_1 from fixed legs, nominal inputs
TEST_LEGS = [((0, 0), (L1, 0), (L1 + L2 * math.cos(th), L2 * math.sin(th)))
             for L1 in (12, 15, 18, 19, 35, 60, 97) for L2 in (20, 50) for th in (math.pi / 4, math.pi / 2, 3 * math.pi / 4)]


def rho1_from_runs(H=30):
    best = 0.0
    for p0, w1, w2 in TEST_LEGS:
        w = (w1[0], w1[1], w2[0], w2[1])
        ys = controller(w, p0, [1.0] * H, Num())
        best = max(best, poly_dev(ys, p0, w))
    return best


# ------------------------------------------------------------------ step 2: certification by BMC (path enumeration)
def certify_check(H, rho, deadline, want_cex=False, reach=False):
    """Decide M2 cap V cap P subset T(rho) (tube part, or the reach part if reach=True) over ticks 0..H.
    Returns dict(status='unsat'|'sat'|'timeout', paths, queries, time, cex)."""
    t0 = time.time()
    w, p0, dts = symbols(H)
    S = Sym()
    base = [V_f(w, S), P_f(w, p0, dts, S)]
    npaths = nq = 0; cache = {}
    try:
        for pc, ys, s in explore(base, lambda op: controller(w, p0, dts, op), deadline=deadline):
            npaths += 1
            ys = [(simp(y[0]), simp(y[1])) for y in ys]
            if reach:
                s.push(); s.add(z3.And(*[d2(y, (w[2], w[3])) > zv(ETA * ETA) for y in ys])); r = tcheck(s, deadline); nq += 1
                if r != z3.unsat:
                    cex = model_traj(s, w, p0, dts, H, pc) if (want_cex and r == z3.sat) else None
                    return dict(status='sat' if r == z3.sat else 'unknown', paths=npaths, queries=nq, time=time.time() - t0, cex=cex)
                s.pop()
                continue
            seen = set()
            for t, y in enumerate(ys):
                key = (y[0].sexpr(), y[1].sexpr())
                if key in seen: continue          # same target term as an earlier tick on this path: same query
                seen.add(key)
                if time.time() > deadline: raise TimeoutError()
                viol = z3.Not(tube(y, p0, w, zv(rho)))
                s.push(); s.add(viol); r = tcheck(s, deadline); nq += 1
                if r != z3.unsat:
                    cex = model_traj(s, w, p0, dts, H, pc) if (want_cex and r == z3.sat) else None
                    s.pop()
                    return dict(status='sat' if r == z3.sat else 'unknown', paths=npaths, queries=nq, time=time.time() - t0,
                                tick=t, cex=cex)
                s.pop()
    except TimeoutError:
        return dict(status='timeout', paths=npaths, queries=nq, time=time.time() - t0)
    if npaths == 0: return dict(status='vacuous', paths=0, queries=nq, time=time.time() - t0)
    return dict(status='unsat', paths=npaths, queries=nq, time=time.time() - t0)


def model_traj(s, w, p0, dts, H, pc, extra=None):
    m = s.model()
    val = lambda v: float(Fr(str(m.eval(v, model_completion=True).as_fraction())))
    W = [val(x) for x in w]; P0 = [val(x) for x in p0]; DT = [val(x) for x in dts]
    ys = controller(W, P0, DT, Num())
    return dict(w=W, p0=P0, dts=DT, ys=[list(map(float, y)) for y in ys], dev=poly_dev(ys, P0, W))


def step2(H, chain, tmo):
    """Binary search for the least verified chain index (up-set); plus the reach part (independent of rho)."""
    deadline = time.time() + tmo
    rec = dict(H=H, checks=[], reach=None)
    rr = certify_check(H, chain[0], deadline, reach=True, want_cex=True)
    rec['reach'] = dict(status=rr['status'], time=rr['time'], paths=rr['paths'], cex=rr.get('cex'))
    k = len(chain)
    def check(j):
        r = certify_check(H, chain[j], time.time() + tmo, want_cex=True)
        rec['checks'].append(dict(j=j + 1, rho=float(chain[j]), status=r['status'], time=r['time'], paths=r['paths'],
                                  queries=r['queries'], tick=r.get('tick')))
        return r['status']
    st = check(k - 1)
    if st != 'unsat':
        rec['jstar'] = None
    else:
        lo, hi = 0, k - 1                         # chain[hi] verified; find least verified index
        while lo < hi:
            mid = (lo + hi) // 2
            if check(mid) == 'unsat': hi = mid
            else: lo = mid + 1
        rec['jstar'] = hi + 1
    rec['tube_time'] = sum(c['time'] for c in rec['checks'])
    rec['total_time'] = rec['tube_time'] + rec['reach']['time']
    rec['certified'] = rec['jstar'] is not None and rr['status'] == 'unsat'
    return rec


# ------------------------------------------------------------------ top-level contract (validation instance)
def A_f(u, p0, dts, op):
    s, hx, hy, gx, gy = u
    return op.And(A1(u, op), le_inf((p0[0] - hx, p0[1] - hy), DELTA, op),
                  *[op.And(zv(fr_exact(TOP['dtlo'])) <= d, d <= zv(fr_exact(TOP['dthi']))) for d in dts])


def fence_viol(y, s):
    return z3.Or(y[0] > s, -y[0] > s, y[1] > s, -y[1] > s)


def mono_check(u, rev, m, H, deadline, u_free=False, order='fair'):
    """Monolithic BMC of M1 (revision rev) composed with M2 over ticks 0..H: is A and not G unsatisfiable?
    u fixed (rationals) unless u_free. Same Fork path enumeration in both orders; they differ only in how the
    property atoms of a path are put to the solver:
      order='fair' (reported): the fence atoms of all ticks of a path as one disjunction; then the goal, first for
        single ticks from the last tick backwards (if 'path and |y_t-g|^2 > eps^2' is unsat for one t, the goal holds
        on that path, a sound shortcut), and only if no single tick settles it the conjunction over all ticks;
      order='orig' (first implementation, kept to document the effect): fence atom tick by tick from tick 0, then the
        goal as one conjunction over all ticks.
    Returns dict(status='accept'|'reject'|'timeout'|'vacuous', paths, queries, time, why)."""
    t0 = time.time()
    w_, p0, dts = symbols(H)
    S = Sym()
    if u_free:
        uu = [z3.Real('s'), z3.Real('hx'), z3.Real('hy'), z3.Real('gx'), z3.Real('gy')]
    else:
        uu = list(u)
    base = [A_f(uu, p0, dts, S)] if u_free else [A_f([zv(x) for x in uu], p0, dts, S)]
    npaths = nq = 0
    def fn(op):
        w = planner(rev, uu, op, m)
        return w, controller(w, p0, dts, op)
    s_ = zv(uu[0]) if not u_free else uu[0]
    g = (zv(uu[3]), zv(uu[4])) if not u_free else (uu[3], uu[4])
    def ask(s, f):
        nonlocal nq
        s.push(); s.add(f); r = tcheck(s, deadline); s.pop(); nq += 1
        return r
    try:
        for pc, (w, ys), s in explore(base, fn, deadline=deadline):
            npaths += 1
            ys = [(simp(y[0]), simp(y[1])) for y in ys]
            if order == 'fair':
                r = ask(s, z3.Or(*[fence_viol(y, s_) for y in ys]))
                if r != z3.unsat:
                    return dict(status='reject' if r == z3.sat else 'unknown', why='fence', paths=npaths, queries=nq, time=time.time() - t0)
                if any(ask(s, d2(y, g) > EPS * EPS) == z3.unsat for y in reversed(ys)):
                    continue
            else:
                seen = set()
                for t, y in enumerate(ys):
                    key = (y[0].sexpr(), y[1].sexpr())
                    if key in seen: continue
                    seen.add(key)
                    r = ask(s, fence_viol(y, s_))
                    if r != z3.unsat:
                        return dict(status='reject' if r == z3.sat else 'unknown', why='fence', tick=t, paths=npaths, queries=nq, time=time.time() - t0)
            r = ask(s, z3.And(*[d2(y, g) > EPS * EPS for y in ys]))
            if r != z3.unsat:
                return dict(status='reject' if r == z3.sat else 'unknown', why='goal', paths=npaths, queries=nq, time=time.time() - t0)
    except TimeoutError:
        return dict(status='timeout', paths=npaths, queries=nq, time=time.time() - t0)
    if npaths == 0: return dict(status='vacuous', paths=0, queries=nq, time=time.time() - t0)
    return dict(status='accept', paths=npaths, queries=nq, time=time.time() - t0)


def planner_check(rev, m, rho, deadline):
    """Delegated planner check: M1 code against the quantifier-free G1 with u free (no ticks, no controller)."""
    t0 = time.time()
    uu = [z3.Real('s'), z3.Real('hx'), z3.Real('hy'), z3.Real('gx'), z3.Real('gy')]
    S = Sym()
    base = [A1(uu, S)]
    npaths = 0; bad = None
    try:
        for pc, w, s in explore(base, lambda op: planner(rev, uu, op, m), deadline=deadline):
            npaths += 1
            s.push(); s.add(z3.Not(G1(uu, [simp(x) for x in w], zv(rho), S))); r = tcheck(s, deadline)
            if r != z3.unsat:
                bad = str(r)
                if r == z3.sat:
                    mm = s.model(); bad = {str(x): str(mm.eval(x, model_completion=True)) for x in uu}
                s.pop(); break
            s.pop()
    except TimeoutError:
        return dict(status='timeout', paths=npaths, time=time.time() - t0)
    return dict(status='pass' if bad is None else 'fail', paths=npaths, time=time.time() - t0, cex=bad)


# ------------------------------------------------------------------ E1 (a): closed-form G1 against Z3
def g1_z3_query(args):
    """For fixed (u,w): is A and A2 and G2 and not G satisfiable (p0, dt, y_0..y_H free)? Split over the disjuncts
    of not G (fence side x tick, goal); returns 'sat' if any part is sat, 'unsat' if all are."""
    u, w, rho, H, tmo = args
    t0 = time.time()
    p0 = [z3.Real('px'), z3.Real('py')]; dts = [z3.Real('dt%d' % t) for t in range(H)]
    ys = [(z3.Real('y%dx' % t), z3.Real('y%dy' % t)) for t in range(H + 1)]
    S = Sym(); uz = [zv(x) for x in u]; wz = [zv(x) for x in w]
    A = A_f(uz, p0, dts, S)
    P = P_f(wz, p0, dts, S)
    T = z3.And(*[tube(y, p0, wz, zv(rho)) for y in ys], z3.Or(*[d2(y, wz[2:]) <= zv(ETA * ETA) for y in ys]))
    G2 = z3.Or(z3.Not(P), T)
    s_ = uz[0]; g = uz[3:]
    parts = [y[0] > s_ for y in ys] + [-y[0] > s_ for y in ys] + [y[1] > s_ for y in ys] + [-y[1] > s_ for y in ys]
    parts.append(z3.And(*[d2(y, g) > EPS * EPS for y in ys]))
    verdict = 'unsat'
    for part in parts:
        sv = z3.Solver(); sv.set('timeout', int(tmo * 1000))
        sv.add(A, V_f(wz, S), G2, part)
        r = sv.check()
        if r == z3.sat: verdict = 'sat'; break
        if r != z3.unsat: verdict = 'unknown'
    return verdict, time.time() - t0


def rand_frac(rng, lo, hi, q=4):
    """Random rational on a 1/q grid in [lo,hi]."""
    a, b = math.ceil(lo * q), math.floor(hi * q)
    return Fr(rng.randint(a, b), q)


def sample_u(rng, kind='any'):
    s = Fr(rng.randint(TOP['slo'], TOP['shi']))
    hm = s - TOP['hm']; gm = s + fr_exact(TOP['gout'])
    if kind == 'edge' and rng.random() < 0.5:
        hx = rand_frac(rng, float(hm) - 2.5, float(hm)) * rng.choice([1, -1]); hy = rand_frac(rng, -float(hm), float(hm))
    else:
        hx, hy = rand_frac(rng, -float(hm), float(hm)), rand_frac(rng, -float(hm), float(hm))
    r = rng.random()
    if kind == 'edge' and r < 0.45:
        gx = rand_frac(rng, float(gm) - 3, float(gm)) * rng.choice([1, -1]); gy = rand_frac(rng, -float(gm), float(gm))
        if rng.random() < 0.5: gx, gy = gy, gx
    elif kind == 'edge' and r < 0.7:
        gx = min(max(hx + rand_frac(rng, -12, 12), -gm), gm); gy = min(max(hy + rand_frac(rng, -12, 12), -gm), gm)
    else:
        gx, gy = rand_frac(rng, -float(gm), float(gm)), rand_frac(rng, -float(gm), float(gm))
    return (s, hx, hy, gx, gy)


def core_parts(u, w, rho):
    """Which conjuncts of the G1 core fail (Fractions, exact)."""
    s, hx, hy, gx, gy = u
    n = lambda a, b: max(abs(a), abs(b))
    L = n(w[0] - hx, w[1] - hy)
    out = []
    if not (CTRL['lmin'] + DELTA <= L <= CTRL['lmax'] - DELTA): out.append('ii-leg1')
    if not (n(hx, hy) <= s - rho - DELTA): out.append('iii-home')
    if not n(w[0], w[1]) <= s - rho: out.append('iii-w1')
    if not n(w[2], w[3]) <= s - rho: out.append('iii-w2')
    if not ((w[2] - gx) ** 2 + (w[3] - gy) ** 2 <= (EPS - ETA) ** 2): out.append('iv-goal')
    if not Vw(w, Num()): out.append('V')
    return out


def sample_w_true(rng, u, rho):
    s, hx, hy, gx, gy = u
    for _ in range(2000):
        c = s - rho
        w2 = (min(max(gx + rand_frac(rng, -1.7, 1.7), -c), c), min(max(gy + rand_frac(rng, -1.7, 1.7), -c), c))
        w1 = (rand_frac(rng, -float(c), float(c)), rand_frac(rng, -float(c), float(c)))
        w = (w1[0], w1[1], w2[0], w2[1])
        if G1(u, w, rho, Num()) and not core_parts(u, w, rho): return w
    return None


def sample_w_false(rng, u, rho):
    """A mission in V, with A1(u), that fails exactly one core conjunct by a small margin."""
    s, hx, hy, gx, gy = u
    base = sample_w_true(rng, u, rho)
    if base is None: return None, None
    which = rng.choice(['ii-leg1', 'iii-waypoint', 'iv-goal', 'iii-home'])
    for _ in range(2000):
        w = list(base)
        if which == 'ii-leg1':
            L = CTRL['lmin'] + DELTA - rand_frac(rng, 0.05, 0.9, 20)
            w[0], w[1] = hx + L * rng.choice([1, -1]), hy + rand_frac(rng, -float(L), float(L))
        elif which == 'iii-waypoint':
            k = rng.choice([0, 1, 2, 3]); w[k] = (s - rho + rand_frac(rng, 0.05, 0.9, 20)) * rng.choice([1, -1])
        elif which == 'iv-goal':
            ang = rng.uniform(0, 2 * math.pi); r = EPS - ETA + rand_frac(rng, 0.05, 0.4, 20)
            w[2] = gx + Fr(round(r * math.cos(ang) * 1000), 1000); w[3] = gy + Fr(round(r * math.sin(ang) * 1000), 1000)
        else:
            return None, None
        w = tuple(w)
        parts = [('iii-waypoint' if x.startswith('iii-w') else x) for x in core_parts(u, w, rho)]
        if parts == [which] and A1(u, Num()): return w, which
    return None, None


# ------------------------------------------------------------------ worker wrappers for the process pool
def _mono_worker(args):
    u, rev, m, H, tmo = args
    return mono_check(u, rev, m, H, time.time() + tmo)


def _step2_worker(args):
    H, chain, tmo = args
    return step2(H, chain, tmo)


def _mono_free_worker(args):
    H, m, tmo, order = args
    r = mono_check(None, 4, m, H, time.time() + tmo, u_free=True, order=order)
    r['H'] = H; r['order'] = order
    return r


# ------------------------------------------------------------------ figures
def setup_mpl():
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    plt.rcParams.update({'font.family': 'serif', 'font.serif': ['DejaVu Serif', 'Times New Roman', 'Times'],
                         'font.size': 8, 'axes.labelsize': 8, 'legend.fontsize': 7, 'xtick.labelsize': 7,
                         'ytick.labelsize': 7, 'axes.prop_cycle': matplotlib.cycler(color=['0.0', '0.45', '0.7']),
                         'lines.linewidth': 1.0, 'pdf.fonttype': 42})
    return plt


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--quick', action='store_true'); ap.add_argument('--full', action='store_true')
    ap.add_argument('--figures-only', '--plot-only', dest='figures_only', action='store_true',
                    help='redraw all figures and results.md from notes/validation/results.json (no experiments)')
    args = ap.parse_args()
    quick = args.quick and not args.full
    global FIG
    if quick: FIG = os.path.join(FIG, 'quick')        # the quick subset never overwrites the full-run figures
    os.makedirs(FIG, exist_ok=True)
    if args.figures_only:
        with open(os.path.join(OUT, 'results.json' if not quick else 'results-quick.json')) as f: R = json.load(f)
        samp = sample_controller(None, R['E2']['H_cert_min'], R['E5']['controller_sampling']['n'])
        figures(R, R['E2']['runs'], [Fr(c).limit_denominator(1000) for c in R['step1']['chain']],
                Fr(R['E2']['rho_star']).limit_denominator(1000), samp)
        write_md(R, quick)
        return 0 if R['all_ok'] else 1
    T_START = time.time()
    os.makedirs(FIG, exist_ok=True); os.makedirs(OUT, exist_ok=True)
    rng = random.Random(SEED); np.random.seed(SEED)
    print('Z3 version', z3.get_version_string(), '| mode', 'quick' if quick else 'full', flush=True)
    ncpu = max(1, min(8, (os.cpu_count() or 2) - 1))
    pool = mp.get_context('spawn').Pool(ncpu)
    R = dict(workers=ncpu, z3=z3.get_version_string(), mode='quick' if quick else 'full', seed=SEED, params=dict(CTRL=CTRL, TOP=TOP))
    ok_all = True
    soundness = []

    # ---------------- step 1: chain
    rho1 = rho1_from_runs()
    rho1f = Fr(math.floor(rho1 * 100 + 1e-6), 100)   # tolerance: the float maximum 0.9499999999999993 is 0.95
    kappa = Fr(1, 20); kch = 8
    chain = [rho1f + j * kappa for j in range(kch)]
    R['step1'] = dict(rho1_observed=rho1, rho1=float(rho1f), kappa=float(kappa), k=kch, chain=[float(c) for c in chain],
                      test_legs=len(TEST_LEGS))
    print('step 1: rho_1 observed %.4f -> chain %s' % (rho1, [float(c) for c in chain]), flush=True)

    # ---------------- E2: certification over H (in parallel); the long jobs that only need rho_j* start early
    Hs = [2, 4, 8, 16] if quick else [2, 4, 8, 16, 32, 64, 128]   # H=256, 512: one-off runs (log), to stay under 20 min
    tmo2 = 60 if quick else 300
    e2_async = [pool.apply_async(_step2_worker, ((H, chain, tmo2),)) for H in Hs]
    tmo3 = 60 if quick else 600
    Hs3 = [2, 4, 8] if quick else [2, 4, 8, 16, 32]
    early = None
    for H, a in zip(Hs, e2_async):          # smallest certified horizon from the short runs
        r = a.get()
        if r['certified']: early = r; break
    rho_early = chain[early['jstar'] - 1] if early else chain[-1]
    single_async = None if quick else pool.map_async(_single_formula, [(H, float(rho_early), 60) for H in (1, 2, 4)])
    e2 = [a.get() for a in e2_async]
    R['E2'] = dict(H=Hs, timeout_s=tmo2, runs=[{k: v for k, v in r.items()} for r in e2])
    for r in e2:
        print('E2 H=%d reach=%s j*=%s tube %.1fs total %.1fs checks %s' % (r['H'], r['reach']['status'], r['jstar'], r['tube_time'],
              r['total_time'], [(c['j'], c['status'], round(c['time'], 1)) for c in r['checks']]), flush=True)
    cert = [r for r in e2 if r['certified']]
    if not cert:
        print('no controller guarantee at any H'); ok_all = False
        Hc = None
    Hc = min(r['H'] for r in cert) if cert else None
    rc = [r for r in e2 if r['H'] == Hc][0]
    jstar = rc['jstar']; rho_star = chain[jstar - 1]
    R['E2']['H_cert_min'] = Hc; R['E2']['jstar'] = jstar; R['E2']['rho_star'] = float(rho_star)
    # a radius below rho_1 must fail (counterexample trajectory)
    below = rho1f - kappa
    cb = certify_check(Hc, below, time.time() + tmo2, want_cex=True)
    R['E2']['below'] = dict(rho=float(below), status=cb['status'], time=cb['time'], tick=cb.get('tick'), cex=cb.get('cex'))
    if cb['status'] != 'sat': ok_all = False
    soundness.append(('chain not trivial: rho=%.2f fails' % float(below), cb['status'] == 'sat'))
    print('E2 below rho_1: rho=%.2f %s at tick %s, dev %.3f' % (float(below), cb['status'], cb.get('tick'),
          cb['cex']['dev'] if cb.get('cex') else float('nan')), flush=True)
    jst = sorted(set(r['jstar'] for r in cert))
    if rho_early != rho_star:
        soundness.append(('rho_j* of the early start equals rho_j* of the smallest certified H', False)); ok_all = False
    R['E2']['jstar_all_certified_H'] = jst

    # ---------------- E1 (a): closed-form G1 vs Z3, controller free, small horizon
    N = 12 if quick else 60
    Hs1 = 1                      # the pointwise lemma needs H >= m = 1 (one eventually-conjunct in A, T)
    tasks_t, tasks_f = [], []
    while len(tasks_t) < N:
        u = sample_u(rng, 'edge')
        if not A1(u, Num()) or bad_closed(u, rho_star): continue
        w = sample_w_true(rng, u, rho_star)
        if w is not None: tasks_t.append((u, w))
    whyf = []
    while len(tasks_f) < N:
        u = sample_u(rng, 'edge')
        if not A1(u, Num()) or bad_closed(u, rho_star): continue
        w, which = sample_w_false(rng, u, rho_star)
        if w is not None: tasks_f.append((u, w)); whyf.append(which)
    t0 = time.time()
    res_t = pool.map(g1_z3_query, [(u, w, rho_star, Hs1, 120) for u, w in tasks_t])
    res_f = pool.map(g1_z3_query, [(u, w, rho_star, Hs1, 120) for u, w in tasks_f])
    ct = {k: sum(1 for r in res_t if r[0] == k) for k in ('unsat', 'sat', 'unknown')}
    cf = {k: sum(1 for r in res_f if r[0] == k) for k in ('unsat', 'sat', 'unknown')}
    byw = {}
    for (r, _), wh in zip(res_f, whyf): byw.setdefault(wh, {}).setdefault(r, 0); byw[wh][r] += 1
    R['E1a'] = dict(N=N, H=Hs1, rho=float(rho_star), G1_true=ct, G1_false=cf, G1_false_by_conjunct=byw,
                    time_true=[r[1] for r in res_t], time_false=[r[1] for r in res_f], wall=time.time() - t0)
    s1 = ct['unsat'] == N; s2 = cf['sat'] == N
    soundness.append(('E1a G1 true -> no counterexample (%d/%d unsat)' % (ct['unsat'], N), s1))
    soundness.append(('E1a G1 false -> witness (%d/%d sat)' % (cf['sat'], N), s2))
    ok_all &= s1 and s2
    print('E1a: G1 true %s ; G1 false %s ; by conjunct %s (%.1fs, slowest query %.1fs)' % (ct, cf, byw, time.time() - t0,
          max(r[1] for r in res_t + res_f)), flush=True)

    # ---------------- E1 (b): end-to-end delegated vs monolithic at fixed u
    M = 12 if quick else 60
    He = Hc
    us = []
    while len(us) < M:
        u = sample_u(rng, 'edge')
        if A1(u, Num()): us.append(u)
    tasks = [(u, rev, rho_star, He, 120) for u in us for rev in (1, 2, 3, 4)]
    t0 = time.time()
    mono = pool.map(_mono_worker, tasks)
    rows = []
    for (u, rev, _, _, _), mo in zip(tasks, mono):
        w = planner(rev, u, Num(), rho_star)
        dg = bool(G1(u, w, rho_star, Num())) and rc['certified']
        rows.append(dict(u=[str(x) for x in u], rev=rev, w=[str(x) for x in w], deleg=dg, mono=mo['status'],
                         why_mono=mo.get('why'), parts=core_parts(u, w, rho_star), paths=mo['paths'], time=mo['time']))
    unsound = [r for r in rows if r['deleg'] and r['mono'] != 'accept']
    cons = [r for r in rows if (not r['deleg']) and r['mono'] == 'accept']
    unk = [r for r in rows if r['mono'] not in ('accept', 'reject')]
    tab = {}
    for r in rows:
        key = 'R%d' % r['rev']; tab.setdefault(key, dict(both_accept=0, both_reject=0, deleg_rejects_mono_accepts=0,
                                                         deleg_accepts_mono_rejects=0, mono_unknown=0))
        if r['mono'] not in ('accept', 'reject'): tab[key]['mono_unknown'] += 1
        elif r['deleg'] and r['mono'] == 'accept': tab[key]['both_accept'] += 1
        elif (not r['deleg']) and r['mono'] == 'reject': tab[key]['both_reject'] += 1
        elif not r['deleg']: tab[key]['deleg_rejects_mono_accepts'] += 1
        else: tab[key]['deleg_accepts_mono_rejects'] += 1
    cls_ = {}
    for r in cons:
        k = '+'.join(r['parts']) or 'controller not certified'; cls_[k] = cls_.get(k, 0) + 1
    R['E1b'] = dict(M=M, H=He, rho=float(rho_star), table=tab, unsound=len(unsound), conservative=len(cons),
                    conservative_classes=cls_, mono_unknown=len(unk), wall=time.time() - t0,
                    mono_time_mean=float(np.mean([r['time'] for r in rows])), rows=rows)
    soundness.append(('E1b delegation accepts and monolithic rejects: %d cases' % len(unsound), len(unsound) == 0 and len(unk) == 0))
    ok_all &= len(unsound) == 0 and len(unk) == 0
    print('E1b: %s unsound=%d conservative=%d classes=%s (%.1fs)' % (tab, len(unsound), len(cons), cls_, time.time() - t0), flush=True)

    # ---------------- E3: speed. Wait for every parallel job, then measure on an idle pool, one check at a time.
    if single_async is not None:
        R['E2']['single_formula'] = single_async.get()
        print('E2 single-formula encoding:', R['E2']['single_formula'], flush=True)
    load = os.getloadavg()
    fixed_us = us[:8]
    q = []
    for H in Hs3:
        row = dict(H=H)
        row['step2'] = step2(H, chain, tmo2)
        row['planner'] = {('R%d' % rev): planner_check(rev, rho_star, rho_star, time.time() + tmo3) for rev in (1, 2, 3, 4)}
        row['mono'] = {('R%d' % rev): mono_check(None, rev, rho_star, H, time.time() + tmo3, u_free=True) for rev in (1, 2, 3, 4)}
        fx = [mono_check(u, 4, rho_star, H, time.time() + tmo3) for u in fixed_us]
        row['mono_fixed_u'] = dict(mean_time=float(np.mean([r['time'] for r in fx])), statuses=[r['status'] for r in fx])
        q.append(row)
        print('E3 quiet H=%d: step2 %.2fs (certified %s) | mono fair %s | planner %s | fixed u %.3fs' % (
            H, row['step2']['total_time'], row['step2']['certified'],
            {k: (v['status'], round(v['time'], 3)) for k, v in row['mono'].items()},
            {k: (v['status'], round(v['time'], 3)) for k, v in row['planner'].items()}, row['mono_fixed_u']['mean_time']), flush=True)
    # original atom order, sequential on the idle pool, same 600 s limit (H=2 and the cost horizon 8 only: each
    # timeout costs the full limit, and the 20-minute budget allows two)
    mono_orig = []
    for H in ([2, 8] if 8 in Hs3 else Hs3[:2]):
        r = mono_check(None, 4, rho_star, H, time.time() + (30 if quick else tmo3), u_free=True, order='orig'); r['H'] = H; r['order'] = 'orig'
        mono_orig.append(r)
    print('E3 monolithic, original atom order (u free, R4, sequential):', [(r['H'], r['status'], round(r['time'], 1), r['paths']) for r in mono_orig], flush=True)
    load_after = os.getloadavg()
    for row in q:
        st = row['step2']
        row['step2'] = dict(total=st['total_time'], certified=st['certified'], jstar=st['jstar'], reach=st['reach']['status'])
    pc = q[0]['planner']['R4']
    R['E3'] = dict(H=Hs3, timeout_s=tmo3, load_before=load, load_after=load_after, quiet=q,
                   mono_orig=[{k: v for k, v in r.items()} for r in mono_orig])
    for row in q:
        dg = row['step2']['certified'] and row['planner']['R4']['status'] == 'pass'
        if dg and row['mono']['R4']['status'] != 'accept':
            soundness.append(('E3 delegation accepts R4 at H=%d but the monolithic check gives %s' % (row['H'], row['mono']['R4']['status']), False)); ok_all = False
    soundness.append(('E3 planner R4 passes the G1 check (Z3, u free)', all(row['planner']['R4']['status'] == 'pass' for row in q)))
    ok_all &= soundness[-1][1]
    for k in ('R1', 'R2', 'R3'):
        soundness.append(('E3 wrong revision %s fails the G1 check (Z3, u free)' % k, all(row['planner'][k]['status'] == 'fail' for row in q)))
        ok_all &= soundness[-1][1]
    R['E3']['completeness_loss'] = [row['H'] for row in q if row['mono']['R4']['status'] == 'accept' and not row['step2']['certified']]
    # cost model from measured values at every certified H; main point: smallest certified H
    costs = []
    for row in q:
        if not (row['step2']['certified'] and row['mono']['R4']['status'] == 'accept'): continue
        cM = row['mono']['R4']['time']; c2 = row['step2']['total']; c1 = row['planner']['R4']['time']
        rej = {k: row['mono'][k]['time'] for k in ('R1', 'R2', 'R3')}
        prej = {k: row['planner'][k]['time'] for k in ('R1', 'R2', 'R3')}
        nb = c2 / (cM - c1) if cM > c1 else float('inf')
        seq_m = sum(rej.values()) + cM; seq_d = sum(prej.values()) + c1
        costs.append(dict(H=row['H'], c_M=cM, c_M_rej=rej, c_2=c2, c_1=c1, c_1_rej=prej, break_even_n=nb,
                          n_star=(math.floor(nb) + 1) if math.isfinite(nb) else None,
                          seq_mono=seq_m, seq_deleg=c2 + seq_d, seq_deleg_per_query=seq_d,
                          break_even_Q=(c2 / (seq_m - seq_d)) if seq_m > seq_d else float('inf')))
    R['E3']['costs'] = costs
    R['E3']['cost'] = costs[0] if costs else None
    for c in costs:
        print('E3 cost H=%d: c_M=%.2f c_2=%.2f c_1=%.3f n>%.2f; R1..R4 mono %.2fs deleg %.2fs' % (c['H'], c['c_M'], c['c_2'], c['c_1'], c['break_even_n'], c['seq_mono'], c['seq_deleg']), flush=True)

    # ---------------- E5: two discharge means per delegate
    t0 = time.time()
    ngrid = grid_planner(rho_star, quick)
    R['E5'] = dict(planner_grid=ngrid, planner_z3=dict(status=pc['status'], time=pc['time']))
    agree = (ngrid['fail'] == 0) == (pc['status'] == 'pass')
    soundness.append(('E5 planner: grid enumeration and Z3 agree (grid fails %d of %d)' % (ngrid['fail'], ngrid['n']), agree))
    ok_all &= agree
    print('E5 planner grid: %s (%.1fs)' % ({k: v for k, v in ngrid.items() if k != 'examples'}, ngrid['time']), flush=True)
    samp = sample_controller(rng, Hc, 3000 if quick else 40000)
    R['E5']['controller_sampling'] = {k: v for k, v in samp.items() if k != 'devs'}
    ok5 = samp['max_dev'] <= float(rho_star) + 1e-9 and samp['reach_fail'] == 0
    soundness.append(('E5 controller sampling: max deviation %.4f <= rho_j* %.3f, reach failures %d' % (samp['max_dev'], float(rho_star), samp['reach_fail']), ok5))
    ok_all &= ok5
    print('E5 controller sampling: max dev %.4f over %d runs, reach failures %d (%.1fs)' % (samp['max_dev'], samp['n'], samp['reach_fail'], samp['time']), flush=True)

    # ---------------- E4: Section 6 reproduction (Euclidean, rho=2) and the validation-instance Bad set
    e4 = section6(rng, quick)
    R['E4'] = e4
    for k, v in e4['checks'].items():
        soundness.append(('E4 ' + k, bool(v))); ok_all &= bool(v)
    badv = bad_validation(rho_star, quick)
    R['E4']['validation_bad'] = badv
    print('E4:', e4['checks'], 'validation Bad points', badv['bad'], 'of', badv['n'], flush=True)

    pool.close()
    R['soundness'] = [dict(check=a, ok=bool(b)) for a, b in soundness]
    R['all_ok'] = bool(ok_all)
    R['wall_time_s'] = time.time() - T_START
    with open(os.path.join(OUT, 'results.json' if not quick else 'results-quick.json'), 'w') as f:
        json.dump(R, f, indent=1, default=str)
    # ---------------- figures
    figures(R, e2, chain, rho_star, samp)
    write_md(R, quick)
    print('soundness:', 'ALL PASS' if ok_all else 'FAILURES', '| wall %.1fs' % R['wall_time_s'], flush=True)
    return 0 if ok_all else 1


def _single_formula(args):
    H, rho, tmo = args
    w, p0, dts = symbols(H)
    S = Sym()
    ys = controller(w, p0, dts, S)
    sv = z3.Solver(); sv.set('timeout', tmo * 1000)
    rz = z3.RealVal(Fr(rho).limit_denominator(1000))
    sv.add(V_f(w, S), P_f(w, p0, dts, S), z3.Or(*[z3.Not(tube(y, p0, w, rz)) for y in ys]), *S.side)
    t0 = time.time(); r = sv.check()
    return dict(H=H, status=str(r), time=time.time() - t0)


def grid_planner(rho, quick):
    """Exhaustive grid over u of A1 with the closed-form G1 (numpy, vectorised); planner R4."""
    t0 = time.time()
    st = 2.5 if quick else 1.0
    ss = [25, 35, 50] if quick else list(range(25, 51, 5))
    rho = float(rho); n = 0; fail = 0; ex = []
    for s in ss:
        hm = s - 3; gm = s + 0.5
        hv = np.arange(-hm, hm + 1e-9, st); gv = np.arange(-gm, gm + 1e-9, st)
        HX, HY = np.meshgrid(hv, hv, indexing='ij'); HX = HX.ravel(); HY = HY.ravel()
        for gx in gv:
            GX = np.full(gv.shape, gx); GY = gv
            hx = HX[:, None]; hy = HY[:, None]; gxx = GX[None, :]; gyy = GY[None, :]
            c = s - rho
            w2x = np.clip(gxx, -c, c) + 0 * hx; w2y = np.clip(gyy, -c, c) + 0 * hx
            near = (np.abs(w2x - hx) < 12) & (np.abs(w2y - hy) < 12)
            w1x = np.where(near, hx + np.where(hx < 0, 20, -20), (hx + w2x) / 2); w1y = np.where(near, hy + 0 * w2y, (hy + w2y) / 2)
            L = np.maximum(np.abs(w1x - hx), np.abs(w1y - hy)); L2 = np.maximum(np.abs(w2x - w1x), np.abs(w2y - w1y))
            okk = ((L2 >= 5) & (L2 <= 100) & (L >= 6) & (L <= 99) & (np.maximum(np.abs(hx), np.abs(hy)) <= s - rho - 1)
                   & (np.maximum(np.abs(w1x), np.abs(w1y)) <= c + 1e-12) & (np.maximum(np.abs(w2x), np.abs(w2y)) <= c + 1e-12)
                   & ((w2x - gxx) ** 2 + (w2y - gyy) ** 2 <= 2.5 ** 2 + 1e-12))
            n += okk.size; f = int((~okk).sum()); fail += f
            if f and len(ex) < 5:
                i, j = np.argwhere(~okk)[0]; ex.append([s, float(HX[i]), float(HY[i]), float(gx), float(GY[j])])
    return dict(n=n, fail=fail, step=st, s_values=ss, time=time.time() - t0, examples=ex)


def sample_controller(rng, H, n):
    """Concrete runs of M2 on random (w, p0, dt) in V and P: max inf-distance to the polyline, reach of w2."""
    t0 = time.time(); r = np.random.default_rng(SEED + 1)
    devs = []; reach_fail = 0; cnt = 0; worst = None
    while cnt < n:
        p0 = r.uniform(-60, 60, 2)
        mode = cnt % 3
        w1 = p0 + (r.uniform(-25, 25, 2) if mode == 0 else r.uniform(-100, 100, 2))
        w2 = w1 + (r.uniform(-30, 30, 2) if mode == 1 else r.uniform(-100, 100, 2))
        if np.max(np.abs(np.r_[w1, w2, p0])) > 100: continue
        L1 = np.max(np.abs(w1 - p0)); L2 = np.max(np.abs(w2 - w1))
        if not (5 <= L1 <= 100 and 5 <= L2 <= 100): continue
        dts = list(r.uniform(0.5, 1.5, H))
        w = (w1[0], w1[1], w2[0], w2[1])
        ys = controller(w, tuple(p0), dts, Num())
        dv = poly_dev(ys, p0, w); devs.append(dv)
        if worst is None or dv > worst[0]: worst = (dv, list(p0), list(w))
        if min(np.hypot(y[0] - w2[0], y[1] - w2[1]) for y in ys) > 0.5: reach_fail += 1
        cnt += 1
    return dict(n=n, H=H, max_dev=float(max(devs)), mean_dev=float(np.mean(devs)), frac_off_polyline=float(np.mean(np.array(devs) > 1e-9)),
                reach_fail=reach_fail, time=time.time() - t0, worst=worst, devs=devs)


# ------------------------------------------------------------------ E4: Section 6 (Euclidean, rho=2)
S6 = dict(s=50.0, rho=2.0, delta=1.0, lmin=5.0, lmax=100.0, eps=3.0, eta=0.5)


def g1_s6(h, g, w1, w2, P=S6):
    nrm = np.linalg.norm; inf = lambda z: np.max(np.abs(z)); s, rho, dl = P['s'], P['rho'], P['delta']
    return (P['lmin'] <= nrm(w2 - w1) <= P['lmax'] and P['lmin'] + dl <= nrm(w1 - h) <= P['lmax'] - dl and inf(h) <= s - rho - dl
            and inf(w1) <= s - rho and inf(w2) <= s - rho and nrm(w2 - g) <= P['eps'] - P['eta'])


def s6_witness(h, g, P=S6):
    s, rho = P['s'], P['rho']; c = s - rho
    q = np.clip(g, -c, c)
    if np.linalg.norm(g - q) > P['eps'] - P['eta'] or np.max(np.abs(h)) > s - rho - P['delta']: return None
    w2 = q
    if np.linalg.norm(h - w2) >= 12: w1 = (h + w2) / 2
    else:
        nh = np.linalg.norm(h)
        w1 = h * (1 - 20 / nh) if nh >= 20 else h + np.array([20.0, 0.0]) * (-1 if h[0] > 0 else 1)
    return (w1, w2) if g1_s6(h, g, w1, w2) else 'FAIL'


def section6(rng, quick):
    out = dict(checks={})
    h, g = np.array([-40., -40.]), np.array([40., 40.])
    miss = {'accepted': ((-30, 30), (40, 40)), 'fence': ((0, -49), (40, 40)), 'goal': ((-30, 30), (44, 40)), 'near-home': ((-36, -40), (-36, 0))}
    res = {k: bool(g1_s6(h, g, np.array(a, float), np.array(b, float))) for k, (a, b) in miss.items()}
    out['missions'] = res
    out['checks']['S6 mission ((-30,30),(40,40)) meets G1'] = res['accepted']
    out['checks']['S6 missions breaking fence/goal/near-home are rejected'] = not (res['fence'] or res['goal'] or res['near-home'])
    # the tube point outside the fence for w1=(0,-49): farthest tube point in direction -y over starts in the disc
    w1 = np.array([0., -49.]); best = None
    for th in np.linspace(0, 2 * np.pi, 721):
        p0 = h + np.array([np.cos(th), np.sin(th)])
        d = w1 - p0; nrm_ = np.array([d[1], -d[0]]) / np.linalg.norm(d)
        for z in (w1 + 2 * nrm_, w1 - 2 * nrm_, w1 + np.array([0, -2.0])):
            if best is None or z[1] < best[1]: best = z
    out['tube_low_point'] = [float(best[0]), float(best[1])]
    p = np.array([-1.72, -50.02]); d0 = min(np.linalg.norm(p - (w1 + lam * (h + np.array([np.cos(t), np.sin(t)]) - w1)))
                                            for lam in np.linspace(0, 1, 401) for t in np.linspace(0, 2 * np.pi, 181))
    out['point_-1.72_-50.02_dist_to_leg1'] = float(d0)
    out['checks']['S6 point (-1.72,-50.02) lies in the rho-tube of some admissible start'] = d0 <= 2.0 + 1e-3
    # Bad formula vs constructed witnesses
    rr = np.random.default_rng(SEED + 2); mism = 0; nb = 20000 if quick else 200000
    for _ in range(nb):
        hh = rr.uniform(-50, 50, 2); gg = rr.uniform(-53, 53, 2)
        q = np.clip(gg, -48, 48); pred = np.max(np.abs(hh)) > 47 or np.linalg.norm(gg - q) > 2.5
        wt = s6_witness(hh, gg)
        if (isinstance(wt, str)) or ((wt is None) != pred): mism += 1
    out['bad_formula_mismatches'] = mism; out['bad_samples'] = nb
    out['checks']['S6 Bad formula agrees with constructed witnesses (%d samples)' % nb] = mism == 0
    found = 0; tried = 0
    for _ in range(60 if quick else 300):
        hh = rr.uniform(-50, 50, 2); gg = rr.uniform(-53, 53, 2)
        q = np.clip(gg, -48, 48)
        if not (np.max(np.abs(hh)) > 47 or np.linalg.norm(gg - q) > 2.5): continue
        tried += 1
        for _ in range(2000):
            a = rr.uniform(-48, 48, 2); b = q + rr.uniform(-2.5, 2.5, 2)
            if g1_s6(hh, gg, a, b): found += 1; break
    out['bad_random_search'] = dict(inputs=tried, found=found)
    out['checks']['S6 no mission found for Bad inputs by random search'] = found == 0
    return out


def bad_validation(rho, quick):
    rr = np.random.default_rng(SEED + 3); n = 20000 if quick else 200000; bad = 0
    for _ in range(n):
        s = rr.integers(25, 51); hh = rr.uniform(-(s - 3), s - 3, 2); gg = rr.uniform(-(s + .5), s + .5, 2)
        bad += bad_closed((float(s), hh[0], hh[1], gg[0], gg[1]), float(rho))
    return dict(n=n, bad=int(bad))


# ------------------------------------------------------------------ figures
def figures(R, e2, chain, rho_star, samp):
    plt = setup_mpl()
    from matplotlib.patches import Rectangle, Polygon
    # E2 time per H
    fig, ax = plt.subplots(figsize=(3.3, 2.3))
    Hs = [r['H'] for r in e2]
    ax.loglog(Hs, [max(r['tube_time'], 1e-3) for r in e2], 'k-o', ms=3, label='tube checks (binary search)')
    ax.loglog(Hs, [max(r['reach']['time'], 1e-3) for r in e2], '--s', color='0.45', ms=3, label='reach check')
    ax.loglog(Hs, [max(r['total_time'], 1e-3) for r in e2], ':^', color='0.0', ms=3, label='step 2 total')
    for r in e2:
        for c in r['checks']:
            if c['status'] == 'timeout': ax.plot(r['H'], c['time'], 'kx')
    ax.set_xscale('log', base=2); ax.set_xticks(Hs); ax.set_xticklabels([str(h) for h in Hs])
    ax.set_xlabel('horizon $H$ (ticks)'); ax.set_ylabel('time (s)'); ax.legend(frameon=False)
    fig.tight_layout(); fig.savefig(os.path.join(FIG, 'e2_certification_time.pdf')); plt.close(fig)
    # single-panel figures placed at 3.3 in: every text element at 8 pt
    small = {'font.size': 8, 'axes.labelsize': 8, 'legend.fontsize': 8, 'xtick.labelsize': 8, 'ytick.labelsize': 8,
             'axes.titlesize': 8}
    with plt.rc_context(small):
        # E2 counterexample
        cex = R['E2']['below'].get('cex')
        if cex:
            fig, ax = plt.subplots(figsize=(3.3, 3.1))
            p0 = np.array(cex['p0']); w = np.array(cex['w']); ys = np.array(cex['ys'])
            rb = R['E2']['below']['rho']; t = R['E2']['below']['tick']
            poly = np.array([p0, w[:2], w[2:]])
            draw_inf_tube(ax, poly, rb, '0.85')
            ax.plot(poly[:, 0], poly[:, 1], '-', color='0.4', lw=0.8, label='polyline')
            ax.plot(ys[:, 0], ys[:, 1], 'k.-', ms=4, lw=0.6, label='targets $y_t$')
            ax.plot(ys[t, 0], ys[t, 1], 'ko', mfc='none', ms=9, label='tick %d, outside' % t)
            ax.set_aspect('equal'); ax.set_xlabel('$x$ (m)'); ax.set_ylabel('$y$ (m)')
            c = (w[:2] + ys[t]) / 2; ax.set_xlim(c[0] - 6, c[0] + 6); ax.set_ylim(c[1] - 7, c[1] + 5)
            ax.legend(frameon=False, loc='lower left')
            ax.set_title('$\\rho=%.2f$ m refuted ($H=%d$)' % (rb, R['E2']['H_cert_min']))
            fig.tight_layout(); fig.savefig(os.path.join(FIG, 'e2_counterexample.pdf')); plt.close(fig)
        # E3 time vs H
        e3 = R['E3']; q = e3['quiet']; H3 = [r['H'] for r in q]
        fig, ax = plt.subplots(figsize=(3.3, 2.8))
        ax.loglog(H3, [r['mono']['R4']['time'] for r in q], 'k-o', ms=3, label='monolithic, $u$ free')
        mo = e3['mono_orig']
        ax.loglog([r['H'] for r in mo], [r['time'] for r in mo], '-', color='0.6', lw=0.8, label='same, original order (x = timeout)')
        for r in mo:
            if r['status'] == 'timeout': ax.plot(r['H'], r['time'], 'kx', ms=6)
        ax.loglog(H3, [r['step2']['total'] for r in q], '--', color='0.45', label='step 2 (open: not certified)')
        for r in q:
            ax.plot(r['H'], r['step2']['total'], 's', ms=3.5, color='0.45', mfc='0.45' if r['step2']['certified'] else 'white')
        ax.loglog(H3, [r['planner']['R4']['time'] for r in q], ':', color='0.0', label='planner check against $G_1$')
        ax.loglog(H3, [r['mono_fixed_u']['mean_time'] for r in q], '-.v', color='0.6', ms=3, label='monolithic, one fixed $u$')
        ax.set_xscale('log', base=2); ax.set_xticks(H3); ax.set_xticklabels([str(h) for h in H3])
        ax.set_ylim(1e-2, 3e5)
        ax.set_xlabel('horizon $H$ (ticks)'); ax.set_ylabel('time (s)')
        ax.legend(frameon=False, loc='upper left', handlelength=2.2, borderaxespad=0.3, labelspacing=0.2, fontsize=7.5)
        fig.tight_layout(); fig.savefig(os.path.join(FIG, 'e3_time_vs_H.pdf')); plt.close(fig)
        # E3 cumulative cost, one panel each (measured unit costs at the smallest certified H)
        cst = e3.get('cost')
        if cst:
            for name in ('e3_cumulative_R.pdf', 'e3_cumulative_Q.pdf'):
                fig, ax = plt.subplots(figsize=(3.3, 2.5))
                cumulative_panel(ax, cst, name.endswith('R.pdf'))
                fig.tight_layout(); fig.savefig(os.path.join(FIG, name)); plt.close(fig)
    # E3 cumulative cost, two panels (kept for existing includes)
    cst = R['E3'].get('cost')
    if cst:
        with plt.rc_context(small):
            fig, axs = plt.subplots(1, 2, figsize=(7, 2.5))
            cumulative_panel(axs[0], cst, True); cumulative_panel(axs[1], cst, False)
            fig.tight_layout(); fig.savefig(os.path.join(FIG, 'e3_cumulative_cost.pdf')); plt.close(fig)
    with plt.rc_context(small):
        # E1 bars
        tab = R['E1b']['table']
        fig, ax = plt.subplots(figsize=(3.3, 2.9))
        keys = ['both_accept', 'deleg_rejects_mono_accepts', 'both_reject', 'deleg_accepts_mono_rejects']
        labs = ['both accept', 'delegation rejects, monolithic accepts', 'both reject', 'delegation accepts, monolithic rejects']
        shades = ['0.0', '0.45', '0.75', 'white']
        x = np.arange(4); bw = 0.2
        top = max(tab['R%d' % r][k] for r in (1, 2, 3, 4) for k in keys)
        for i, (k, lab, sh) in enumerate(zip(keys, labs, shades)):
            ax.bar(x + (i - 1.5) * bw, [tab['R%d' % r][k] for r in (1, 2, 3, 4)], bw, color=sh, edgecolor='k', lw=0.5, label=lab)
        ax.set_ylim(0, top * 1.75)
        ax.set_xticks(x); ax.set_xticklabels(['R1', 'R2', 'R3', 'R4']); ax.set_xlabel('planner revision'); ax.set_ylabel('inputs $u$ (count)')
        ax.legend(frameon=False, loc='upper left', borderaxespad=0.3, labelspacing=0.25, handlelength=1.2)
        fig.tight_layout(); fig.savefig(os.path.join(FIG, 'e1_end_to_end.pdf')); plt.close(fig)
    # E4 geometry of Section 6 and the Bad set
    h = np.array([-40., -40.])
    fig, axs = plt.subplots(1, 3, figsize=(7, 2.6), gridspec_kw=dict(width_ratios=[1.25, 1, 1]))
    ax = axs[0]
    ax.add_patch(Rectangle((-50, -50), 100, 100, fill=False, ec='k', lw=1.0))
    ax.add_patch(Rectangle((-48, -48), 96, 96, fill=True, fc='0.93', ec='0.5', lw=0.6, ls='--'))
    for (w1, w2), shade, lab in ((((-30, 30), (40, 40)), '0.65', 'accepted'), (((0, -49), (40, 40)), '0.3', 'rejected')):
        poly = np.array([h, w1, w2], float)
        draw_disc_tube(ax, poly, 2.0, shade, alpha=0.45)
        ax.plot(poly[:, 0], poly[:, 1], color='k', lw=0.6 if lab == 'accepted' else 0.9, ls='-' if lab == 'rejected' else '--',
                label='%s mission' % lab)
    ax.plot(-1.72, -50.02, 'kx', ms=6); ax.annotate('(-1.72, -50.02)', (-1.72, -50.02), (8, -58), fontsize=6, arrowprops=dict(arrowstyle='-', lw=0.5))
    ax.plot(*h, 'ko', ms=3); ax.text(h[0] - 3, h[1] - 6, '$h$', fontsize=7); ax.plot(40, 40, 'k*', ms=6); ax.text(41, 43, '$g$', fontsize=7)
    ax.set_xlim(-58, 58); ax.set_ylim(-62, 56); ax.set_aspect('equal'); ax.set_xlabel('$x$ (m)'); ax.set_ylabel('$y$ (m)')
    ax.set_title('(a) $\\rho$-tubes; admissible $w_1,w_2$ shaded', fontsize=7)
    ax.legend(frameon=True, framealpha=1, edgecolor='none', loc='center', fontsize=5.5)
    rr = np.random.default_rng(SEED + 4)
    ax = axs[1]
    ax.add_patch(Rectangle((-55, -55), 110, 110, fc='0.8', ec='none'))
    ax.add_patch(Rectangle((-47, -47), 94, 94, fc='white', ec='k', lw=0.6))
    ax.add_patch(Rectangle((-50, -50), 100, 100, fill=False, ec='k', lw=1.0, ls='--'))
    pts = rr.uniform(-50, 50, (160, 2)); g0 = np.array([0., 0.])
    acc = np.array([s6_witness(p, g0) is not None for p in pts])
    ax.plot(pts[acc, 0], pts[acc, 1], '.', color='0.35', ms=2.5, label='accepted (witness meets $G_1$)')
    ax.plot(pts[~acc, 0], pts[~acc, 1], 'kx', ms=3, label='Bad')
    ax.set_aspect('equal'); ax.set_xlim(-55, 55); ax.set_ylim(-55, 55); ax.set_xlabel('$h_x$ (m)'); ax.set_ylabel('$h_y$ (m)')
    ax.set_title('(b) Bad in the $h$-plane ($g=0$)', fontsize=7)
    ax = axs[2]
    xs = np.linspace(-55, 55, 441); X, Y = np.meshgrid(xs, xs)
    D = np.hypot(X - np.clip(X, -48, 48), Y - np.clip(Y, -48, 48))
    ax.contourf(X, Y, (D > 2.5).astype(float), levels=[0.5, 1.5], colors=['0.8'])
    ax.contour(X, Y, D, levels=[2.5], colors='k', linewidths=0.6)
    ax.add_patch(Rectangle((-50, -50), 100, 100, fill=False, ec='k', lw=1.0, ls='--'))
    pts = rr.uniform(-54, 54, (220, 2)); h0 = np.array([0., 0.])
    acc = np.array([s6_witness(h0, p) is not None for p in pts])
    ax.plot(pts[acc, 0], pts[acc, 1], '.', color='0.35', ms=2.5); ax.plot(pts[~acc, 0], pts[~acc, 1], 'kx', ms=3)
    ax.set_aspect('equal'); ax.set_xlim(-55, 55); ax.set_ylim(-55, 55); ax.set_xlabel('$g_x$ (m)'); ax.set_ylabel('$g_y$ (m)')
    ax.set_title('(c) Bad in the $g$-plane ($h=0$)', fontsize=7)
    fig.text(0.62, 0.01, 'shaded: Bad (closed form); dots: a constructed mission meets $G_1$; crosses: no mission found', fontsize=6, ha='center')
    fig.tight_layout(rect=(0, 0.04, 1, 1)); fig.savefig(os.path.join(FIG, 'e4_geometry_bad.pdf')); plt.close(fig)
    # E5 histogram of sampled deviation
    fig, ax = plt.subplots(figsize=(3.3, 2.3))
    dv = np.array(samp['devs']); dv = dv[dv > 1e-9]
    if len(dv):
        ax.hist(dv, bins=40, color='0.6', edgecolor='k', lw=0.3)
    ax.axvline(float(rho_star), color='k', ls='--', lw=0.8); ax.text(float(rho_star), ax.get_ylim()[1] * 0.95, r' $\rho_{j^*}$', fontsize=7, va='top')
    ax.axvline(samp['max_dev'], color='0.4', ls=':', lw=0.8)
    ax.set_xlabel('max inf-distance of $y_t$ to the polyline (m)'); ax.set_ylabel('runs (count)')
    ax.set_title('%d runs, %.1f%% leave the polyline; max %.3f m' % (samp['n'], 100 * samp['frac_off_polyline'], samp['max_dev']), fontsize=7)
    fig.tight_layout(); fig.savefig(os.path.join(FIG, 'e5_controller_sampling.pdf')); plt.close(fig)


def cumulative_panel(ax, c, by_n):
    """by_n: cumulative cost over n accepted planner checks sharing one certification (n*c_M against c_2 + n*c_1);
    otherwise over Q queries, each running the measured revision sequence R1, R2, R3, R4."""
    n = np.arange(1, 9)
    if by_n:
        mono, dele = n * c['c_M'], c['c_2'] + n * c['c_1']; be = c['break_even_n']
        xl = 'accepted planner checks $n$'; lm, ld = 'monolithic $n c_M$', 'delegated $c_2+n c_1$'
    else:
        mono, dele = n * c['seq_mono'], c['c_2'] + n * c['seq_deleg_per_query']; be = c['break_even_Q']
        xl = 'queries $Q$ (each R1, R2, R3, R4)'; lm, ld = 'monolithic', 'delegated'
    ax.plot(n, mono, 'k-o', ms=3, label=lm); ax.plot(n, dele, '--s', color='0.45', ms=3, label=ld)
    if np.isfinite(be) and be <= 8:
        ax.axvline(be, color='0.6', lw=0.8, ls=':')
        ax.text(be, 0.5, ' break-even\n %.2f' % be, transform=ax.get_xaxis_transform(), va='center', fontsize=7)
    ax.set_title('$H=%d$: $c_M=%.1f$ s, $c_2=%.1f$ s, $c_1=%.2f$ s' % (c['H'], c['c_M'], c['c_2'], c['c_1']), fontsize=8)
    ax.set_xlabel(xl); ax.set_ylabel('cumulative time (s)'); ax.legend(frameon=False, loc='upper left', fontsize=7.5)


def draw_disc_tube(ax, poly, r, shade, alpha=0.4):
    from matplotlib.patches import Circle, Polygon
    for a, b in zip(poly[:-1], poly[1:]):
        d = b - a; n = np.array([-d[1], d[0]]) / np.linalg.norm(d) * r
        ax.add_patch(Polygon([a + n, b + n, b - n, a - n], closed=True, fc=shade, ec='none', alpha=alpha))
    for p in poly: ax.add_patch(Circle(p, r, fc=shade, ec='none', alpha=alpha))


def draw_inf_tube(ax, poly, r, shade):
    from matplotlib.patches import Polygon
    sq = np.array([[r, r], [-r, r], [-r, -r], [r, -r]])
    for a, b in zip(poly[:-1], poly[1:]):
        pts = np.vstack([a + sq, b + sq])
        from math import atan2
        c = pts.mean(axis=0); ang = np.arctan2(pts[:, 1] - c[1], pts[:, 0] - c[0])
        # convex hull (gift wrapping over 8 points)
        hull = convex_hull(pts)
        ax.add_patch(Polygon(hull, closed=True, fc=shade, ec='0.6', lw=0.4))


def convex_hull(P):
    P = sorted(map(tuple, P))
    cross = lambda o, a, b: (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])
    lo, up = [], []
    for p in P:
        while len(lo) >= 2 and cross(lo[-2], lo[-1], p) <= 0: lo.pop()
        lo.append(p)
    for p in reversed(P):
        while len(up) >= 2 and cross(up[-2], up[-1], p) <= 0: up.pop()
        up.append(p)
    return lo[:-1] + up[:-1]


def write_md(R, quick):
    L = []
    L.append('# Validation results (%s run)\n' % R['mode'])
    L.append('Generated by `scripts/validate.py%s`. Z3 %s, seed %d, wall time %.0f s. Overall soundness: **%s**.\n'
             % (' --quick' if quick else '', R['z3'], R['seed'], R['wall_time_s'], 'all checks pass' if R['all_ok'] else 'FAILURES'))
    L.append('## Soundness checks\n')
    for c in R['soundness']: L.append('- [%s] %s' % ('pass' if c['ok'] else 'FAIL', c['check']))
    s1 = R['step1']
    L.append('\n## Step 1 (chain)\n\nrho_1 observed on %d fixed legs with nominal dt: %.4f m; chain rho_j = %.2f + (j-1)*%.2f, j=1..%d.\n'
             % (s1['test_legs'], s1['rho1_observed'], s1['rho1'], s1['kappa'], s1['k']))
    e2 = R['E2']
    L.append('## E2 certification (step 2)\n\n| H | paths | reach | j* | rho_j* | checks (j: status, s) | tube s | total s |\n|---|---|---|---|---|---|---|---|')
    for r in e2['runs']:
        L.append('| %d | %s | %s (%.1f s) | %s | %s | %s | %.1f | %.1f |' % (
            r['H'], r['checks'][0]['paths'] if r['checks'] else '-', r['reach']['status'], r['reach']['time'], r['jstar'],
            '%.2f' % s1['chain'][r['jstar'] - 1] if r['jstar'] else '-',
            ', '.join('%d: %s %.1f' % (c['j'], c['status'], c['time']) for c in r['checks']), r['tube_time'], r['total_time']))
    b = e2['below']
    L.append('\nSmallest certified horizon H=%s, j*=%s, rho_j*=%.2f m. Radius below rho_1: rho=%.2f gives %s at tick %s (deviation of the counterexample %.3f m).'
             % (e2['H_cert_min'], e2['jstar'], e2['rho_star'], b['rho'], b['status'], b['tick'], b['cex']['dev'] if b.get('cex') else float('nan')))
    if 'single_formula' in e2:
        L.append('\nSame controller as one unrolled Z3 formula (tube part, no path enumeration, 60 s limit): ' +
                 ', '.join('H=%d %s %.1f s' % (x['H'], x['status'], x['time']) for x in e2['single_formula']) + '.')
    a = R['E1a']
    L.append('\n## E1 (a) closed-form G1 against Z3 (controller free, H=%d)\n\nG1 true: %s of %d (unsat expected). G1 false: %s of %d (sat expected); by failing conjunct %s.'
             % (a['H'], a['G1_true'], a['N'], a['G1_false'], a['N'], a['G1_false_by_conjunct']))
    bb = R['E1b']
    L.append('\n## E1 (b) end to end, H=%d, %d inputs x 4 revisions\n\n| revision | both accept | delegation rejects, monolithic accepts | both reject | delegation accepts, monolithic rejects | monolithic unknown |\n|---|---|---|---|---|---|'
             % (bb['H'], bb['M']))
    for k in sorted(bb['table']):
        t = bb['table'][k]
        L.append('| %s | %d | %d | %d | %d | %d |' % (k, t['both_accept'], t['deleg_rejects_mono_accepts'], t['both_reject'], t['deleg_accepts_mono_rejects'], t['mono_unknown']))
    L.append('\nUnsound cases (delegation accepts, monolithic rejects): %d. Conservative cases: %d, by failing G1 conjunct: %s.' % (bb['unsound'], bb['conservative'], bb['conservative_classes']))
    e3 = R['E3']
    L.append('\n## E3 speed (measured one check at a time on an idle pool; load average %s before, %s after)\n' % (
        ', '.join('%.2f' % x for x in e3['load_before']), ', '.join('%.2f' % x for x in e3['load_after'])))
    L.append('Workers: E2 (one horizon per worker) and E1 ran on a pool of %d worker processes at the same time; the E3 rows below, including the original-order runs, ran one check at a time in the main process with the pool idle; E4 and E5 ran in the main process.\n' % R.get('workers', 8))
    L.append('| H | monolithic R4, u free (fair order) | monolithic R4, original order | step 2 total | planner check R4 | monolithic R4, one fixed u |\n|---|---|---|---|---|---|')
    for row in e3['quiet']:
        mo = [r for r in e3['mono_orig'] if r['H'] == row['H']]
        mo = ('%s %.1f s' % (mo[0]['status'], mo[0]['time'])) if mo else 'not run here (timed out at 600 s in runs 1-2, parallel pool)'
        L.append('| %d | %s %.2f s (%d paths) | %s | %.2f s (%s) | %.3f s | %.3f s |' % (
            row['H'], row['mono']['R4']['status'], row['mono']['R4']['time'], row['mono']['R4']['paths'], mo, row['step2']['total'],
            'certified' if row['step2']['certified'] else 'not certified: reach ' + row['step2']['reach'], row['planner']['R4']['time'], row['mono_fixed_u']['mean_time']))
    L.append('\nWrong revisions, u free (monolithic verdict and time; planner check against G1):')
    for row in e3['quiet']:
        L.append('- H=%d: ' % row['H'] + '; '.join('%s monolithic %s %.3f s, planner %s %.4f s' % (k, row['mono'][k]['status'], row['mono'][k]['time'],
                 row['planner'][k]['status'], row['planner'][k]['time']) for k in ('R1', 'R2', 'R3')))
    L.append('\nThe original atom order (fence tick by tick from tick 0, then the goal as one conjunction) is an artefact of the first encoding: on the same paths it times out where the fair order (fence as one disjunction, goal last tick first) finishes in seconds. Only the fair order is used for the cost model.')
    if e3['completeness_loss']:
        L.append('\n**Completeness loss of the delegated route at H=%s.** The monolithic check proves R4 composed with M2 correct, while step 2 cannot certify the reach part of T at that horizon (some mission in V, two legs up to 100 m, is not finished), so G1 is empty and delegation rejects a correct system. The planner R4 only emits missions short enough to finish; the controller certification quantifies over every mission in V.' % ', '.join(str(h) for h in e3['completeness_loss']))
    for c in e3['costs']:
        L.append('\nCost model at H=%d (measured): c_M=%.2f s (R4 accepted), c_M^rej = %s, c_2=%.2f s, c_1=%.3f s. Break-even in accepted planner checks sharing one certification: n > c_2/(c_M-c_1) = %.2f, so delegation is cheaper from n=%s. Sequence R1,R2,R3,R4: monolithic %.2f s, delegated %.2f s (c_2 plus four planner checks).%s' % (
            c['H'], c['c_M'], ', '.join('%s %.3f s' % kv for kv in c['c_M_rej'].items()), c['c_2'], c['c_1'], c['break_even_n'], c['n_star'],
            c['seq_mono'], c['seq_deleg'], ' **For this one sequence delegation is slower.**' if c['seq_deleg'] > c['seq_mono'] else ''))
    c = e3.get('cost')
    if c:
        mf = [r for r in e3['quiet'] if r['H'] == c['H']][0]['mono_fixed_u']['mean_time']
        L.append('\n**For one fixed input delegation is slower**: at H=%d one fixed-input monolithic check takes %.3f s, against %.2f s for step 2 plus one planner check.' % (c['H'], mf, c['c_2'] + c['c_1']))
    e5 = R['E5']
    L.append('\n## E5 two discharge means\n\nPlanner R4: Z3 %s in %.3f s; grid enumeration (step %.1f m, s in %s): %d inputs, %d failures, %.1f s.' % (
        e5['planner_z3']['status'], e5['planner_z3']['time'], e5['planner_grid']['step'], e5['planner_grid']['s_values'], e5['planner_grid']['n'], e5['planner_grid']['fail'], e5['planner_grid']['time']))
    cs = e5['controller_sampling']
    L.append('Controller: BMC certified rho_j*=%.2f; concrete sampling of %d runs over H=%d ticks: max inf-deviation %.4f m (a lower bound on the true supremum), %.1f%% of runs leave the polyline, reach failures %d, %.1f s.'
             % (R['E2']['rho_star'], cs['n'], cs['H'], cs['max_dev'], 100 * cs['frac_off_polyline'], cs['reach_fail'], cs['time']))
    e4 = R['E4']
    L.append('\n## E4 Section 6 reproduction\n\nMissions: %s. Lowest tube point for w1=(0,-49): %s. Bad formula mismatches %d of %d samples; random search found %d missions for %d Bad inputs. Validation-instance Bad points: %d of %d sampled inputs.'
             % (e4['missions'], e4['tube_low_point'], e4['bad_formula_mismatches'], e4['bad_samples'], e4['bad_random_search']['found'],
                e4['bad_random_search']['inputs'], e4['validation_bad']['bad'], e4['validation_bad']['n']))
    with open(os.path.join(OUT, 'results.md' if not quick else 'results-quick.md'), 'w') as f:
        f.write('\n'.join(L) + '\n')


if __name__ == '__main__':
    sys.exit(main())
