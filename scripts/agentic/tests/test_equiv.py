#!/usr/bin/env python
"""Self-tests of the checker (run: .venv/bin/python scripts/agentic/tests/test_equiv.py). Exit 0 iff all pass.

1. Fidelity: the contract and the example proposal, written in the proposal vocabulary, are equivalent (Z3) to the
   formulas of scripts/vcore.py and scripts/validate.py they restate; the example witness equals planner R4.
2. Polygon brackets used by route (a) of R: inner n-gon inside the disc, outer n-gon around it (Z3, exact).
3. Pointwise class detection: direct indexing of y is detected and forces the full horizon; the count of
   existential temporal operators on the D3 query of the example is 2 for y and 1 for dts.
"""
import os, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
AG = os.path.dirname(HERE)
sys.path.insert(0, AG); sys.path.insert(0, os.path.dirname(AG))
from fractions import Fraction
import z3
import check as C
import contract
import proposal as PR
from proposal import H, E, Ticks, Recorder, recording, flat_u, flat_w
import vcore, validate
from vcore import Sym

ex = C.load(os.path.join(AG, 'example_proposal.py'))
results = []


def valid(name, f, g, dist=None, tmo=120):
    """Prove f <=> g (both Z3 Booleans) by refuting each direction with the checker's solver."""
    t0 = time.time()
    st = []
    for q in ([f, z3.Not(g)], [g, z3.Not(f)]):
        r, m, info = C.solve(q, time.time() + tmo, dist=dist)
        st.append(r)
    ok = all(r == 'unsat' for r in st)
    results.append((name, ok, time.time() - t0, st))


u, w, p0 = C.sym_u(), C.sym_w(), C.sym_p0()
dts, y = C.sym_dts(H), C.sym_y(H + 1)
e = E(p0, dts)
S = Sym()
U5, W4, DL = list(flat_u(u)), list(flat_w(w)), list(dts._items)

valid('contract.A == validate.A_f', contract.A(u, e), validate.A_f(U5, p0, DL, S))
G_val = z3.Not(z3.Or(z3.Or(*[validate.fence_viol(yt, u.s) for yt in y._items]),
                     z3.And(*[validate.d2(yt, u.g) > validate.EPS * validate.EPS for yt in y._items])))
rec = Recorder()
with recording(rec): Gc = contract.G(u, e, y)
valid('contract.G == not(fence or goal violation) of validate.mono_check', Gc, G_val, dist=rec.dist)
valid('example A1 == vcore.A1', ex.A1(u), vcore.A1(U5, S))
valid('example A2 == vcore.Vw', ex.A2(w), vcore.Vw(W4, S))
valid('example A2 == validate.V_f', ex.A2(w), validate.V_f(W4, S))
rec = Recorder()
with recording(rec): g1 = ex.G1(u, w)
valid('example G1 == vcore.G1 (rho = 1)', g1, vcore.G1(U5, W4, z3.RealVal(1), S), dist=rec.dist)
valid('example P == validate.P_f', ex.P(w, e), validate.P_f(W4, p0, DL, S))
rec = Recorder()
with recording(rec): g2 = ex.G2(w, e, y)
G2_val = z3.Or(z3.Not(validate.P_f(W4, p0, DL, S)),
               z3.And(z3.And(*[validate.tube(yt, p0, W4, z3.RealVal(1)) for yt in y._items]),
                      z3.Or(*[validate.d2(yt, (W4[2], W4[3])) <= validate.zv(validate.ETA * validate.ETA) for yt in y._items])))
valid('example G2 == not P_f or (tube(1) and reach) of validate.py', g2, G2_val, dist=rec.dist)
wt = ex.witness(u)
wp = vcore.planner(4, U5, S, 1)
valid('example witness == vcore.planner R4 (m = 1)', z3.BoolVal(True),
      z3.And(*[a == b for a, b in zip(list(wt[0]) + list(wt[1]), wp)]))

# 2. polygon brackets
v = (z3.Real('vx'), z3.Real('vy'))
for k in (Fraction(1, 4), Fraction(25, 4), Fraction(9), Fraction(2)):
    for n in (8, 32, 128):
        for strict in (False, True):
            t0 = time.time()
            kz = z3.RealVal(k)
            inner = z3.And(*[z3.RealVal(c) * v[0] + z3.RealVal(s) * v[1] <= z3.RealVal(a) for c, s, a in C.polygon(n, kz, True, strict)])
            outer = z3.And(*[z3.RealVal(c) * v[0] + z3.RealVal(s) * v[1] <= z3.RealVal(a) for c, s, a in C.polygon(n, kz, False, strict)])
            nsq = v[0] * v[0] + v[1] * v[1]
            s1 = z3.SolverFor('QF_NRA'); s1.add(inner, (nsq >= kz) if strict else (nsq > kz))
            s2 = z3.SolverFor('QF_NRA'); s2.add(nsq <= kz, z3.Not(outer))
            ok = s1.check() == z3.unsat and s2.check() == z3.unsat
            results.append(('polygon k=%s n=%d strict=%s: inner in disc, disc in outer' % (k, n, strict), ok, time.time() - t0, []))

# 3. pointwise detection
class NonPointwise:
    A1, G1, A2 = ex.A1, ex.G1, ex.A2
    def G2(w, e, y):          # reach written as "the last target is near w2": indexes y directly
        return PR.Or(PR.Not(ex.P(w, e)), PR.And(PR.Box(y, lambda yt: PR.Or(PR.near_segment_inf(yt, e.p0, w.w1, 1),
                     PR.near_segment_inf(yt, w.w1, w.w2, 1))), PR.dist_sq(y[-1], w.w2) <= Fraction(1, 4)))
ctx = C.Ctx(NonPointwise, 60)
ny, ndt, why = C.horizon(ctx, ['A', 'G1', 'A2', 'G2', 'G'], lambda f: [z3.Not(f['G']), f['A'], f['G1'], f['A2'], f['G2']])
results.append(('direct y[-1] forces the full horizon (%s)' % '; '.join(why), ny == H + 1 and ndt == 1, 0, []))
ctx = C.Ctx(ex, 60)
B = C.build(ctx, H + 1, H, ['A', 'G1', 'A2', 'G2', 'G'])
f = B['f']
cnt = C.existential_count(z3.And(z3.Not(f['G']), f['A'], f['G1'], f['A2'], f['G2']), B['rec'].ops)
results.append(('existential operators in the example D3 query: %s' % cnt, cnt == {'y': 2, 'dts': 1}, 0, []))

bad = 0
for name, ok, t, st in results:
    print('%-4s %6.2f s  %s %s' % ('PASS' if ok else 'FAIL', t, name, '' if ok else st))
    bad += not ok
print('%d of %d self-tests pass' % (len(results) - bad, len(results)))
sys.exit(1 if bad else 0)
