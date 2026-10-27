# Sharper maximality check: missions in V whose hand G1 fails in exactly one conjunct, by a margin
# below 0.5 m (coordinates on a 0.1 m grid). Z3 should still find a counterexample (H=1, complete).
import sys, time
src = open(sys.argv[1]).read().split('sv = Solver()')[0].replace('H = 2', 'H = 1')
exec(src)
import numpy as np
from fractions import Fraction as F
rng = np.random.default_rng(13)
n = np.linalg.norm; inf = lambda z: np.max(np.abs(z))
def margins(S, hh, gg, a, b):   # positive = satisfied, negative = violated (in metres)
    return {'leg1min': n(a-hh)-6, 'leg1max': 99-n(a-hh), 'home': S-3-inf(hh), 'w1': S-2-inf(a),
            'w2': S-2-inf(b), 'goal': 2.5-n(b-gg)}
cases = []
while len(cases) < 16:
    S = 50; hh = np.round(rng.uniform(-48, 48, 2), 1); gg = np.round(rng.uniform(-49, 49, 2), 1)
    a = np.round(rng.uniform(-49, 49, 2), 1); b = np.round(gg + rng.uniform(-3, 3, 2), 1)
    if not (5 <= n(b-a) <= 100): continue
    m = margins(S, hh, gg, a, b); bad = [k for k, v in m.items() if v < 0]
    if len(bad) == 1 and bad[0] in ('leg1min', 'w1', 'home', 'w2') and m[bad[0]] > -0.5: cases.append((S, hh, gg, a, b, bad[0], round(m[bad[0]], 3)))
res = {}; t0 = time.time()
q = lambda x: Q(int(round(x*10)), 10)
for S, hh, gg, a, b, which, mg in cases:
    sv = Solver(); sv.set('timeout', 60000)
    sv.add(s == S, h[0] == q(hh[0]), h[1] == q(hh[1]), g[0] == q(gg[0]), g[1] == q(gg[1]),
           w1[0] == q(a[0]), w1[1] == q(a[1]), w2[0] == q(b[0]), w2[1] == q(b[1]), A, V, G2, Not(G))
    r = str(sv.check()); res[(which, r)] = res.get((which, r), 0) + 1
    print(which, mg, r, flush=True)
print('edge cases:', len(cases), 'verdicts by failing conjunct:', res, 'seconds:', round(time.time()-t0))
