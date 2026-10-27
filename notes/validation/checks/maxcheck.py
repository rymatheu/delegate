# Instance-level maximality of the hand G1 (worked example): for random missions in V with hand G1 FALSE
# (s=50), Z3 should find (p0, dt, y) with A, A2, G2 and not G. H=1 is complete by the pointwise lemma (m=1).
import sys, random, time
src = open(sys.argv[1]).read().split('sv = Solver()')[0].replace('H = 2', 'H = 1')
exec(src)
import numpy as np
rng = np.random.default_rng(5)
def G1num(S, hh, gg, a, b):
    n = np.linalg.norm; inf = lambda z: np.max(np.abs(z))
    return (5 <= n(b-a) <= 100 and 6 <= n(a-hh) <= 99 and inf(hh) <= S-3 and inf(a) <= S-2 and inf(b) <= S-2 and n(b-gg) <= 2.5)
cases = []
while len(cases) < 30:
    S = 50; hh = rng.integers(-49, 50, 2); gg = rng.integers(-49, 50, 2)
    a = rng.integers(-50, 51, 2); b = gg + rng.integers(-4, 5, 2)
    if 5 <= np.linalg.norm(b-a) <= 100 and not G1num(S, hh, gg, a, b): cases.append((S, hh, gg, a, b))
res = {}; t0 = time.time()
for S, hh, gg, a, b in cases:
    sv = Solver(); sv.set('timeout', 60000)
    sv.add(s == S, h[0] == int(hh[0]), h[1] == int(hh[1]), g[0] == int(gg[0]), g[1] == int(gg[1]),
           w1[0] == int(a[0]), w1[1] == int(a[1]), w2[0] == int(b[0]), w2[1] == int(b[1]), A, V, G2, Not(G))
    r = str(sv.check()); res[r] = res.get(r, 0) + 1
    print(tuple(hh), tuple(gg), tuple(a), tuple(b), r, flush=True)
print('missions in V with hand G1 false:', len(cases), 'verdicts:', res, 'seconds:', round(time.time()-t0))
