# Maximality on the leg-length conjunct: w1 at distance in (5.5, 6) from h, everything else satisfied.
import sys, time
src = open(sys.argv[1]).read().split('sv = Solver()')[0].replace('H = 2', 'H = 1')
exec(src)
import numpy as np
rng = np.random.default_rng(21)
q = lambda x: Q(int(round(x*10)), 10)
res = {}; t0 = time.time(); k = 0
while k < 10:
    hh = np.round(rng.uniform(-40, 40, 2), 1); ang = rng.uniform(0, 2*np.pi); r = rng.uniform(5.5, 5.95)
    a = np.round(hh + r*np.array([np.cos(ang), np.sin(ang)]), 1)
    if not (5.5 < np.linalg.norm(a-hh) < 6): continue
    b = np.round(rng.uniform(-45, 45, 2), 1); gg = b
    if not (5 <= np.linalg.norm(b-a) <= 100) or np.max(np.abs(a)) > 48: continue
    sv = Solver(); sv.set('timeout', 60000)
    sv.add(s == 50, h[0] == q(hh[0]), h[1] == q(hh[1]), g[0] == q(gg[0]), g[1] == q(gg[1]),
           w1[0] == q(a[0]), w1[1] == q(a[1]), w2[0] == q(b[0]), w2[1] == q(b[1]), A, V, G2, Not(G))
    rr = str(sv.check()); res[rr] = res.get(rr, 0) + 1; k += 1
    print(round(float(np.linalg.norm(a-hh)), 3), rr, flush=True)
print('leg-length edge cases:', k, 'verdicts:', res, 'seconds:', round(time.time()-t0))
