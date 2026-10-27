# Instance-level soundness by Z3: fix (u,w) with hand G1 true, ask for (p0, dt, y) with A, A2, G2 and not G (H=1).
import random
from z3 import *
exec(open('z3check.py').read().split('sv = Solver()')[0].replace('H = 2', 'H = 1'))
import numpy as np
rng = np.random.default_rng(3)
def G1num(S, hh, gg, a, b):
    n = np.linalg.norm; inf = lambda z: np.max(np.abs(z))
    return (5 <= n(b-a) <= 100 and 6 <= n(a-hh) <= 99 and inf(hh) <= S-3 and inf(a) <= S-2 and inf(b) <= S-2 and n(b-gg) <= 2.5)
cases = [(50, (-40, -40), (40, 40), (-30, 30), (40, 40))]
while len(cases) < 25:
    S = 50; hh = rng.integers(-47, 48, 2); gg = rng.integers(-48, 49, 2); a = rng.integers(-48, 49, 2); b = gg + rng.integers(-1, 2, 2)
    if G1num(S, hh, gg, a, b): cases.append((S, tuple(hh), tuple(gg), tuple(a), tuple(b)))
res = {}
for S, hh, gg, a, b in cases:
    sv = Solver(); sv.set('timeout', 60000)
    sv.add(s == S, h[0] == int(hh[0]), h[1] == int(hh[1]), g[0] == int(gg[0]), g[1] == int(gg[1]),
           w1[0] == int(a[0]), w1[1] == int(a[1]), w2[0] == int(b[0]), w2[1] == int(b[1]), hand, A, V, G2, Not(G))
    r = str(sv.check()); res[r] = res.get(r, 0) + 1
print('instances with hand G1 true:', len(cases), 'Z3 verdicts on counterexample search:', res)
