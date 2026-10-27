import numpy as np, sys
sys.path.insert(0, '.')
exec(open('example2.py').read().split('h, g = np.array')[0])
rng = np.random.default_rng(11); bs = bm = n = 0
for k in range(60000):
    h = rng.uniform(-50, 50, 2); g = rng.uniform(-50, 50, 2)
    w1 = rng.uniform(-50, 50, 2); w2 = g + rng.uniform(-4, 4, 2) if rng.uniform() < .7 else rng.uniform(-50, 50, 2)
    if not V(w1, w2): continue
    n += 1; r = viol(h, g, w1, w2); ok = G1(h, g, w1, w2)
    bs += bool(ok and r); bm += bool((not ok) and (r is None))
print('missions', n, 'G1 true but violated', bs, 'G1 false but no violation', bm)
