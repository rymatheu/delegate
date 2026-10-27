"""Sanity check of the alternative monolithic verdicts: concrete runs of R4 composed with M2 on random u, p0, dt in A,
including inputs biased to edges; report any violation of G at horizon H."""
import sys, random, math
sys.path.insert(0, '/Users/ryan/Research/delegate/scripts')
from vcore import controller, planner, Num
H = int(sys.argv[1]); n = int(sys.argv[2]); rng = random.Random(7)
viol = 0; ex = None
for i in range(n):
    s = rng.uniform(25, 50) if i % 4 else rng.choice([25, 50])
    hm, gm = s - 3, s + 0.5
    e = lambda m: (rng.choice([-1, 1]) * rng.uniform(m - 1, m)) if rng.random() < 0.5 else rng.uniform(-m, m)
    hx, hy = e(hm), e(hm); gx, gy = e(gm), e(gm)
    if rng.random() < 0.3: gx, gy = max(-gm, min(gm, hx + rng.uniform(-12, 12))), max(-gm, min(gm, hy + rng.uniform(-12, 12)))
    p0 = (hx + rng.uniform(-1, 1), hy + rng.uniform(-1, 1))
    dts = [rng.uniform(0.9, 1.1) for _ in range(H)]
    w = planner(4, (s, hx, hy, gx, gy), Num(), 1.04)
    ys = controller(w, p0, dts, Num())
    fence = all(abs(y[0]) <= s and abs(y[1]) <= s for y in ys)
    goal = any(math.hypot(y[0] - gx, y[1] - gy) <= 3 for y in ys)
    if not (fence and goal):
        viol += 1; ex = ex or dict(u=(s, hx, hy, gx, gy), p0=p0, fence=fence, goal=goal)
print('H=%d runs=%d violations=%d example=%s' % (H, n, viol, ex))
