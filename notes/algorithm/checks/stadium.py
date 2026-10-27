import numpy as np
rng = np.random.default_rng(5); bad = 0
def segdist(z, a, b):
    t = np.clip(np.dot(z-a, b-a)/np.dot(b-a, b-a), 0, 1); return np.linalg.norm(z-a-t*(b-a))
def poly(z, a, b, r):
    d = b-a; q = z-a; cr = q[0]*d[1]-q[1]*d[0]
    return (q@q <= r*r) or ((z-b)@(z-b) <= r*r) or (0 <= q@d <= d@d and cr*cr <= r*r*(d@d))
for _ in range(200000):
    a, b, z = rng.uniform(-5, 5, (3, 2)); r = rng.uniform(0.1, 3)
    if abs(segdist(z, a, b) - r) < 1e-9: continue
    bad += (segdist(z, a, b) <= r) != poly(z, a, b, r)
print('stadium polynomial vs distance, disagreements:', bad)
