# Worked instance of the write-up: s=50, rho=2, delta=1, legs in [5,100], eps=3, eta=0.5.
import numpy as np
rng = np.random.default_rng(7)
s, rho, delta, lmin, lmax, eps, eta = 50.0, 2.0, 1.0, 5.0, 100.0, 3.0, 0.5
inf = lambda p: np.max(np.abs(p)); nrm = np.linalg.norm
V = lambda w1, w2: lmin <= nrm(w2-w1) <= lmax
def G1(h, g, w1, w2):
    return (V(w1, w2) and lmin+delta <= nrm(w1-h) <= lmax-delta and inf(h) <= s-rho-delta
            and inf(w1) <= s-rho and inf(w2) <= s-rho and nrm(w2-g) <= eps-eta)
def viol(h, g, w1, w2):
    for t in np.linspace(0, 2*np.pi, 721):
        d = np.array([np.cos(t), np.sin(t)])
        for p0 in (h+delta*d, h-delta*d):
            if not (lmin <= nrm(w1-p0) <= lmax): return 'P not given by A'
            for y in (p0+rho*d, w1+rho*d, w2+rho*d):
                if inf(y) > s+1e-12: return 'fence at %s' % np.round(y, 2)
        if nrm(w2+eta*d-g) > eps+1e-12: return 'goal'
    return None
h, g = np.array([-40., -40.]), np.array([40., 40.])
for w1, w2 in [((-30, 30), (40, 40)), ((0, -49), (40, 40)), ((-38, -37), (40, 40)), ((-30, 30), (44, 40))]:
    w1, w2 = np.array(w1, float), np.array(w2, float)
    print(w1, w2, 'V', V(w1, w2), 'G1', G1(h, g, w1, w2), 'counterexample:', viol(h, g, w1, w2))
# Bad at s=50 predicted: |h|_inf > 47 or dist(g, [-48,48]^2) > 2.5
def bad_pred(h, g):
    q = np.clip(g, -48, 48); return inf(h) > 47 or nrm(g-q) > 2.5
def witness(h, g):
    if inf(h) > 47: return None
    q = np.clip(g, -48, 48)
    if nrm(g-q) > 2.5: return None
    w2 = q
    if nrm(h-w2) >= 12: w1 = (h+w2)/2
    else: w1 = h*(1-20/nrm(h)) if nrm(h) >= 20 else h + np.array([20., 0.]) * (-1 if h[0] > 0 else 1)
    return (w1, w2) if G1(h, g, w1, w2) else 'FAIL'
mism = 0
for k in range(200000):
    h = rng.uniform(-50, 50, 2); g = rng.uniform(-53, 53, 2)
    wt = witness(h, g)
    if wt == 'FAIL' or (wt is None) != bad_pred(h, g): mism += 1
print('Bad formula vs constructed witnesses, mismatches:', mism)
# and: when Bad predicted, random search must not find a mission
found = 0
for k in range(300):
    h = rng.uniform(-50, 50, 2); g = rng.uniform(-53, 53, 2)
    if not bad_pred(h, g): continue
    for j in range(3000):
        w1 = rng.uniform(-48, 48, 2); w2 = np.clip(g, -48, 48) + rng.uniform(-2.5, 2.5, 2)
        if G1(h, g, w1, w2): found += 1; break
print('Bad inputs where a mission was nevertheless found (must be 0):', found)
