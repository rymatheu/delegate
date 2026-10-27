# Soundness of the hand G1 (D3+) for the worked example, unrolled over H=2 (3 ticks), by Z3 (nlsat).
from z3 import *
rho, delta, lmin, lmax, eps, eta = 2, 1, 5, 100, 3, Q(1, 2)
H = 1
s = Real('s'); h = [Real('hx'), Real('hy')]; g = [Real('gx'), Real('gy')]
w1 = [Real('w1x'), Real('w1y')]; w2 = [Real('w2x'), Real('w2y')]; p0 = [Real('px'), Real('py')]
dt = [Real('dt%d' % t) for t in range(H+1)]; y = [[Real('y%dx' % t), Real('y%dy' % t)] for t in range(H+1)]
sub = lambda a, b: [a[0]-b[0], a[1]-b[1]]; dot = lambda a, b: a[0]*b[0]+a[1]*b[1]
cr = lambda a, b: a[0]*b[1]-a[1]*b[0]; n2 = lambda a: dot(a, a)
inf_le = lambda z, c: And(z[0] <= c, -z[0] <= c, z[1] <= c, -z[1] <= c)
def stad(z, a, b, r):
    q, d = sub(z, a), sub(b, a)
    return Or(n2(q) <= r*r, n2(sub(z, b)) <= r*r, And(0 <= dot(q, d), dot(q, d) <= n2(d), cr(q, d)**2 <= r*r*n2(d)))
A = And(s > 0, n2(sub(p0, h)) <= delta**2, *[And(Q(24, 10000) <= d, d <= Q(26, 10000)) for d in dt])
G = And(*[inf_le(yt, s) for yt in y], Or(*[n2(sub(yt, g)) <= eps**2 for yt in y]))
V = And(lmin**2 <= n2(sub(w2, w1)), n2(sub(w2, w1)) <= lmax**2)
P = And(lmin**2 <= n2(sub(w1, p0)), n2(sub(w1, p0)) <= lmax**2, *[And(Q(1, 2000) <= d, d <= Q(1, 50)) for d in dt])
T = And(*[Or(stad(yt, p0, w1, rho), stad(yt, w1, w2, rho)) for yt in y], Or(*[n2(sub(yt, w2)) <= eta**2 for yt in y]))
G2 = Implies(P, T)
hand = And(V, Or(s <= 0, And((lmin+delta)**2 <= n2(sub(w1, h)), n2(sub(w1, h)) <= (lmax-delta)**2,
            inf_le(h, s-rho-delta), inf_le(w1, s-rho), inf_le(w2, s-rho), n2(sub(w2, g)) <= (eps-eta)**2)))
sv = Solver(); sv.set('timeout', 300000)
parts = [('fence x+ t%d' % t, y[t][0] > s) for t in range(H+1)] + [('fence x- t%d' % t, -y[t][0] > s) for t in range(H+1)] \
      + [('fence y+ t%d' % t, y[t][1] > s) for t in range(H+1)] + [('fence y- t%d' % t, -y[t][1] > s) for t in range(H+1)] \
      + [('goal', And(*[n2(sub(yt, g)) > eps**2 for yt in y]))]
for name, viol in parts:
    sv = Solver(); sv.set('timeout', 300000)
    sv.add(s == 50, hand, A, V, G2, viol)
    print('s=50, hand G1 and A and A2 and G2 and', name, ':', sv.check(), flush=True)
# instance-level maximality spot checks: the three rejected missions of the write-up have counterexamples
for W1, W2 in [((0, -49), (40, 40)), ((-30, 30), (44, 40)), ((-36, -40), (-36, 0))]:
    s2 = Solver(); s2.set('timeout', 120000)
    s2.add(s == 50, h[0] == -40, h[1] == -40, g[0] == 40, g[1] == 40, w1[0] == W1[0], w1[1] == W1[1], w2[0] == W2[0], w2[1] == W2[1])
    s2.add(A, V, G2, Not(G))
    print(W1, W2, 'counterexample exists:', s2.check())
