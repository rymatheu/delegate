"""Proposer B: coarse controller guarantee (axis-aligned bounding box of p0, w1, w2 grown by R_BOX, instead of a
tube around the two segments), A2 = the controller's mission guards, G1 with an inward fence margin RHO."""
import os, sys
sys.path.insert(0, '/Users/ryan/Research/delegate/scripts/agentic')
from proposal import (And, Or, Not, Ite, Box, Diamond, Min, Max, inf_le, inf_ge, inf_lt, dist_sq, sub, mid, Q)

RHO = Q(int(os.environ.get('B_RHO_NUM', 5)), int(os.environ.get('B_RHO_DEN', 4)))   # G1 inward fence margin
R_BOX = 1                   # growth of the bounding box in G2 (controller blend-out stays within R/2 = 1)
ETA = Q(1, 2)               # reach radius in G2
EPS, DELTA = 3, 1
LMIN, LMAX, BOX = 5, 100, 100
DTMIN, DTMAX = Q(1, 2), Q(3, 2)
NAME = 'proposer B: bbox G2 (r=%s), rho=%s' % (R_BOX, RHO)
PLANNER_MARGIN = RHO
PLANNER_REVISION = 4


def A1(u):
    s, h, g = u
    return And(25 <= s, s <= 50, inf_le(h, s - 3), inf_le(g, s + Q(1, 2)))


def A2(w):
    w1, w2 = w
    d2 = sub(w2, w1)
    return And(inf_ge(d2, LMIN), inf_le(d2, LMAX), inf_le(w1, BOX), inf_le(w2, BOX))


def G1(u, w):
    s, h, g = u
    w1, w2 = w
    L = sub(w1, h)
    core = And(inf_ge(L, LMIN + DELTA), inf_le(L, LMAX - DELTA),
               inf_le(h, s - RHO - DELTA), inf_le(w1, s - RHO), inf_le(w2, s - RHO),
               dist_sq(w2, g) <= (EPS - ETA) * (EPS - ETA))
    return And(A2(w), Or(Not(A1(u)), core))


def P(w, e):
    p0, dts = e
    d1 = sub(w.w1, p0)
    return And(inf_ge(d1, LMIN), inf_le(d1, LMAX), inf_le(p0, BOX), Box(dts, lambda d: And(DTMIN <= d, d <= DTMAX)))


def G2(w, e, y):
    p0, dts = e
    w1, w2 = w
    lo = [Min(p0[i], w1[i], w2[i]) - R_BOX for i in (0, 1)]
    hi = [Max(p0[i], w1[i], w2[i]) + R_BOX for i in (0, 1)]
    hull = Box(y, lambda yt: And(lo[0] <= yt[0], yt[0] <= hi[0], lo[1] <= yt[1], yt[1] <= hi[1]))
    reach = Diamond(y, lambda yt: dist_sq(yt, w2) <= ETA * ETA)
    return Or(Not(P(w, e)), And(hull, reach))


def witness(u):
    s, h, g = u
    c = s - RHO
    w2 = (Min(Max(g[0], -c), c), Min(Max(g[1], -c), c))
    near = inf_lt(sub(w2, h), 2 * (LMIN + DELTA))
    w1 = Ite(near, (h[0] + Ite(h[0] < 0, 20, -20), h[1]), mid(h, w2))
    return (w1, w2)
