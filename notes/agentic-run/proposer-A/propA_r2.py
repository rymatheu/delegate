"""Proposer A, round 2: tightest delegates read off the controller code (scripts/vcore.py, controller).

Tube shape: not a tube around both legs, but a per-coordinate hull box. Before handover the target is exactly on
leg 1 (b = 0); a rejected mission holds the target at p0; after the blend-out it is exactly on leg 2. The only
off-polyline target is the one blend tick, q = (point of leg 2) - c*d1 with c*|d1|_inf < R/2 = 1 and c in [0, 1]:
the offset points back along leg 1, so it can leave the hull of {p0, w1, w2} only beyond w2's coordinate, by < 1.
Hence every coordinate obeys  min(p0, w1, w2 - 1) <= y_t <= max(p0, w1, w2 + 1), for every w, p0, dts (round 2 states it only under
the guards P, so the checker can prune held-tick paths). Reach: b reaches 1 exactly (min(.,1)) and a reaches 1 two ticks after handover, so y_t == w2 exactly
(eta = 0) within H = 8 ticks when no tick is held (dt inside the clamp range).
Margins: |w2|_inf <= s - 1, |w1|_inf <= s (no margin), |h|_inf <= s - delta (no tube margin), |w2 - g| <= eps.
"""
import os, sys
sys.path.insert(0, '/Users/ryan/Research/delegate/scripts/agentic')
from proposal import (And, Or, Not, Ite, Box, Diamond, Min, Max, inf_le, inf_ge, dist_sq, sub, Q, vc_op, flat_u)

NAME = 'proposer A: hull box, offset 1 on w2 only, exact reach'
OFF = 1                      # R/2: blend offset bound (strict in the code, closed here)
EPS, DELTA = 3, 1
LMIN, LMAX, BOX = 5, 100, 100
DTMIN, DTMAX = Q(1, 2), Q(3, 2)
PLANNER_MARGIN = 1
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
               inf_le(h, s - DELTA), inf_le(w1, s), inf_le(w2, s - OFF),
               dist_sq(w2, g) <= EPS * EPS)
    return And(A2(w), Or(Not(A1(u)), core))


def P(w, e):
    p0, dts = e
    d1 = sub(w.w1, p0)
    return And(inf_ge(d1, LMIN), inf_le(d1, LMAX), inf_le(p0, BOX), Box(dts, lambda d: And(DTMIN <= d, d <= DTMAX)))


def G2(w, e, y):
    p0, dts = e
    w1, w2 = w
    def hull(yt):
        return And(*[And(Min(p0[k], w1[k], w2[k] - OFF) <= yt[k], yt[k] <= Max(p0[k], w1[k], w2[k] + OFF)) for k in range(2)])
    reach = Diamond(y, lambda yt: And(yt[0] == w2[0], yt[1] == w2[1]))
    return Or(Not(P(w, e)), And(Box(y, hull), reach))     # round 2: guard outermost so C2 can restrict to P


def witness(u):
    """The deployed planner revision R4 itself (margin 1) is the witness."""
    from vcore import planner
    f = planner(4, flat_u(u), vc_op(u), PLANNER_MARGIN)
    return ((f[0], f[1]), (f[2], f[3]))
