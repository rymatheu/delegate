"""Proposer C, round 1: corner-handover shape read off scripts/vcore.py controller().

Targets of M2 (when every guard passes and no tick is held): y = p0 + a d1 + b d2.
  before handover: b = 0, a in [0,1]          -> on leg 1, inside the box spanned by p0 and w1
  blend tick:      a = 1 - k, k = (1-a_h)/2 with (1-a_h)|d1|_inf < R = 2, so 0 <= k <= 1/2 and |k d1|_inf < 1
                   -> y = (w1 + b d2) - k d1: leg 2 shifted towards p0 (inner side of the corner) by < 1
  after:           a = 1, b in [0,1]          -> on leg 2; b reaches 1 exactly, so y = w2 exactly at some tick
G2: per tick, y in the leg-1 box, or in the leg-2 box grown only on the sides that face p0, by
    min(1, max(0, p0 - w1 per axis)/2) (half of the leg-1 component, capped at R/2 = 1); reach is exact (y = w2).
G1 margins follow: w1 needs margin 0 (the shift at w1 goes back along leg 1), w2 needs margin 1, goal within eps.
"""
import os, sys
sys.path.insert(0, '/Users/ryan/Research/delegate/scripts/agentic')
from proposal import (And, Or, Not, Ite, Box, Diamond, Min, Max, inf_le, inf_ge, inf_lt, dist_sq, sub, mid, Q)

NAME = 'proposer C: corner-handover boxes, exact reach'
EPS, DELTA = 3, 1
LMIN, LMAX, BOX = 5, 100, 100
DTMIN, DTMAX = Q(1, 2), Q(3, 2)
W2M = 1                      # margin of w2 (R/2 corner shift)
PLANNER_MARGIN = W2M
PLANNER_REVISION = 4


def A1(u):
    s, h, g = u
    return And(25 <= s, s <= 50, inf_le(h, s - 3), inf_le(g, s + Q(1, 2)))


def A2(w):                   # exactly the mission-only guards of the code (ok in vcore.controller)
    w1, w2 = w
    d2 = sub(w2, w1)
    return And(inf_ge(d2, LMIN), inf_le(d2, LMAX), inf_le(w1, BOX), inf_le(w2, BOX))


def G1(u, w):
    s, h, g = u
    w1, w2 = w
    L = sub(w1, h)
    core = And(inf_ge(L, LMIN + DELTA), inf_le(L, LMAX - DELTA),
               inf_le(w1, s), inf_le(w2, s - W2M),
               dist_sq(w2, g) <= EPS * EPS)
    return And(A2(w), Or(Not(A1(u)), core))


def P(w, e):                 # the environment-dependent guards of the code
    p0, dts = e
    d1 = sub(w.w1, p0)
    return And(inf_ge(d1, LMIN), inf_le(d1, LMAX), inf_le(p0, BOX), Box(dts, lambda d: And(DTMIN <= d, d <= DTMAX)))


def _shift(p, q):            # inner-side growth on the side where p exceeds q: min(1, max(0, p - q)/2)
    return Min(1, Max(0, p - q) / 2)


def G2(w, e, y):
    p0, dts = e
    w1, w2 = w
    def leg1(t):
        return And(Min(p0[0], w1[0]) <= t[0], t[0] <= Max(p0[0], w1[0]),
                   Min(p0[1], w1[1]) <= t[1], t[1] <= Max(p0[1], w1[1]))
    def corner(t):
        return And(Min(w1[0], w2[0]) - _shift(w1[0], p0[0]) <= t[0], t[0] <= Max(w1[0], w2[0]) + _shift(p0[0], w1[0]),
                   Min(w1[1], w2[1]) - _shift(w1[1], p0[1]) <= t[1], t[1] <= Max(w1[1], w2[1]) + _shift(p0[1], w1[1]))
    tube = Box(y, lambda t: Or(leg1(t), corner(t)))
    reach = Diamond(y, lambda t: And(t[0] == w2[0], t[1] == w2[1]))
    return Or(Not(P(w, e)), And(tube, reach))


def witness(u):
    s, h, g = u
    c = s - W2M
    w2 = (Min(Max(g[0], -c), c), Min(Max(g[1], -c), c))
    near = inf_lt(sub(w2, h), 2 * (LMIN + DELTA))
    w1 = Ite(near, (h[0] + Ite(h[0] < 0, 20, -20), h[1]), mid(h, w2))
    return (w1, w2)
