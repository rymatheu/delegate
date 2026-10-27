"""Example proposal: the delegates the algorithm itself computes for the validation instance (scripts/validate.py).

    A1 = the planner-input part of A (A with e projected out)
    G1 = the closed form of vcore.G1 with rho = 1.00: V and (not A1 or [(ii) and (iii) and (iv)])
    A2 = V   (the mission guards of the controller code)
    G2 = not P or T_rho with rho = 1.00, eta = 0.5   (P: start and tick guards; T: tube and reach)

Check it with   .venv/bin/python scripts/agentic/check.py scripts/agentic/example_proposal.py --phase2
tests/test_equiv.py proves with Z3 that each set below equals its counterpart in scripts/vcore.py / validate.py.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from proposal import (And, Or, Not, Ite, Box, Diamond, Min, Max, inf_le, inf_ge, inf_lt, dist_sq, sub, mid,
                      near_segment_inf, Q)

NAME = 'algorithm delegates, rho = 1.00'
RHO = 1                     # tube radius certified by step 2 at H = 8 (rho_j* of validate.py)
ETA = Q(1, 2)               # reach radius of T
EPS, DELTA = 3, 1           # from the top-level contract
LMIN, LMAX, BOX = 5, 100, 100           # controller guards (vcore.CTRL: lmin, lmax, B)
DTMIN, DTMAX = Q(1, 2), Q(3, 2)         # controller dt clamp (vcore.CTRL: dtmin, dtmax)

PLANNER_MARGIN = RHO        # inward margin m the planner revisions R1..R4 use (vcore.planner argument m)
PLANNER_REVISION = 4        # the revision intended for deployment; phase 2 requires it to pass C1


def A1(u):
    s, h, g = u
    return And(25 <= s, s <= 50, inf_le(h, s - 3), inf_le(g, s + Q(1, 2)))


def A2(w):                  # V: leg 2 length in [l_min, l_max], waypoints inside the upload box
    w1, w2 = w
    d2 = sub(w2, w1)
    return And(inf_ge(d2, LMIN), inf_le(d2, LMAX), inf_le(w1, BOX), inf_le(w2, BOX))


def G1(u, w):
    s, h, g = u
    w1, w2 = w
    L = sub(w1, h)
    core = And(inf_ge(L, LMIN + DELTA), inf_le(L, LMAX - DELTA),         # (ii) leg 1 fine from every start
               inf_le(h, s - RHO - DELTA), inf_le(w1, s - RHO), inf_le(w2, s - RHO),   # (iii) tube in fence
               dist_sq(w2, g) <= (EPS - ETA) * (EPS - ETA))                # (iv) eta-disc at w2 in eps-disc at g
    return And(A2(w), Or(Not(A1(u)), core))


def P(w, e):                # the environment the controller relies on
    p0, dts = e
    d1 = sub(w.w1, p0)
    return And(inf_ge(d1, LMIN), inf_le(d1, LMAX), inf_le(p0, BOX), Box(dts, lambda d: And(DTMIN <= d, d <= DTMAX)))


def G2(w, e, y):
    p0, dts = e
    w1, w2 = w
    tube = Box(y, lambda yt: Or(near_segment_inf(yt, p0, w1, RHO), near_segment_inf(yt, w1, w2, RHO)))
    reach = Diamond(y, lambda yt: dist_sq(yt, w2) <= ETA * ETA)
    return Or(Not(P(w, e)), And(tube, reach))


def witness(u):
    """A mission for every u in A1 (route (b) of R): the construction of planner revision R4 with margin 1."""
    s, h, g = u
    c = s - RHO
    w2 = (Min(Max(g[0], -c), c), Min(Max(g[1], -c), c))       # goal clipped into F_{s-rho}
    near = inf_lt(sub(w2, h), 2 * (LMIN + DELTA))               # goal close to home: leg 1 would be too short
    w1 = Ite(near, (h[0] + Ite(h[0] < 0, 20, -20), h[1]), mid(h, w2))
    return (w1, w2)
