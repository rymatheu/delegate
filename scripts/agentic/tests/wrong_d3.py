"""Deliberately wrong proposal (D3): the waypoint margin in G1 is 0.5 m, smaller than the tube radius rho = 1 m of
G2, so a target in the tube around a waypoint 0.5 m inside the fence can be 0.5 m outside it."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from example_proposal import *
from proposal import And, Or, Not, Q, inf_le, inf_ge, dist_sq, sub

NAME = 'wrong: waypoint margin 0.5 < rho = 1 (violates D3)'
MARGIN = Q(1, 2)


def G1(u, w):
    s, h, g = u
    w1, w2 = w
    L = sub(w1, h)
    core = And(inf_ge(L, LMIN + DELTA), inf_le(L, LMAX - DELTA), inf_le(h, s - RHO - DELTA),
               inf_le(w1, s - MARGIN), inf_le(w2, s - MARGIN), dist_sq(w2, g) <= (EPS - ETA) * (EPS - ETA))
    return And(A2(w), Or(Not(A1(u)), core))

