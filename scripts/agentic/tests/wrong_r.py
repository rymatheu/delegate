"""Deliberately wrong proposal (R): G1 is empty. The leg-1 bounds are written with l_min and l_max swapped
(|w1 - h|_inf >= l_max + delta = 101 and <= l_min - delta = 4), so no mission meets G1 for any input. D1, D2 and D3
then hold vacuously; only the realizability check R exposes the proposal."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from example_proposal import *
from proposal import And, Or, Not, inf_le, inf_ge, dist_sq, sub

NAME = 'wrong: G1 empty (violates R)'


def G1(u, w):
    s, h, g = u
    w1, w2 = w
    L = sub(w1, h)
    core = And(inf_ge(L, LMAX + DELTA), inf_le(L, LMIN - DELTA), inf_le(h, s - RHO - DELTA),
               inf_le(w1, s - RHO), inf_le(w2, s - RHO), dist_sq(w2, g) <= (EPS - ETA) * (EPS - ETA))
    return And(A2(w), Or(Not(A1(u)), core))
