"""Deliberately wrong proposal (D1): A1 asks for the goal inside the fence, |g|_inf <= s, but the top-level A admits
goals up to 0.5 m outside it (|g|_inf <= s + 0.5). Everything else is the example proposal."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from example_proposal import *          # A2, G2, P, constants, witness
import example_proposal as base
from proposal import And, Or, Not, inf_le

NAME = 'wrong: A1 excludes goals outside the fence (violates D1)'


def A1(u):
    s, h, g = u
    return And(25 <= s, s <= 50, inf_le(h, s - 3), inf_le(g, s))


def G1(u, w):
    return And(A2(w), Or(Not(A1(u)), base.G1(u, w)))
