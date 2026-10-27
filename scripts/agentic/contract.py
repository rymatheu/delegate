"""Top-level contract (A, G) of the validation instance, in the proposal vocabulary.

The constants and the planner-input part of A are imported from scripts/vcore.py (TOP, A1, le_inf); the formulas
are those of scripts/validate.py (A_f, and fence_viol / d2 / EPS in mono_check). tests/test_equiv.py proves with
Z3 that A below equals validate.A_f and that G below equals the negation of validate's violation formula.
    A(u, e)    := 25 <= s <= 50, |h|_inf <= s - 3, |g|_inf <= s + 1/2, |p0 - h|_inf <= delta = 1,
                  Box over dts: 9/10 <= dt <= 11/10
    G(u, e, y) := Box over y: |y_t|_inf <= s (inside the fence F_s = [-s, s]^2),
                  Diamond over y: |y_t - g|^2 <= eps^2 with eps = 3 (Euclidean)
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from vcore import TOP, A1 as _A1_vc, le_inf, fr_exact
from proposal import And, Box, Diamond, inf_le, dist_sq, sub, vc_op, flat_u

DELTA = TOP['delta']
EPS = TOP['eps']
DTLO, DTHI = fr_exact(TOP['dtlo']), fr_exact(TOP['dthi'])


def A(u, e):
    p0, dts = e
    op = vc_op(u, p0)
    return And(_A1_vc(flat_u(u), op), le_inf(sub(p0, u.h), DELTA, op),
               Box(dts, lambda d: And(DTLO <= d, d <= DTHI)))


def G(u, e, y):
    s, h, g = u
    return And(Box(y, lambda yt: inf_le(yt, s)), Diamond(y, lambda yt: dist_sq(yt, g) <= EPS * EPS))
