"""Deliberately wrong proposal (phase 2, C2): the controller tube in G2 is 0.90 m, below what the controller code
meets (the corner blend moves the target up to just under R/2 = 1 m off the polyline). Phase 1 passes (a thinner
tube only strengthens G2); C2 must find a run of M2 that leaves the 0.90 m tube."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from example_proposal import *
from proposal import And, Or, Not, Box, Diamond, Q, dist_sq, near_segment_inf

NAME = 'wrong: controller tube 0.90 m (violates C2)'
RHO2 = Q(9, 10)


def G2(w, e, y):
    p0, dts = e
    w1, w2 = w
    tube = Box(y, lambda yt: Or(near_segment_inf(yt, p0, w1, RHO2), near_segment_inf(yt, w1, w2, RHO2)))
    reach = Diamond(y, lambda yt: dist_sq(yt, w2) <= ETA * ETA)
    return Or(Not(P(w, e)), And(tube, reach))
