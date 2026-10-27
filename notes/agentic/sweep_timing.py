#!/usr/bin/env python3
"""Times scripts/delegate.py's procedure (steps 1-9, including the sweep) on the speed-governor chain at H = 2,
alone in a fresh process.  Run from the directory root:  .venv/bin/python notes/agentic/sweep_timing.py
(about 7 minutes on the author's machine on 19 Oct 2026; inside the one command scripts/delegate.py the same
instance takes about 71 s, because Z3's term order depends on the symbols created by earlier instances).
scripts/delegate.py is imported, not modified."""
import sys, time, io, contextlib, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "scripts"))
import delegate as D
from fractions import Fraction
from z3 import And, Implies, get_version_string
V, Alw, Ev = D.V, D.Alw, D.Ev
H = 2
SG = D.Arch({"Perception": (["o"], ["e"]), "Controller": (["e"], ["u"]), "Actuator": (["u"], ["v"])}, env=["o"], H=H)
o_ = lambda t: V("o", t); v_ = lambda t: V("v", t)
AP = Alw(0, H, lambda t: And(o_(t) >= 0, o_(t) <= 5))(0)
GP = And(Alw(0, H, lambda t: And(v_(t) >= 0, v_(t) <= 2))(0),
         Alw(0, H - 1, lambda t: Implies(o_(t) <= 1, Ev(0, 1, lambda s: v_(s) <= Fraction(1, 4))(t)))(0),
         Alw(0, H - 1, lambda t: Implies(o_(t) >= 3, Ev(0, 1, lambda s: v_(s) >= 1)(t)))(0))
print(f"z3 version {get_version_string()}")
t0 = time.time(); buf = io.StringIO()
with contextlib.redirect_stdout(buf): r = D.delegate(SG, AP, GP, "speed governor, H = 2")
print(f"delegate() on the speed governor, H = 2, fresh process: {time.time() - t0:.1f} s; "
      f"all verdicts true: {r is not None and all(r['verdicts'].values())}")
