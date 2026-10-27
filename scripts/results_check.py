"""Verifies hand-simplified forms used in docs/results.pdf against the computed contracts."""
import sys, io, contextlib
sys.path.insert(0, "scripts")
from delegate import *
def quiet(f, *a):
    with contextlib.redirect_stdout(io.StringIO()): return f(*a)
r = V("r",0); m = V("m",0); d = V("d",0)
A = Arch({"Radio": (["r"], ["m"]), "Display": (["m"], ["d"])}, env=["r"], H=0)
R = quiet(delegate, A, absle(r,1), absle(d-r, Fraction(1,2)), "relay")
def eq(a,b): return valid(a == b)
print("relay seed:", eq(R["seed"]["Radio"], m==r), eq(R["seed"]["Display"], d==m))
AR,GR = R["sweep"]["Radio"]; AD,GD = R["sweep"]["Display"]
print("relay sweep Radio:", eq(AR, absle(r,1)), eq(GR, Implies(absle(r,1), absle(m-r, Fraction(1,2)))))
print("relay sweep Display:", eq(AD, absle(m, Fraction(3,2))),
      eq(GD, Implies(absle(m, Fraction(3,2)), And(Or(d <= -Fraction(1,2), d <= m), Or(d >= Fraction(1,2), d >= m)))))
# chain
m1=V("m1",0); m2=V("m2",0)
A3 = Arch({"C1": (["r"], ["m1"]), "C2": (["m1"], ["m2"]), "C3": (["m2"], ["d"])}, env=["r"], H=0)
R3 = quiet(delegate, A3, absle(r,1), absle(d-r, Fraction(1,2)), "chain")
print("chain seed:", eq(R3["seed"]["C1"], m1==r), eq(R3["seed"]["C2"], m2==m1), eq(R3["seed"]["C3"], d==m2))
A1,G1 = R3["sweep"]["C1"]; A2,G2 = R3["sweep"]["C2"]; A3_,G3 = R3["sweep"]["C3"]
print("chain sweep C1:", eq(A1, absle(r,1)), eq(G1, Implies(absle(r,1), absle(m1-r, Fraction(1,2)))))
print("chain sweep C2:", eq(A2, absle(m1, Fraction(3,2))),
      eq(G2, Implies(absle(m1, Fraction(3,2)), And(Or(m2 <= -Fraction(1,2), m2 <= m1), Or(m2 >= Fraction(1,2), m2 >= m1)))))
print("chain sweep C3 A:", eq(A3_, absle(m2, Fraction(3,2))))
# candidate for C3's G: on |m2|<=3/2: d = m2 if |m2| <= 1/2 ... let Z3 tell: print simplified
print("chain sweep C3 G (z3):", fmt(G3))
cand = Implies(absle(m2, Fraction(3,2)), And(Or(d <= -Fraction(1,2), d <= m2), Or(d >= Fraction(1,2), d >= m2)))
print("chain sweep C3 G == same shape as Display:", eq(G3, cand))
# disjunctive
GP4 = Or(And(Implies(r >= 0, d >= 1), Implies(r < 0, d <= -1)), absle(d - 2*r, Fraction(1,4)))
R4 = quiet(delegate, A, absle(r,1), GP4, "disj")
print("disj seed Display (z3):", fmt(R4["seed"]["Display"]))
cand4 = d == If(absle(m, Fraction(1,8)), 2*m, If(m >= 0, 1, -1))
print("disj witness == (|m|<=1/8 -> 2m, m>=0 -> 1, else -1):", eq(R4["seed"]["Display"], cand4))
cand4b = d == If(absle(m, Fraction(1,8)), 2*m, If(m >= 0, 1, RealVal(-1)))
AD4, GD4 = R4["sweep"]["Display"]; AR4, GR4 = R4["sweep"]["Radio"]
print("disj sweep Display A:", eq(AD4, BoolVal(True)))
print("disj sweep Display G (z3):", fmt(GD4))
print("disj sweep Radio G (z3):", fmt(GR4))
# H = 2
A2h = Arch({"Radio": (["r"], ["m"]), "Display": (["m"], ["d"])}, env=["r"], H=2)
GPt = And(Alw(0,1, lambda t: Implies(V("r",t) >= Fraction(1,2), Ev(0,1, lambda u: V("d",u) >= Fraction(1,2))(t)))(0),
          Alw(0,2, lambda t: absle(V("d",t), 1))(0))
Rt = quiet(delegate, A2h, Alw(0,2, lambda t: absle(V("r",t),1))(0), GPt, "H2")
print("H2 seed Display (z3):", fmt(Rt["seed"]["Display"]))
m0,m1_,m2_ = V("m",0),V("m",1),V("m",2); d0,d1,d2 = V("d",0),V("d",1),V("d",2)
cand_t = And(d0 == 0, d1 == If(m0 >= Fraction(1,2), Fraction(1,2), 0) , d2 == If(m1_ >= Fraction(1,2), Fraction(1,2), 0))
print("H2 witness candidate (d0=0, d1=[m0>=1/2]/2, d2=[m1>=1/2]/2):", eq(Rt["seed"]["Display"], cand_t))
