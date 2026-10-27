"""Pointwise check of the set-theoretic inference rules of the author's notes (2026-10-21).

Every statement is an inclusion between Boolean combinations of sets of behaviours, so it holds iff it holds for
one arbitrary behaviour x.  We model "x in A" by a Boolean a, etc., and ask Z3 whether the premises can hold while
the conclusion fails (satisfiable = the rule is wrong).  Sets: A (top assumption), G (top guarantee), A1, G1, A2,
G2, M1, M2.  "M |= (A, G)" is M & A -> G (equivalent to: for every E <= A, M & E <= G).
"""
from z3 import Bool, Bools, Implies, And, Or, Not, Solver, unsat

a, g, a1, g1, a2, g2, m1, m2 = Bools("a g a1 g1 a2 g2 m1 m2")
imp = lambda m, A, G: Implies(And(m, A), G)          # x-pointwise form of M |= (A, G)
sat_ = lambda A, G: Or(Not(A), G)                    # saturated implementation set S = not A or G

def holds(name, premises, conclusion):
    s = Solver(); s.add(And(*premises)); s.add(Not(conclusion))
    r = s.check() == unsat
    print(f"  {'holds ' if r else 'FAILS '} {name}")
    return r

results = []
print("Lemma (simplified refinement), both directions, without the nonemptiness hypothesis:")
refine_full = And(Implies(a2, a1), Implies(Or(g1, Not(a1)), Or(g2, Not(a2))))   # (A2<=A1) and (G1 u -A1 <= G2 u -A2)
refine_simp = And(Implies(a2, a1), Implies(And(g1, a2), g2))                     # (A2<=A1) and (G1 n A2 <= G2)
results.append(holds("full refinement -> simplified", [refine_full], refine_simp))
results.append(holds("simplified -> full refinement", [refine_simp], refine_full))

print("Rules:")
results.append(holds("Refinement", [imp(m1, a1, g1), refine_simp], imp(m1, a2, g2)))
results.append(holds("Composition as written: premise G1 <= A1 (typo)",
                     [imp(m1, a1, g1), imp(m2, a2, g2), Implies(g1, a1)], imp(And(m1, m2), a1, g2)) is False)
results.append(holds("Composition corrected: premise G1 <= A2",
                     [imp(m1, a1, g1), imp(m2, a2, g2), Implies(g1, a2)], imp(And(m1, m2), a1, g2)))
results.append(holds("Composition corrected, via the composition operator and refinement",
                     [Implies(g1, a2)],
                     And(Implies(a1, Or(And(a1, a2), Not(And(g1, g2)))), Implies(And(And(g1, g2), a1), g2))))
results.append(holds("Assumption Relaxation", [imp(m1, a1, g1), Implies(a2, a1)], imp(m1, a2, g1)))
results.append(holds("Guarantee Tightening", [imp(m1, a1, g1), Implies(And(g1, a1), g2)], imp(m1, a1, g2)))

print("Two-component scheme (A<=A1, G1<=A2, G2 n A2 <= G, M1 |= (A1,G1), M2 |= (A2,G2)):")
scheme = [Implies(a, a1), Implies(g1, a2), Implies(And(g2, a2), g), imp(m1, a1, g1), imp(m2, a2, g2)]
results.append(holds("scheme -> M1||M2 |= (A, G)", scheme, imp(And(m1, m2), a, g)))
results.append(holds("Guarantee Tightening alone does NOT close the last step (needs G2 n A <= G)",
                     [Implies(And(g2, a2), g)], Implies(And(g2, a), g)) is False)
results.append(holds("scheme -> (V2) for component 2:  A n S1 n S2 <= A2", scheme[:3], Implies(And(a, sat_(a1, g1), sat_(a2, g2)), a2)))
results.append(holds("scheme -> (V2) for component 1:  A n S1 n S2 <= A1", scheme[:3], Implies(And(a, sat_(a1, g1), sat_(a2, g2)), a1)))
results.append(holds("scheme -> (V1):  A n S1 n S2 <= G", scheme[:3], Implies(And(a, sat_(a1, g1), sat_(a2, g2)), g)))
results.append(holds("(V1),(V2) do NOT imply G1 <= A2 (the scheme is strictly stronger)",
                     [Implies(And(a, sat_(a1, g1), sat_(a2, g2)), a2), Implies(And(a, sat_(a1, g1), sat_(a2, g2)), a1),
                      Implies(And(a, sat_(a1, g1), sat_(a2, g2)), g)], Implies(g1, a2)) is False)
results.append(holds("(V1),(V2) -> M1||M2 |= (A, G)  (the plan's constraints suffice)",
                     [Implies(And(a, sat_(a1, g1), sat_(a2, g2)), a2), Implies(And(a, sat_(a1, g1), sat_(a2, g2)), a1),
                      Implies(And(a, sat_(a1, g1), sat_(a2, g2)), g), imp(m1, a1, g1), imp(m2, a2, g2)],
                     imp(And(m1, m2), a, g)))
print(f"{sum(results)}/{len(results)} as expected")
raise SystemExit(0 if all(results) else 1)
