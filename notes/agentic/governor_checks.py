#!/usr/bin/env python3
"""Verifier checks for the agentic formulation (notes/agentic/formulation.md), on the speed-governor chain of
docs/example.tex.  Run from the directory root:

    .venv/bin/python notes/agentic/governor_checks.py

Quantifier elimination is used in two places only: K_alt ("(K) by alternation"), which quantifies over the ports
of ONE component, and the projection of one counterexample cell (a single conjunction of literals).  Every proposal below is hand-written: it stands for what a proposer would output.
The script prints every verdict and every counterexample, and exits 0 iff every verdict is the expected one.
Times are printed for information; they are machine-dependent and do not enter the exit code."""
import sys, time
from fractions import Fraction as Fr
from z3 import *

# ---------- the instance (same A_P, G_P as scripts/delegate.py, horizon H as a parameter) ----------
COMPS = {"Perception": (["o"], ["e"]), "Controller": (["e"], ["u"]), "Actuator": (["u"], ["v"])}
ENV = ["o"]
SYM = {}
def X(v, t):
    k = f"{v}_{t}"
    if k not in SYM: SYM[k] = Real(k)
    return SYM[k]
def alw(a, b, f): return And([f(t) for t in range(a, b + 1)])
def query(H):
    AP = alw(0, H, lambda t: And(X("o", t) >= 0, X("o", t) <= 5))
    GP = And(alw(0, H, lambda t: And(X("v", t) >= 0, X("v", t) <= 2)),
             alw(0, H - 1, lambda t: Implies(X("o", t) <= 1, Or(X("v", t) <= Fr(1, 4), X("v", t + 1) <= Fr(1, 4)))),
             alw(0, H - 1, lambda t: Implies(X("o", t) >= 3, Or(X("v", t) >= 1, X("v", t + 1) >= 1))))
    return AP, GP

# ---------- the verifier ----------
def syms(f):
    out, seen = set(), set()
    def walk(e):
        if e.get_id() in seen: return
        seen.add(e.get_id())
        if is_const(e) and e.decl().kind() == Z3_OP_UNINTERPRETED: out.add(str(e))
        for c in e.children(): walk(c)
    walk(f); return out
def ports(c): i, o = COMPS[c]; return sorted(set(i) | set(o))   # sorted: formula construction order fixes Z3 models
def ports_ok(c, *fs):
    """(Ports): a syntactic check.  Returns the list of offending timed variables (empty = pass)."""
    return sorted({s for f in fs for s in syms(f) if s.rsplit("_", 1)[0] not in ports(c)})
def valid(f, timeout=None):
    """Validity in quantifier-free linear real arithmetic: Not(f) unsat.  Returns (verdict, counterexample model)."""
    s = Solver(); s.set("random_seed", 0)
    if timeout: s.set("timeout", timeout)
    s.add(Not(f)); r = s.check()
    if r == unsat: return True, None
    if r == sat: return False, s.model()
    return None, None                                       # unknown: the loop treats this as a rejection
def show(m, keep=None, H=2):
    """A model as a trace, optionally projected onto the variables in `keep` (a component's ports)."""
    names = sorted({s.rsplit("_", 1)[0] for s in SYM} if keep is None else keep)
    rows = []
    for v in names:
        vals = [m.eval(X(v, t), model_completion=True) for t in range(H + 1)]
        rows.append(f"{v}=({', '.join(str(x) for x in vals)})")
    return " ".join(rows)

def atoms(f):
    """The arithmetic atoms of a quantifier-free formula, each once, in first-visit order."""
    out, seen = [], set()
    def walk(e):
        if e.get_id() in seen: return
        seen.add(e.get_id())
        if is_app(e) and e.decl().kind() in (Z3_OP_LE, Z3_OP_LT, Z3_OP_GE, Z3_OP_GT, Z3_OP_EQ) and is_arith(e.children()[0]):
            out.append(e); return
        for c in e.children(): walk(c)
    walk(f); return out
def saturate(A, G): return simplify(Or(Not(A), G))
def V1(AP, GP, S):
    return valid(Implies(And(AP, *S.values()), GP))
def V2(AP, S, A):
    out = {}
    for j, Aj in A.items(): out[j] = valid(Implies(And(AP, *S.values()), Aj))
    return out
def K_cert(c, Sc, strat, H):
    """(K) through a strategy certificate: strat[(y, t)] is a term over inputs of c at times <= t (checked
    syntactically).  Then (K) holds if Sc[outputs := strategy] is valid: one quantifier-free validity check over the
    input history of c.  On failure the counterexample is an input history of c, nothing else."""
    ins, outs = COMPS[c]
    for (y, t), term in strat.items():
        bad = [s for s in sorted(syms(term)) if s.rsplit("_", 1)[0] not in ins or int(s.rsplit("_", 1)[1]) > t]
        if bad: return False, f"certificate for {y}_{t} reads {bad}: not an input at a time <= {t}"
    missing = [(y, t) for y in outs for t in range(H + 1) if (y, t) not in strat]
    if missing: return False, f"certificate misses {missing}"
    sub = [(X(y, t), term) for (y, t), term in strat.items()]
    ok, m = valid(substitute(Sc, *sub))
    return ok, (None if ok else show(m, ins, H))
def K_alt(c, Sc, H):
    """(K) by alternation: forall in(0) exists out(0) ... forall in(H) exists out(H) Sc, over the ports of c only."""
    ins, outs = COMPS[c]; q = Sc
    for t in reversed(range(H + 1)):
        q = Exists([X(y, t) for y in outs], q)
        if ins: q = ForAll([X(x, t) for x in ins], q)
    return valid(q)[0]
def R_of(AP, S, c): return And(AP, *[S[j] for j in S if j != c])
def refines_quotient(AP, GP, S, A, c):
    """C_c refines rho_{ports(c)}(P / composition of the others), checked WITHOUT computing the quotient:
       (a) R_c & S_c |= G_P & AND_{j != c} A_j   and   (b) R_c |= A_c."""
    R = R_of(AP, S, c)
    a = valid(Implies(And(R, S[c]), And(GP, *[A[j] for j in A if j != c])))[0]
    b = valid(Implies(R, A[c]))[0]
    return a and b
def in_quotient(AP, GP, S, A, c, z, H):
    """Membership of ONE local history z of ports(c) in the guarantee of rho_{ports(c)}(P / others):
       z is allowed iff  R_c & (ports(c) = z) & not(G_P & AND_{j != c} A_j)  is unsat.  One quantifier-free call.
       Returns (allowed, completion): the completion is a full trace witnessing that z is forbidden."""
    R = R_of(AP, S, c)
    pin = And([X(v, t) == z[(v, t)] for (v, t) in z])
    s = Solver(); s.add(R, pin, Not(And(GP, *[A[j] for j in A if j != c])))
    r = s.check()
    return (True, None) if r == unsat else (False, s.model())

# ---------- reporting ----------
EXPECT = []
def verdict(label, got, want):
    EXPECT.append((label, got == want)); print(f"  {label}: {got}" + ("" if got == want else f"   <-- expected {want}"))

def check_family(name, AP, GP, A, G, strat, H, want_v1=True, want_v2=True, want_k=None, alt=True):
    print("-" * 78); print(name)
    S = {c: saturate(A[c], G[c]) for c in COMPS}
    for c in COMPS:
        verdict(f"(Ports) {c}", ports_ok(c, A[c], G[c]), [])
    t0 = time.perf_counter(); ok1, m1 = V1(AP, GP, S); t1 = time.perf_counter() - t0
    verdict("(V1)", ok1, want_v1); print(f"    [{t1*1000:.1f} ms]")
    if not ok1:
        print("    counterexample (full trace, seen by the coordinator):", show(m1, None, H))
        for c in COMPS: print(f"    projected to {c}: {show(m1, ports(c), H)}")
    t0 = time.perf_counter(); v2 = V2(AP, S, A); t2 = time.perf_counter() - t0
    for c in COMPS:
        verdict(f"(V2) A_{c}", v2[c][0], want_v2 if not isinstance(want_v2, dict) else want_v2[c])
        if not v2[c][0]:
            print(f"    counterexample: {show(v2[c][1], None, H)}")
    print(f"    [(V2) all: {t2*1000:.1f} ms]")
    for c in COMPS:
        want = True if want_k is None else want_k[c]
        if c in strat:
            t0 = time.perf_counter(); ok, info = K_cert(c, S[c], strat[c], H); tk = time.perf_counter() - t0
            verdict(f"(K) {c} by certificate", ok, want); print(f"    [{tk*1000:.1f} ms]")
            if not ok: print(f"    counterexample (input history of {c}): {info}")
        if alt:
            t0 = time.perf_counter(); ok = K_alt(c, S[c], H); tk = time.perf_counter() - t0
            verdict(f"(K) {c} by alternation over ports({c})", ok, want); print(f"    [{tk*1000:.1f} ms]")
    return S

def main():
    print(f"z3 version {get_version_string()}")
    H = 2; AP, GP = query(H)
    o, e, u, v = (lambda t: X("o", t)), (lambda t: X("e", t)), (lambda t: X("u", t)), (lambda t: X("v", t))
    T = BoolVal(True)
    print(f"H = {H}\n  A_P = {A_P_str(AP)}\n  G_P = {A_P_str(GP)}")

    # ---- D_react: threshold-preserving, memoryless, written as PolySTL 'always' formulas ----
    G = {"Perception": alw(0, H, lambda t: And(Implies(o(t) >= 3, e(t) >= 3), Implies(o(t) <= 1, e(t) <= 1))),
         "Controller": alw(0, H, lambda t: And(Implies(e(t) >= 3, u(t) >= 3), Implies(e(t) <= 1, u(t) <= 1))),
         "Actuator":   alw(0, H, lambda t: And(v(t) >= 0, v(t) <= 2, Implies(u(t) >= 3, v(t) >= 1),
                                               Implies(u(t) <= 1, v(t) <= Fr(1, 4))))}
    A = {c: T for c in COMPS}
    strat = {"Perception": {("e", t): o(t) for t in range(H + 1)},
             "Controller": {("u", t): e(t) for t in range(H + 1)},
             "Actuator":   {("v", t): If(u(t) >= 3, RealVal(1), RealVal(0)) for t in range(H + 1)}}
    S_react = check_family("D_react: always(o>=3 -> e>=3, o<=1 -> e<=1); same for e->u; always(v in [0,2], u>=3 -> v>=1, u<=1 -> v<=1/4)",
                           AP, GP, A, G, strat, H)
    for c in COMPS: verdict(f"C_{c} refines rho(P / others), checked without the quotient", refines_quotient(AP, GP, S_react, A, c), True)

    # ---- D_lazy: only the one feature the query needs, o(1) >= 3, crosses the edges ----
    G_lazy = {"Perception": Implies(o(1) >= 3, e(1) >= 3),
              "Controller": Implies(e(1) >= 3, u(1) >= 3),
              "Actuator":   And(alw(0, H, lambda t: And(v(t) >= 0, v(t) <= 2)), v(0) >= 1, v(1) <= Fr(1, 4),
                                Implies(u(1) >= 3, v(2) >= 1))}
    strat_lazy = {"Perception": strat["Perception"], "Controller": strat["Controller"],
                  "Actuator": {("v", 0): RealVal(1), ("v", 1): RealVal(0), ("v", 2): If(u(1) >= 3, RealVal(1), RealVal(0))}}
    S_lazy = check_family("D_lazy: (o(1)>=3 -> e(1)>=3); (e(1)>=3 -> u(1)>=3); v in [0,2], v(0)>=1, v(1)<=1/4, (u(1)>=3 -> v(2)>=1)",
                          AP, GP, A, G_lazy, strat_lazy, H)
    # sampled quotient: is D_lazy's Actuator maximal given the others?  one local history outside S_Actuator
    z = {("u", t): 0 for t in range(H + 1)}; z.update({("v", 0): Fr(1, 8), ("v", 1): 1, ("v", 2): Fr(1, 8)})
    zin = valid(Implies(And([X(a, t) == val for (a, t), val in z.items()]), S_lazy["Actuator"]))[0]
    allowed, _ = in_quotient(AP, GP, S_lazy, A, "Actuator", z, H)
    print("  local history z of Actuator: u = (0,0,0), v = (1/8, 1, 1/8)")
    verdict("  z satisfies S_Actuator of D_lazy", zin, False)
    verdict("  z is allowed by rho(P / others) (one quantifier-free call)", allowed, True)
    print("  => D_lazy's Actuator is not maximal: z is a positive example a proposer may add.")
    z2 = {("u", t): 0 for t in range(H + 1)}; z2.update({("v", 0): Fr(1, 8), ("v", 1): Fr(1, 8), ("v", 2): Fr(1, 8)})
    allowed2, comp = in_quotient(AP, GP, S_lazy, A, "Actuator", z2, H)
    verdict("  z' = (u = 0, v = 1/8 throughout) allowed by rho(P / others)", allowed2, False)
    print("    completion witnessing that z' is forbidden (full trace):", show(comp, None, H))

    # ---- the swept (maximal) family of docs/example.tex, transcribed, checked by the same verifier ----
    rng = lambda w, lo, hi: alw(0, H, lambda t: And(X(w, t) >= lo, X(w, t) <= hi))
    A_sw = {"Perception": AP, "Controller": T, "Actuator": T}
    G_sw = {"Perception": Implies(And(AP, o(1) >= 3), And(rng("e", 0, 5), e(1) >= 3)),
            "Controller": Implies(And(rng("e", 0, 5), e(1) >= 3), And(rng("u", 0, 5), u(1) >= 3)),
            "Actuator": And(rng("v", 0, 2), Or(v(0) >= 1, v(1) >= 1), Or(v(0) <= Fr(1, 4), v(1) <= Fr(1, 4)),
                            Or(v(1) <= Fr(1, 4), v(2) <= Fr(1, 4)), Implies(And(rng("u", 0, 5), u(1) >= 3), Or(v(1) >= 1, v(2) >= 1)))}
    S_sw = check_family("swept family of docs/example.tex (transcribed): same verifier, no certificate", AP, GP, A_sw, G_sw, {}, H)
    for c in COMPS:
        verdict(f"  S_{c} of D_lazy |= S_{c} of the swept family", valid(Implies(S_lazy[c], S_sw[c]))[0],
                c == "Actuator")
    print("  => D_lazy is not inside the maximal family: maximal is not greatest (no greatest acceptable delegation).")
    # ---- weakening from the forwarding family: each step needs only quantifier-free checks ----
    print("-" * 78); print("weakening mode: start from forwarding guarantees e = o, u = e and D_lazy's Actuator")
    W = {"Perception": alw(0, H, lambda t: e(t) == o(t)), "Controller": alw(0, H, lambda t: u(t) == e(t)),
         "Actuator": G_lazy["Actuator"]}
    verdict("  start: (V1)", V1(AP, GP, W)[0], True)
    for c in ["Perception", "Controller"]:
        new = dict(W); new[c] = G_lazy[c]
        verdict(f"  weaken {c}: old S |= new S (so (R),(K) are inherited)", valid(Implies(W[c], new[c]))[0], True)
        verdict(f"  weaken {c}: (V1) with the others", V1(AP, GP, new)[0], True)
        W = new
    # an over-weakening that the verifier rejects
    bad = dict(W); bad["Perception"] = T
    ok, m = V1(AP, GP, bad)
    verdict("  over-weaken Perception to true: (V1)", ok, False)
    print("    counterexample:", show(m, None, H))
    print("    projected to Perception:", show(m, ports("Perception"), H))

    # ---- a faulty first round and its repair ----
    G0 = dict(G); G0["Perception"] = alw(0, H, lambda t: Implies(o(t) >= 3, e(t) >= 3))   # forgot the low side
    S0 = check_family("round 0 (faulty): Perception forgets (o<=1 -> e<=1); others as D_react", AP, GP, A, G0, strat, H,
                      want_v1=False, alt=False)
    ok, m = V1(AP, GP, S0)
    print("  every component's projection lies outside its own quotient guarantee (the algebra names no culprit):")
    for c in COMPS:
        zc = {(x, t): m.eval(X(x, t), model_completion=True) for x in ports(c) for t in range(H + 1)}
        verdict(f"    projection to {c} allowed by rho(P / others)", in_quotient(AP, GP, S0, A, c, zc, H)[0], False)
    # generalise the counterexample to its cell: the literals of all atoms of the negated (V1) obligation that hold at
    # the counterexample.  Every trace in the cell is a counterexample; the cell is ONE conjunction, so projecting it
    # onto ports(c) eliminates quantifiers from a single polyhedron (no case split), not from a general formula.
    F = And(AP, *S0.values(), Not(GP))
    cell = And([a if is_true(m.eval(a, model_completion=True)) else Not(a) for a in atoms(F)])
    verdict("  the cell of the counterexample entails A_P & all S_i & not G_P", valid(Implies(cell, F))[0], True)
    for c in ["Perception"]:
        hidden = [X(x, t) for x in sorted({k.rsplit("_", 1)[0] for k in SYM}) if x not in ports(c) for t in range(H + 1)]
        t0 = time.perf_counter(); proj = simplify(Tactic("qe")(Exists(hidden, cell)).as_expr()); tq = time.perf_counter() - t0
        print(f"  projected cell for {c} (a forbidden region over its ports) [{tq*1000:.1f} ms]: {str(proj).replace(chr(10), ' ')}")
        verdict(f"  projected cell for {c} is over ports({c})", ports_ok(c, proj), [])
        fixed = alw(0, H, lambda t: And(Implies(o(t) >= 3, e(t) >= 3), Implies(o(t) <= 1, e(t) <= 1)))
        verdict(f"  repaired {c} guarantee excludes the projected cell", valid(Not(And(fixed, proj)))[0], True)

    # ---- assume-guarantee round: Actuator assumes a decisive command; (V2) blames the writer of u ----
    A_ag = {"Perception": T, "Controller": T, "Actuator": alw(0, H, lambda t: Or(u(t) >= 3, u(t) <= 1))}
    check_family("assume-guarantee, round 1: Actuator assumes always(u>=3 or u<=1); Controller unchanged",
                 AP, GP, A_ag, G, strat, H, want_v1=False,
                 want_v2={"Perception": True, "Controller": True, "Actuator": False}, alt=False)
    S_ag1 = {c: saturate(A_ag[c], G[c]) for c in COMPS}
    _, m_ag = V1(AP, GP, S_ag1)
    verdict("  the (V1) counterexample satisfies A_Actuator", is_true(m_ag.eval(A_ag["Actuator"], model_completion=True)), False)
    print("  (saturation lets the Actuator do anything off its assumption, so this (V1) failure is the (V2) failure")
    print("   seen again; the coordinator routes it to the writer of u, the Controller.)")
    G_ag = dict(G); G_ag["Controller"] = And(G["Controller"], A_ag["Actuator"])
    strat_ag = dict(strat); strat_ag["Controller"] = {("u", t): If(e(t) >= 3, RealVal(3), RealVal(0)) for t in range(H + 1)}
    check_family("assume-guarantee, round 2: Controller adds always(u>=3 or u<=1) (strategy u := 3 if e>=3 else 0)",
                 AP, GP, A_ag, G_ag, strat_ag, H, alt=False)

    # ---- proposals the verifier must reject for the reasons stated in the report ----
    print("-" * 78); print("rejections")
    verdict("  Actuator proposes always(o<=1 -> v<=1/4): (Ports) offenders", ports_ok("Actuator", alw(0, H, lambda t: Implies(o(t) <= 1, v(t) <= Fr(1, 4))))[:1], ["o_0"])
    Sf = dict(S_react); Sf["Actuator"] = saturate(BoolVal(False), T)            # A = false: S = true
    v2f = valid(Implies(And(AP, *Sf.values()), BoolVal(False)))
    verdict("  Actuator proposes A = false: (V2) for A_Actuator", v2f[0], False)
    print("    counterexample:", show(v2f[1], None, H))
    verdict("  Actuator proposes (true, false): (K) by alternation", K_alt("Actuator", BoolVal(False), H), False)
    pin = alw(0, H, lambda t: And(u(t) == 0, v(t) == 0))
    ok, info = K_cert("Actuator", pin, {("v", t): RealVal(0) for t in range(H + 1)}, H)
    verdict("  Actuator pins its input, always(u = 0 and v = 0): (K) by certificate", ok, False)
    print("    counterexample (input history of Actuator):", info)
    verdict("  same, (K) by alternation", K_alt("Actuator", pin, H), False)
    ok, info = K_cert("Actuator", G_lazy["Actuator"], {("v", 0): RealVal(1), ("v", 1): RealVal(0), ("v", 2): If(u(2) >= 3, RealVal(1), RealVal(0))}, H)
    verdict("  Actuator certificate v(2) := 1 if u(2)>=3: wrong strategy for D_lazy (counterexample shown)", ok, False)
    print("    counterexample (input history of Actuator):", info)
    ok, info = K_cert("Actuator", G_lazy["Actuator"], {("v", 0): If(u(1) >= 3, RealVal(1), RealVal(1)), ("v", 1): RealVal(0), ("v", 2): RealVal(1)}, H)
    verdict("  Actuator certificate reading u(1) at time 0: rejected syntactically", ok, False)
    print("    reason:", info)

    # ---- scaling of the quantifier-free checks with the horizon (D_react unrolls to any H) ----
    print("-" * 78); print("scaling of D_react's checks with the horizon (times machine-dependent)")
    for Hn in (2, 5, 10, 20, 40, 80):
        APn, GPn = query(Hn)
        Gn = {"Perception": alw(0, Hn, lambda t: And(Implies(o(t) >= 3, e(t) >= 3), Implies(o(t) <= 1, e(t) <= 1))),
              "Controller": alw(0, Hn, lambda t: And(Implies(e(t) >= 3, u(t) >= 3), Implies(e(t) <= 1, u(t) <= 1))),
              "Actuator": alw(0, Hn, lambda t: And(v(t) >= 0, v(t) <= 2, Implies(u(t) >= 3, v(t) >= 1), Implies(u(t) <= 1, v(t) <= Fr(1, 4))))}
        t0 = time.perf_counter(); ok1 = V1(APn, GPn, Gn)[0]; t1 = time.perf_counter() - t0
        t0 = time.perf_counter()
        okk = all(K_cert(c, Gn[c], {("e", t): o(t) for t in range(Hn + 1)} if c == "Perception" else
                         {("u", t): e(t) for t in range(Hn + 1)} if c == "Controller" else
                         {("v", t): If(u(t) >= 3, RealVal(1), RealVal(0)) for t in range(Hn + 1)}, Hn)[0] for c in COMPS)
        tk = time.perf_counter() - t0
        verdict(f"  H = {Hn:2d}: (V1) and (K) by certificate (all three)", ok1 and okk, True)
        print(f"    [{4 * (Hn + 1)} timed variables; (V1) {t1*1000:.1f} ms; (K) x3 {tk*1000:.1f} ms]")

    print("=" * 78)
    bad = [l for l, ok in EXPECT if not ok]
    print(f"{len(EXPECT)} verdicts; " + ("all as expected" if not bad else f"UNEXPECTED: {bad}"))
    return 1 if bad else 0

def A_P_str(f): return str(f).replace("\n", " ")

if __name__ == "__main__":
    sys.exit(main())
