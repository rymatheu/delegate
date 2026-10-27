"""Checks for theory/temporal-decomposition.md (syntax-directed decomposition D of full PolySTL).

Run:  .venv/bin/python scripts/polystl_decomp_check.py

Sections
  [S] rule schemas of the table of D, propositionally over bounded time (sound rows valid, naive rows refuted)
  [i] EARS chain  G(|r|>0.5 -> F_[0,2] |d|>=0.4)  over Radio -> Display, delays (0,0) and (1,1)
  [ii] eventually-queries on the relay: naive distribution unsound, decider assignments, comb flag, sweep from D's seed
  [iii] information fork: no local delegation exists (agreement lemma + finite-sample UNSAT); with an edge, D succeeds
  [iv] temporal assumption flow: env liveness -> response chain; shadow assumption vs forward image

Quantifier elimination: Z3 tactic qe2 only, every elimination cross-checked against the quantified input by two
decision paths (qe2+smt and Z3's default engine). Closed quantified sentences are decided by both paths and the
two verdicts must agree.
"""
import itertools
import time
import z3

TIMEOUT_MS = 600_000
RESULTS = []


def report(tag, claim, ok, expect=True, extra=""):
    status = "PASS" if ok == expect else "FAIL"
    RESULTS.append((tag, status))
    print(f"  [{status}] {tag}: {claim} -> {ok}{(' | ' + extra) if extra else ''}")


# ------------------------------------------------------------------ decision helpers
def valid(f):
    """Validity of a quantifier-free (or quantified) formula with Z3's default engine. Returns (bool, model)."""
    s = z3.Solver(); s.set("timeout", TIMEOUT_MS); s.add(z3.Not(f)); r = s.check()
    assert r != z3.unknown, f"default engine: unknown ({s.reason_unknown()})"
    return (r == z3.unsat), (s.model() if r == z3.sat else None)


def sat(f):
    s = z3.Solver(); s.set("timeout", TIMEOUT_MS); s.add(f); r = s.check()
    assert r != z3.unknown
    return r == z3.sat, (s.model() if r == z3.sat else None)


def decide_qe2(f):
    s = z3.Then("qe2", "smt").solver(); s.add(z3.Not(f)); r = s.check()
    assert r != z3.unknown, "qe2+smt: unknown"
    return r == z3.unsat


def decide_sentence(f):
    """Closed quantified LRA sentence: decide by qe2+smt and by the default engine; they must agree."""
    a = decide_qe2(f)
    b, _ = valid(f)
    assert a == b, f"decision paths disagree: qe2+smt={a}, default={b}"
    return a


def qe(f):
    """qe2 elimination, cross-checked: output equivalent to input under both decision paths."""
    g = z3.Goal(); g.add(f)
    out = z3.Then("qe2", "simplify")(g).as_expr()
    ok1 = decide_qe2(out == f)
    ok2, _ = valid(out == f)
    assert ok1 and ok2, f"qe2 output not equivalent to input (qe2+smt {ok1}, default {ok2})"
    return out


# ------------------------------------------------------------------ mini bounded PolySTL (unrolled, QF_LRA)
class Sig:
    """Signals over [0,H]: x[name][t] is a z3 Real (or Bool for schema checks)."""

    def __init__(self, names, H, kind=z3.Real, tag=""):
        self.H = H
        self.x = {n: [kind(f"{n}{tag}_{t}") for t in range(H + 1)] for n in names}

    def __getitem__(self, n):
        return self.x[n]

    def vars(self, names=None, times=None):
        names = names if names is not None else list(self.x)
        times = times if times is not None else range(self.H + 1)
        return [self.x[n][t] for n in names for t in times]


def _chk(t, H):
    if t > H:
        raise IndexError(f"formula reaches time {t} > horizon {H}")


def Alw(a, b, f, H):
    def g(t):
        _chk(t + b, H)
        return z3.And([f(t + s) for s in range(a, b + 1)]) if b >= a else z3.BoolVal(True)
    return g


def Ev(a, b, f, H):
    def g(t):
        _chk(t + b, H)
        return z3.Or([f(t + s) for s in range(a, b + 1)]) if b >= a else z3.BoolVal(False)
    return g


def Until(a, b, f, g_, H):
    """f U_[a,b] g at t: exists tau in [a,b] with g(t+tau) and f(t+s) for all s in [0,tau)."""
    def g(t):
        _chk(t + b, H)
        return z3.Or([z3.And([g_(t + tau)] + [f(t + s) for s in range(tau)]) for tau in range(a, b + 1)])
    return g


def Imp(f, g):
    return lambda t: z3.Implies(f(t), g(t))


def Conj(*fs):
    return lambda t: z3.And([f(t) for f in fs])


def Disj(*fs):
    return lambda t: z3.Or([f(t) for f in fs])


def Tru():
    return lambda t: z3.BoolVal(True)


def absle(x, c):
    return z3.And(x <= c, -x <= c)


def absge(x, c):
    return z3.Or(x >= c, x <= -c)


def absgt(x, c):
    return z3.Or(x > c, x < -c)


def types_of(S, bounds):
    return z3.And([absle(S[n][t], bounds[n]) for n in bounds for t in range(S.H + 1)])


def receptive_causal(S, ins, outs, delay, obligation, bounds, assumption=None):
    """Closed sentence: for all typed input histories there is a causal (delay-respecting) output history
    in the obligation (saturated with the assumption if given). Prefix built from the time-expanded order:
    outputs at time tau are chosen after inputs up to tau-delay are revealed."""
    H = S.H
    events = []
    for tau in range(delay):                       # outputs that see no input
        events.append(("E", [S[o][tau] for o in outs], tau))
    for t in range(H + 1):
        events.append(("A", [S[i][t] for i in ins], t))
        if t + delay <= H:
            events.append(("E", [S[o][t + delay] for o in outs], t + delay))
    M = obligation if assumption is None else z3.Implies(assumption, obligation)
    for kind, vs, t in reversed(events):
        if kind == "E":
            ty = z3.And([absle(v, bounds[o]) for v, o in zip(vs, outs)])
            M = z3.Exists(vs, z3.And(ty, M))
        else:
            ty = z3.And([absle(v, bounds[i]) for v, i in zip(vs, ins)])
            M = z3.ForAll(vs, z3.Implies(ty, M))
    return decide_sentence(M)


def graph_in(S, strategy, obligation, bounds, ins):
    """Explicit strategy (dict var -> term over inputs/earlier outputs): its graph lies in the obligation."""
    sub = [(v, e) for v, e in strategy.items()]
    ob = obligation
    for _ in range(S.H + 2):                       # terms may refer to earlier outputs: substitute to a fixpoint
        ob = z3.substitute(ob, *sub)
    ty = z3.And([absle(S[i][t], bounds[i]) for i in ins for t in range(S.H + 1)])
    tys = z3.And([absle(e, bounds[str(v).split("_")[0]]) for v, e in strategy.items()])
    for _ in range(S.H + 2):
        tys = z3.substitute(tys, *sub)
    ok, _ = valid(z3.Implies(ty, z3.And(ob, tys)))
    return ok


# ================================================================== [S] rule schemas
def schemas():
    print("\n[S] rule schemas of D, propositional, bounded time (H=6). Hypothesis 'split': p_k(t) & p_i(t) -> phi(t).")
    H = 6
    B = Sig(["pk", "pi", "phi", "qk", "qi", "psi", "s", "f", "al", "be", "ga", "q", "p"], H, kind=z3.Bool)
    P = lambda n: (lambda t: B[n][t])
    split = z3.And([z3.Implies(z3.And(B["pk"][t], B["pi"][t]), B["phi"][t]) for t in range(H + 1)])
    split2 = z3.And([z3.Implies(z3.And(B["qk"][t], B["qi"][t]), B["psi"][t]) for t in range(H + 1)])
    a, b = 0, 3
    # box
    ok, _ = valid(z3.Implies(z3.And(split, Alw(a, b, P("pk"), H)(0), Alw(a, b, P("pi"), H)(0)), Alw(a, b, P("phi"), H)(0)))
    report("S.box", "Alw pk & Alw pi |= Alw phi", ok)
    # eventually naive
    ok, m = valid(z3.Implies(z3.And(split, Ev(a, b, P("pk"), H)(0), Ev(a, b, P("pi"), H)(0)), Ev(a, b, P("phi"), H)(0)))
    report("S.ev-naive", "Ev pk & Ev pi |= Ev phi  (naive distribution)", ok, expect=False,
           extra="counterexample: pk only at " + str([t for t in range(b + 1) if z3.is_true(m.eval(B['pk'][t]))]) +
           ", pi only at " + str([t for t in range(b + 1) if z3.is_true(m.eval(B['pi'][t]))]) if m is not None else "")
    ok, _ = valid(z3.Implies(z3.And(split, Ev(a, b, P("pk"), H)(0), Alw(a, b, P("pi"), H)(0)), Ev(a, b, P("phi"), H)(0)))
    report("S.ev-decide", "Ev pk & Alw pi |= Ev phi  (decider k)", ok)
    ok, _ = valid(z3.Implies(z3.And(split, Alw(2, 2, P("pk"), H)(0), Alw(2, 2, P("pi"), H)(0)), Ev(a, b, P("phi"), H)(0)))
    report("S.ev-static", "pk@2 & pi@2 |= Ev_[0,3] phi  (static witness)", ok)
    deliver = Alw(0, H, Imp(P("s"), P("f")), H)(0)
    ok, _ = valid(z3.Implies(z3.And(split, Ev(a, b, Conj(P("pk"), P("s")), H)(0), deliver,
                                    Alw(a, b, Imp(P("f"), P("pi")), H)(0)), Ev(a, b, P("phi"), H)(0)))
    report("S.ev-announce", "Ev(pk & s) & Alw(s->f) & Alw(f->pi) |= Ev phi  (announce, delay 0)", ok)
    # announce through a delay-1 edge: the decider must commit one step ahead
    deliver1 = Alw(0, H - 1, lambda t: z3.Implies(B["s"][t], B["f"][t + 1]), H)(0)
    ok, _ = valid(z3.Implies(z3.And(split, Ev(a, b, lambda t: z3.And(B["pk"][t], B["s"][t - 1]) if t >= 1 else z3.BoolVal(False), H)(0),
                                    deliver1, Alw(a, b, Imp(P("f"), P("pi")), H)(0)), Ev(a, b, P("phi"), H)(0)))
    report("S.ev-announce-d1", "Ev(pk & prev s) & Alw(s->next f) & Alw(f->pi) |= Ev phi  (announce, delay 1)", ok)
    # disjunction
    A1, A2, Bk, Bi, F1, F2 = z3.Bools("a_k a_i b_k b_i phi1 phi2")
    sp = z3.And(z3.Implies(z3.And(A1, A2), F1), z3.Implies(z3.And(Bk, Bi), F2))
    ok, _ = valid(z3.Implies(z3.And(sp, z3.Or(A1, Bk), z3.Or(A2, Bi)), z3.Or(F1, F2)))
    report("S.or-naive", "(a_k|b_k) & (a_i|b_i) |= phi1|phi2", ok, expect=False)
    ok, _ = valid(z3.Implies(z3.And(sp, z3.Or(A1, Bk), z3.And(A2, Bi)), z3.Or(F1, F2)))
    report("S.or-decide", "(a_k|b_k) & (a_i & b_i) |= phi1|phi2", ok)
    S1, S2, G1, G2 = z3.Bools("s1 s2 g1 g2")
    ok, _ = valid(z3.Implies(z3.And(sp, z3.Or(z3.And(A1, S1), z3.And(Bk, S2)), z3.Implies(S1, G1), z3.Implies(S2, G2),
                                    z3.Implies(G1, A2), z3.Implies(G2, Bi)), z3.Or(F1, F2)))
    report("S.or-announce", "(a_k&s1 | b_k&s2) & (s_j->g_j) & (g1->a_i) & (g2->b_i) |= phi1|phi2", ok)
    # until
    bU = 3
    ok, _ = valid(z3.Implies(z3.And(split, split2, Until(0, bU, P("pk"), P("qk"), H)(0), Until(0, bU, P("pi"), P("qi"), H)(0)),
                             Until(0, bU, P("phi"), P("psi"), H)(0)))
    report("S.until-naive", "(pk U qk) & (pi U qi) |= phi U psi", ok, expect=False)
    ok, _ = valid(z3.Implies(z3.And(split, split2, Until(0, bU, P("pk"), P("qk"), H)(0),
                                    Alw(0, bU - 1, P("pi"), H)(0), Alw(0, bU, P("qi"), H)(0)),
                             Until(0, bU, P("phi"), P("psi"), H)(0)))
    report("S.until-decide", "(pk U_[0,3] qk) & Alw_[0,2] pi & Alw_[0,3] qi |= phi U_[0,3] psi", ok)
    # until, announce: decider's first flag marks the witness; exact delay-0 delivery s <-> f; receivers (pi W f) & G(f -> qi)
    exact = Alw(0, H, lambda t: B["s"][t] == B["f"][t], H)(0)
    weak_until = z3.And([z3.Implies(z3.And([z3.Not(B["f"][u]) for u in range(tau + 1)]), B["pi"][tau]) for tau in range(bU)])
    ok, _ = valid(z3.Implies(z3.And(split, split2, exact,
                                    Until(0, bU, lambda t: z3.And(B["pk"][t], z3.Not(B["s"][t])), lambda t: z3.And(B["qk"][t], B["s"][t]), H)(0),
                                    weak_until, Alw(0, bU, Imp(P("f"), P("qi")), H)(0)),
                             Until(0, bU, P("phi"), P("psi"), H)(0)))
    report("S.until-announce", "((pk&~s) U (qk&s)) & G(s<->f) & (pi W f) & G(f->qi) |= phi U psi", ok)
    # release, decide: phi R_[0,b] psi := forall tau in [0,b]: psi(tau) or exists s<tau phi(s)
    def Rel(a_, b_, f, g_):
        return lambda t: z3.And([z3.Or([g_(t + tau)] + [f(t + s_) for s_ in range(tau)]) for tau in range(a_, b_ + 1)])
    ok, _ = valid(z3.Implies(z3.And(split, split2, Rel(0, bU, P("pk"), P("qk"))(0), Alw(0, bU - 1, P("pi"), H)(0), Alw(0, bU, P("qi"), H)(0)),
                             Rel(0, bU, P("phi"), P("psi"))(0)))
    report("S.release-decide", "(pk R qk) & Alw_[0,2] pi & Alw_[0,3] qi |= phi R_[0,3] psi", ok)
    ok, _ = valid(z3.Implies(z3.And(split, split2, Rel(0, bU, P("pk"), P("qk"))(0), Rel(0, bU, P("pi"), P("qi"))(0)),
                             Rel(0, bU, P("phi"), P("psi"))(0)))
    report("S.release-naive", "(pk R qk) & (pi R qi) |= phi R psi", ok, expect=False)
    # eventually, announce with commit-ahead lambda=2 through latency l=1 to a receiver of delay 1
    lam, lat = 2, 1
    dk = Alw(0, H - lat, lambda t: z3.Implies(B["s"][t], B["f"][t + lat]), H)(0)
    a2, b2 = 2, 4
    dec_ob = z3.Or([z3.And(B["s"][tau - lam], B["pk"][tau]) for tau in range(a2, b2 + 1)])
    rec_ob = z3.And([z3.Implies(B["f"][tau - lam + lat], B["pi"][tau]) for tau in range(a2, b2 + 1)])
    ok, _ = valid(z3.Implies(z3.And(split, dk, dec_ob, rec_ob), Ev(a2, b2, P("phi"), H)(0)))
    report("S.ev-announce-ahead", "Ev_[2,4](prev^2 s & pk) & G(s -> next f) & G_[1,3](f -> next pi) |= Ev_[2,4] phi", ok)
    # guarded response lemma (window budget)
    T = 2
    lhs = z3.And(Alw(0, T, Imp(P("al"), Ev(0, 1, P("be"), H)), H)(0), Alw(0, T + 1, Imp(P("be"), Ev(1, 2, P("ga"), H)), H)(0))
    ok, _ = valid(z3.Implies(lhs, Alw(0, T, Imp(P("al"), Ev(1, 3, P("ga"), H)), H)(0)))
    report("S.GRL", "Alw(al->Ev_[0,1] be) & Alw(be->Ev_[1,2] ga) |= Alw(al->Ev_[1,3] ga)", ok)
    ok, _ = valid(z3.Implies(lhs, Alw(0, T, Imp(P("al"), Ev(1, 2, P("ga"), H)), H)(0)))
    report("S.GRL-budget", "same premises |= Alw(al->Ev_[1,2] ga)  (window smaller than the sum)", ok, expect=False)
    # liveness transfer
    w, k = 2, 1
    ok, _ = valid(z3.Implies(z3.And(Alw(0, 2, Ev(0, w, P("q"), H), H)(0), Alw(0, 2 + w, Imp(P("q"), Ev(0, k, P("p"), H)), H)(0)),
                             Alw(0, 2, Ev(0, w + k, P("p"), H), H)(0)))
    report("S.LT", "Alw Ev_[0,2] q & Alw(q->Ev_[0,1] p) |= Alw Ev_[0,3] p  (liveness transfer)", ok)
    # eventually-always / always-eventually by composition
    ok, _ = valid(z3.Implies(z3.And(split, Ev(0, 2, Alw(0, 2, P("pk"), H), H)(0), Alw(0, 4, P("pi"), H)(0)),
                             Ev(0, 2, Alw(0, 2, P("phi"), H), H)(0)))
    report("S.ev-alw", "Ev Alw pk & Alw_[0,4] pi |= Ev_[0,2] Alw_[0,2] phi", ok)


# ================================================================== [i] EARS chain
def ears():
    print("\n[i] EARS chain: G_[0,2](|r|>0.5 -> F_[0,2] |d|>=0.4), Radio r->m, Display m->d, types |r|,|m|,|d| <= 1")
    T, k, H = 2, 2, 5
    bounds = {"r": 1, "m": 1, "d": 1}
    S = Sig(["r", "m", "d"], H)
    r, m, d = S["r"], S["m"], S["d"]
    ty = types_of(S, bounds)
    trig = lambda t: absgt(r[t], 0.5)
    quiet = lambda t: absle(r[t], 0.2)
    resp = lambda t: absge(d[t], 0.4)
    dquiet = lambda t: absle(d[t], 0.1)
    Fon = lambda t: absge(m[t], 0.5)
    Foff = lambda t: absle(m[t], 0.1)
    G_P = Alw(0, T, Imp(trig, Ev(0, k, resp, H)), H)(0)
    Q = Alw(0, T, Imp(Alw(0, k, quiet, H), Alw(k, k, dquiet, H)), H)(0)       # no response without cause

    def D(dR, dD, sR, sD):
        rad = Alw(0, T, Imp(trig, Ev(dR, dR + sR, Fon, H)), H)(0)
        dis = Alw(0, T + dR + sR, Imp(Fon, Ev(dD, dD + sD, resp, H)), H)(0)
        return rad, dis

    def Dq(dR, dD):
        rad = Alw(0, H - dR, Imp(quiet, Alw(dR, dR, Foff, H)), H)(0)
        dis = Alw(0, H - dD, Imp(Foff, Alw(dD, dD, dquiet, H)), H)(0)
        return rad, dis

    for (dR, dD) in [(0, 0), (1, 1)]:
        slack = k - dR - dD
        print(f"  -- delays (Radio {dR}, Display {dD}); window budget k - sum(delays) = {slack}")
        for sR in range(0, slack + 2):
            for sD in range(0, slack + 2 - sR):
                rad, dis = D(dR, dD, sR, sD)
                ok, mdl = valid(z3.Implies(z3.And(ty, rad, dis), G_P))
                report(f"i.C1 d=({dR},{dD}) s=({sR},{sD})", f"(C1) for G_P with Radio window [{dR},{dR+sR}], Display [{dD},{dD+sD}]",
                       ok, expect=(sR + sD <= slack))
        rad, dis = D(dR, dD, 0, 0); radq, disq = Dq(dR, dD)
        ok, _ = valid(z3.Implies(z3.And(ty, rad, dis, radq, disq), z3.And(G_P, Q)))
        report(f"i.C1Q d=({dR},{dD})", "(C1) for G_P & Q (no spurious response) with on/off flags", ok)
        # realizability: explicit causal strategies, and the receptive-causal sentence by qe2 (cross-checked)
        enc = lambda x: z3.If(x > 0.5, z3.RealVal(1), z3.If(x < -0.5, z3.RealVal(-1), z3.RealVal(0)))
        dec = lambda x: z3.If(x >= 0.5, z3.RealVal(0.5), z3.If(x <= -0.5, z3.RealVal(-0.5), z3.RealVal(0)))
        stratR = {m[t]: (enc(r[t - dR]) if t - dR >= 0 else z3.RealVal(0)) for t in range(H + 1)}
        stratD = {d[t]: (dec(m[t - dD]) if t - dD >= 0 else z3.RealVal(0)) for t in range(H + 1)}
        report(f"i.strat d=({dR},{dD})", "graph(Radio strategy) in S_R and graph(Display strategy) in S_D (with Q parts)",
               graph_in(S, stratR, z3.And(rad, radq), bounds, ["r"]) and graph_in(S, stratD, z3.And(dis, disq), bounds, ["m"]))
        t0 = time.time()
        okR = receptive_causal(S, ["r"], ["m"], dR, z3.And(rad, radq), bounds)
        okD = receptive_causal(S, ["m"], ["d"], dD, z3.And(dis, disq), bounds)
        report(f"i.real d=({dR},{dD})", "receptive & causal (forall-exists sentence, qe2 + default agree)", okR and okD,
               extra=f"{time.time()-t0:.1f}s")
    # the uninformed cover: Display always responds, Radio trivial
    always = Alw(0, H, resp, H)(0)
    ok, _ = valid(z3.Implies(z3.And(ty, always), G_P))
    report("i.cover", "Display 'always |d|>=0.4', Radio trivial: (C1) for G_P alone", ok)
    ok, _ = valid(z3.Implies(z3.And(ty, always), z3.And(G_P, Q)))
    report("i.cover+Q", "same, for G_P & Q", ok, expect=False)
    # latency lower bound: delays (1,1), k=1 < 2 -> no delegation at all for G_P^1 & Q^1 (two-trace argument)
    print("  -- latency lower bound: k=1 < delay sum 2, query G_[0,2](trig->F_[0,1]resp) & G_[0,2](G_[0,1]quiet -> d quiet at +1)")
    k1, H1 = 1, 3
    A_, B_ = Sig(["r", "m", "d"], H1, tag="A"), Sig(["r", "m", "d"], H1, tag="B")

    def query1(X):
        tr = lambda t: absgt(X["r"][t], 0.5); qu = lambda t: absle(X["r"][t], 0.2)
        rs = lambda t: absge(X["d"][t], 0.4); dq = lambda t: absle(X["d"][t], 0.1)
        return z3.And(Alw(0, 2, Imp(tr, Ev(0, k1, rs, H1)), H1)(0), Alw(0, 2, Imp(Alw(0, k1, qu, H1), Alw(k1, k1, dq, H1)), H1)(0))
    rA = [0, 0, 1, 0]; rB = [0, 0, 0, 0]          # agree on r(0), r(1); A triggers at t=2
    env = z3.And([A_["r"][t] == rA[t] for t in range(H1 + 1)] + [B_["r"][t] == rB[t] for t in range(H1 + 1)])
    # with total delay 2, d(tau) depends on r(<= tau-2); for tau <= 3 that is r(<=1), identical in A and B
    share = z3.And([A_["d"][t] == B_["d"][t] for t in range(H1 + 1)])
    ok, _ = sat(z3.And(env, share, query1(A_), query1(B_)))
    report("i.lower", "exists d-values shared by A and B (forced by delay 2) satisfying the query on both", ok, expect=False)
    share0 = z3.And([A_["d"][t] == B_["d"][t] for t in range(2)])      # delay 0: only d(0),d(1) are forced equal
    ok, _ = sat(z3.And(env, share0, query1(A_), query1(B_)))
    report("i.lower-d0", "same two traces with delays (0,0): no contradiction", ok)


def ears3():
    print("\n[i.3] EARS chain of three: Radio r->m (delay 1), Filter m->n (delay 0), Display n->d (delay 1); k=3")
    T, k, H = 2, 3, 6
    bounds = {"r": 1, "m": 1, "n": 1, "d": 1}
    S = Sig(["r", "m", "n", "d"], H)
    r, m, n, d = S["r"], S["m"], S["n"], S["d"]
    ty = types_of(S, bounds)
    trig = lambda t: absgt(r[t], 0.5); quiet = lambda t: absle(r[t], 0.2)
    resp = lambda t: absge(d[t], 0.4); dquiet = lambda t: absle(d[t], 0.1)
    on = lambda x: (lambda t: absge(x[t], 0.5)); off = lambda x: (lambda t: absle(x[t], 0.1))
    G_P = Alw(0, T, Imp(trig, Ev(0, k, resp, H)), H)(0)
    Q = Alw(0, T, Imp(Alw(0, k, quiet, H), Alw(k, k, dquiet, H)), H)(0)
    delays = (1, 0, 1)
    for slack_to in (None, "Filter"):
        sF = (k - sum(delays)) if slack_to == "Filter" else 0
        SR = z3.And(Alw(0, T, Imp(trig, Alw(1, 1, on(m), H)), H)(0), Alw(0, H - 1, Imp(quiet, Alw(1, 1, off(m), H)), H)(0))
        SF = z3.And(Alw(0, T + 1, Imp(on(m), Ev(0, sF, on(n), H)), H)(0), Alw(0, H, Imp(off(m), off(n)), H)(0))
        SD = z3.And(Alw(0, T + 1 + sF, Imp(on(n), Alw(1, 1, resp, H)), H)(0), Alw(0, H - 1, Imp(off(n), Alw(1, 1, dquiet, H)), H)(0))
        ok, _ = valid(z3.Implies(z3.And(ty, SR, SF, SD), G_P))
        okq, _ = valid(z3.Implies(z3.And(ty, SR, SF, SD), Q))
        report(f"i3.C1 slack->{slack_to or 'none'}", "(C1) for G_P and for Q, three-component chain, delay sum 2 <= k=3", ok and okq)
    okR = receptive_causal(S, ["r"], ["m"], 1, SR, bounds)
    okF = receptive_causal(S, ["m"], ["n"], 0, SF, bounds)
    okD = receptive_causal(S, ["n"], ["d"], 1, SD, bounds)
    report("i3.real", "all three receptive & causal", okR and okF and okD)
    SFbad = z3.And(Alw(0, T + 1, Imp(on(m), Ev(0, 2, on(n), H)), H)(0), Alw(0, H, Imp(off(m), off(n)), H)(0))
    SDbad = z3.And(Alw(0, T + 3, Imp(on(n), Alw(1, 1, resp, H)), H)(0), Alw(0, H - 1, Imp(off(n), Alw(1, 1, dquiet, H)), H)(0))
    ok, _ = valid(z3.Implies(z3.And(ty, SR, SFbad, SDbad), G_P))
    report("i3.budget", "Filter takes window [0,2] (budget 1 exceeded)", ok, expect=False)


def ears_tracking():
    print("\n[i.4] EARS + tracking, delays 0: G_P & Q & G_[0,4]|d-r|<=0.5; flags DERIVED from the band |m-r|<=a (no extra capacity)")
    T, k, H = 2, 2, 4
    bounds = {"r": 1, "m": 2, "d": 3}
    S = Sig(["r", "m", "d"], H); r, m, d = S["r"], S["m"], S["d"]; ty = types_of(S, bounds)
    G_P = Alw(0, T, Imp(lambda t: absgt(r[t], 0.5), Ev(0, k, lambda t: absge(d[t], 0.4), H)), H)(0)
    Q = Alw(0, T, Imp(Alw(0, k, lambda t: absle(r[t], 0.2), H), Alw(k, k, lambda t: absle(d[t], 0.1), H)), H)(0)
    TR = Alw(0, H, lambda t: absle(d[t] - r[t], 0.5), H)(0)
    for a, b, exp_real in ((0.1, 0.3, True), (0.2, 0.3, False)):
        SR = Alw(0, H, lambda t: absle(m[t] - r[t], a), H)(0)
        SD = z3.And(Alw(0, H, lambda t: absle(d[t] - m[t], b), H)(0),
                    Alw(0, H, Imp(lambda t: absge(m[t], 0.5 - a), lambda t: absge(d[t], 0.4)), H)(0),
                    Alw(0, H, Imp(lambda t: absle(m[t], 0.2 + a), lambda t: absle(d[t], 0.1)), H)(0))
        ok, _ = valid(z3.Implies(z3.And(ty, SR, SD), z3.And(G_P, Q, TR)))
        report(f"i4.C1 a={a},b={b}", "(C1) for G_P & Q & tracking (sound for any a, b with a+b<=0.5)", ok)
        real = receptive_causal(S, ["r"], ["m"], 0, SR, bounds) and receptive_causal(S, ["m"], ["d"], 0, SD, bounds)
        report(f"i4.real a={a},b={b}", "both receptive (needs on/off flags disjoint: 0.2+a < 0.5-a, and b >= 0.1+a)", real, expect=exp_real)


# ================================================================== [ii] eventually on the relay
def eventually():
    print("\n[ii] relay, H=1, delays 0, types |r|<=1, |m|<=2, |d|<=3; split |m-r|<=a, |d-m|<=b, a=0.2, b=0.3")
    H = 1
    bounds = {"r": 1, "m": 2, "d": 3}
    S = Sig(["r", "m", "d"], H)
    r, m, d = S["r"], S["m"], S["d"]
    ty = types_of(S, bounds)
    a, b = 0.2, 0.3
    pR = lambda t: absle(m[t] - r[t], a)
    pD = lambda t: absle(d[t] - m[t], b)
    # ---- (ii-a) body is one mixed predicate, no data-dependent choice
    print("  (ii-a) G_P = F_[0,1] |d-r|<=0.5, A_P = types")
    G_P = Ev(0, 1, lambda t: absle(d[t] - r[t], 0.5), H)(0)
    modes = {
        "naive (both F)":          (Ev(0, 1, pR, H)(0), Ev(0, 1, pD, H)(0), False),
        "decider Radio":           (Ev(0, 1, pR, H)(0), Alw(0, 1, pD, H)(0), True),
        "decider Display":         (Alw(0, 1, pR, H)(0), Ev(0, 1, pD, H)(0), True),
        "static witness t=0":      (pR(0), pD(0), True),
    }
    for name, (sR, sD, exp) in modes.items():
        ok, mdl = valid(z3.Implies(z3.And(ty, sR, sD), G_P))
        ex = ""
        if mdl is not None:
            ex = "cex " + ", ".join(f"{v}={mdl.eval(x, model_completion=True)}" for v in "rmd" for x in S[v])
        report(f"ii-a.{name}", "(C1)", ok, expect=exp, extra=ex)
        if exp:
            okR = receptive_causal(S, ["r"], ["m"], 0, sR, bounds)
            okD = receptive_causal(S, ["m"], ["d"], 0, sD, bounds)
            report(f"ii-a.{name}.real", "both obligations receptive & causal", okR and okD)
    # announce with a comb flag on m: Display only has to be accurate at flagged times
    comb = lambda t: z3.Or([z3.And(m[t] >= 0.3 * j, m[t] <= 0.3 * j + 0.1) for j in range(-7, 7)])
    sR = Ev(0, 1, lambda t: z3.And(pR(t), comb(t)), H)(0)
    sD = Alw(0, 1, Imp(comb, pD), H)(0)
    ok, _ = valid(z3.Implies(z3.And(ty, sR, sD), G_P))
    report("ii-a.announce(comb)", "(C1) with Radio F(|m-r|<=a & comb(m)), Display G(comb(m) -> |d-m|<=b)", ok)
    okR = receptive_causal(S, ["r"], ["m"], 0, sR, bounds)
    okD = receptive_causal(S, ["m"], ["d"], 0, sD, bounds)
    report("ii-a.announce(comb).real", "both receptive & causal (comb: period 0.3, teeth 0.1 < band width 0.4)", okR and okD)
    sD_strict = Alw(0, 1, pD, H)(0)
    weaker, _ = valid(z3.Implies(z3.And(ty, sD_strict), sD))
    stricter, _ = valid(z3.Implies(z3.And(ty, sD), sD_strict))
    report("ii-a.announce gain", "Display's announced obligation strictly weaker than its cover obligation",
           weaker and not stricter)
    # comb too sparse: no capacity
    comb_bad = lambda t: z3.Or([z3.And(m[t] >= 0.6 * j, m[t] <= 0.6 * j + 0.1) for j in range(-4, 4)])
    sRb = Ev(0, 1, lambda t: z3.And(pR(t), comb_bad(t)), H)(0)
    report("ii-a.sparse comb", "Radio receptive with teeth every 0.6 (gap 0.5 > band width 0.4)",
           receptive_causal(S, ["r"], ["m"], 0, sRb, bounds), expect=False)
    # seed + sweep (fixed-point sweep, theory/foundations.md section 9): D's output is a seed, the sweep maximizes it
    print("  sweep from D's 'decider Radio' seed (fixed-point sweep, foundations section 9), qe2 cross-checked:")
    ports = {"Radio": [r[0], r[1], m[0], m[1]], "Display": [m[0], m[1], d[0], d[1]]}
    allv = S.vars()
    A_P = z3.BoolVal(True)

    def F_i(Sd, i):
        Qf = z3.Or([z3.Not(A_P)] + [z3.Not(Sd[j]) for j in Sd if j != i] + [G_P])
        others = [x for x in allv if not any(x.eq(p) for p in ports[i])]
        return qe(z3.ForAll(others, z3.Implies(ty, Qf)))
    seed = {"Radio": Ev(0, 1, pR, H)(0), "Display": Alw(0, 1, pD, H)(0)}
    t0 = time.time()
    cur = dict(seed)
    for i in ["Display", "Radio"]:
        cur[i] = F_i(cur, i)
    v_ok, _ = valid(z3.Implies(z3.And(ty, cur["Radio"], cur["Display"]), G_P))
    grew = all(valid(z3.Implies(z3.And(ty, seed[i]), cur[i]))[0] for i in seed)
    fixed = all(valid(z3.Implies(ty, cur[i] == F_i(cur, i)))[0] for i in cur)
    report("ii-a.sweep", "sweep (Display, Radio) from D seed: valid, grew, fixed point", v_ok and grew and fixed,
           extra=f"{time.time()-t0:.1f}s")
    # Display still has to be accurate at both times on central inputs (the decider structure survives maximization)
    ok, _ = valid(z3.Implies(z3.And(ty, absle(m[0], 0.5), absle(m[1], 0.5), cur["Display"]), z3.And(pD(0), pD(1))))
    report("ii-a.sweep shape", "after the sweep Display still obeys |d-m|<=0.3 at BOTH times for |m|<=0.5", ok)

    # ---- (ii-b) the witness must be a time where r is small: the choice depends on data
    print("  (ii-b) G_P = F_[0,1](|r|<=0.5 & |d-r|<=0.5), A_P = types & F_[0,1] |r|<=0.5")
    small = lambda t: absle(r[t], 0.5)
    A_P = Ev(0, 1, small, H)(0)
    G_P = Ev(0, 1, lambda t: z3.And(small(t), absle(d[t] - r[t], 0.5)), H)(0)
    modes = {
        "naive (both F)":   (Ev(0, 1, lambda t: z3.And(small(t), pR(t)), H)(0), Ev(0, 1, pD, H)(0), False),
        "decider Radio":    (Ev(0, 1, lambda t: z3.And(small(t), pR(t)), H)(0), Alw(0, 1, pD, H)(0), True),
        "decider Display (derived guard |m|<=0.5-a)":
                            (Alw(0, 1, pR, H)(0), Ev(0, 1, lambda t: z3.And(absle(m[t], 0.5 - a), pD(t)), H)(0), True),
        "static witness t=0": (z3.And(small(0), pR(0)), pD(0), True),
    }
    for name, (sR, sD, exp) in modes.items():
        ok, mdl = valid(z3.Implies(z3.And(ty, A_P, sR, sD), G_P))
        ex = ""
        if mdl is not None:
            ex = "cex " + ", ".join(f"{v}={mdl.eval(x, model_completion=True)}" for v in "rmd" for x in S[v])
        report(f"ii-b.{name}", "(C1)", ok, expect=exp, extra=ex)
    sR, sD, _ = modes["decider Radio"]
    report("ii-b.decider Radio.real", "Radio receptive & causal on A_P, Display receptive & causal",
           receptive_causal(S, ["r"], ["m"], 0, sR, bounds, assumption=A_P) and receptive_causal(S, ["m"], ["d"], 0, sD, bounds))
    sR, sD, _ = modes["decider Display (derived guard |m|<=0.5-a)"]
    reach = z3.And(ty, A_P, sR, m[0] == 0.6, m[1] == 0.6)
    ok1, _ = sat(reach)
    ok2, _ = sat(z3.And(ty, m[0] == 0.6, m[1] == 0.6, sD))
    report("ii-b.decider Display.real", "input m=(0.6,0.6) reachable under A_P & S_R, and S_D has no output there",
           ok1 and not ok2)
    sR, sD, _ = modes["static witness t=0"]
    report("ii-b.static.real", "static-witness Radio obligation receptive on A_P",
           receptive_causal(S, ["r"], ["m"], 0, sR, bounds, assumption=A_P), expect=False)


# ================================================================== [iii] information fork
def fork():
    print("\n[iii] information fork, H=0: C1 reads x writes u; C2 reads y writes v; types all |.|<=1")
    x, y, u, v = z3.Reals("x y u v")
    bounds = {"x": 1, "y": 1, "u": 1, "v": 1}

    def G(x, y, u, v):
        Pp = z3.And(u >= 0.5, v >= 0.5); Pm = z3.And(u <= -0.5, v <= -0.5)
        Ep = z3.And(x >= 0.5, y >= 0.5); Em = z3.And(x <= -0.5, y <= -0.5)
        return z3.And(z3.Or(Pp, Pm), z3.Implies(Ep, Pp), z3.Implies(Em, Pm))
    ty_env = z3.And(absle(x, 1), absle(y, 1)); ty_out = z3.And(absle(u, 1), absle(v, 1))
    # (a) agreement lemma, finite sample: u = f(x), v = g(y) on x,y in {-1,1}
    f = {s: z3.Real(f"f_{s}") for s in (-1, 1)}; g = {s: z3.Real(f"g_{s}") for s in (-1, 1)}
    cons = z3.And([G(sx, sy, f[sx], g[sy]) for sx in (-1, 1) for sy in (-1, 1)] +
                  [absle(f[s], 1) for s in f] + [absle(g[s], 1) for s in g])
    ok, _ = sat(cons)
    report("iii.fork", "exist f(+-1), g(+-1) with G on all four (x,y) in {-1,1}^2  (necessary for ANY delegation)", ok, expect=False)
    # (b) centralized: one component sees x and y
    ok = decide_sentence(z3.ForAll([x, y], z3.Implies(ty_env, z3.Exists([u, v], z3.And(ty_out, G(x, y, u, v))))))
    report("iii.central", "forall x,y exists u,v G  (realizable by one component seeing both)", ok)
    # (c) D's candidate annotations over the fork: all fail
    S1p, S2p = z3.And(u >= 0.5), z3.And(v >= 0.5)
    ok, _ = valid(z3.Implies(z3.And(ty_env, ty_out, S1p, S2p), G(x, y, u, v)))
    report("iii.D static(+)", "(C1) for static branch +", ok, expect=False)
    S1 = z3.Or(z3.And(x > -0.5, u >= 0.5), z3.And(x < 0.5, u <= -0.5))
    S2 = z3.And(v >= 0.5, v <= -0.5)
    report("iii.D decide(C1), C2 covers", "C2's cover obligation v>=0.5 & v<=-0.5 satisfiable", sat(S2)[0], expect=False)
    # (d) add an edge C1 -> C2 (C2 reads u): decider C1, the flag is the sign region of u itself
    S2e = z3.And(z3.Implies(u >= 0.5, v >= 0.5), z3.Implies(u <= -0.5, v <= -0.5))
    ok, _ = valid(z3.Implies(z3.And(ty_env, ty_out, S1, S2e), G(x, y, u, v)))
    report("iii.edge C1", "(C1) with C1: (x>-0.5 & u>=0.5) | (x<0.5 & u<=-0.5), C2: (u>=0.5->v>=0.5) & (u<=-0.5->v<=-0.5)", ok)
    r1 = decide_sentence(z3.ForAll([x], z3.Implies(absle(x, 1), z3.Exists([u], z3.And(absle(u, 1), S1)))))
    r2 = decide_sentence(z3.ForAll([u, y], z3.Implies(z3.And(absle(u, 1), absle(y, 1)), z3.Exists([v], z3.And(absle(v, 1), S2e)))))
    report("iii.edge real", "both receptive", r1 and r2)
    ok = decide_sentence(z3.ForAll([x], z3.Implies(absle(x, 1), z3.Exists([u], z3.And(absle(u, 1),
                         z3.ForAll([y], z3.Implies(absle(y, 1), z3.Exists([v], z3.And(absle(v, 1), G(x, y, u, v))))))))))
    report("iii.alternation", "forall x exists u forall y exists v G (the edge architecture's game)", ok)
    # the fork's game is a Henkin quantifier (u may not see y, v may not see x); the 'exists u forall y' order
    # with v blind to x is what (a) refutes. Show the FO prefix where u must be chosen before x is known fails too:
    ok = decide_sentence(z3.Exists([u], z3.And(absle(u, 1), z3.ForAll([x, y], z3.Implies(ty_env,
                         z3.Exists([v], z3.And(absle(v, 1), G(x, y, u, v))))))))
    report("iii.u-blind", "exists u forall x,y exists v G  (C1 blind: constant u)", ok, expect=False)


# ================================================================== [iv] temporal assumption flow
def assumptions():
    print("\n[iv] temporal assumption: A_P = G_[0,1] F_[0,1] |r|<=0.2 (env rests), relay with delays 0, H=3")
    H = 3
    bounds = {"r": 1, "m": 1, "d": 1}
    S = Sig(["r", "m", "d"], H)
    r, m, d = S["r"], S["m"], S["d"]
    ty = types_of(S, bounds)
    quiet = lambda t: absle(r[t], 0.2); busy = lambda t: absge(r[t], 0.5)
    rest = lambda t: absle(d[t], 0.1); act = lambda t: absge(d[t], 0.4)
    A_P = Alw(0, 1, Ev(0, 1, quiet, H), H)(0)
    G_P = z3.And(Alw(0, 1, Ev(0, 2, rest, H), H)(0), Alw(0, H, Imp(busy, act), H)(0))
    # D: liveness transfer rewrites the liveness conjunct into a response conjunct G_[0,2](quiet -> F_[0,1] rest);
    # D then delegates it as an EARS chain with flag |m|<=0.1 (static witness 0 at each leg)
    SR = z3.And(Alw(0, 2, Imp(quiet, lambda t: absle(m[t], 0.1)), H)(0), Alw(0, H, Imp(busy, lambda t: absge(m[t], 0.5)), H)(0))
    SD = z3.And(Alw(0, 2, Imp(lambda t: absle(m[t], 0.1), rest), H)(0), Alw(0, H, Imp(lambda t: absge(m[t], 0.5), act), H)(0))
    ok, _ = valid(z3.Implies(z3.And(ty, A_P, SR, SD), G_P))
    report("iv.C1", "(C1) for the liveness query via liveness transfer + EARS chain", ok)
    always_rest = Alw(0, H, rest, H)(0)
    ok, _ = valid(z3.Implies(z3.And(ty, A_P, always_rest), G_P))
    report("iv.cover", "Display 'always rest' alone", ok, expect=False)
    # assumptions solved last: A_D = shadow of A_P & S_R onto in(Display) = m
    t0 = time.time()
    rv = [r[t] for t in range(H + 1)]
    tyr = z3.And([absle(x, 1) for x in rv])
    shadow = qe(z3.Exists(rv, z3.And(tyr, A_P, SR)))
    fwd = Alw(0, 1, Ev(0, 1, lambda t: absle(m[t], 0.1), H), H)(0)      # forward image: liveness flows through the flag
    tym = z3.And([absle(m[t], 1) for t in range(H + 1)])
    c2, _ = valid(z3.Implies(z3.And(ty, A_P, SR), fwd))
    report("iv.C2 fwd", "(C2): A_P & S_R |= forward assumption G_[0,1]F_[0,1]|m|<=0.1", c2)
    eq, _ = valid(z3.Implies(tym, shadow == fwd))
    report("iv.shadow=fwd", "shadow pi_m(A_P & S_R) equals the forward image (on typed m)", eq, extra=f"qe2 {time.time()-t0:.1f}s")
    # downstream obligations do not change an upstream-fed shadow (Display receptive, downstream of m)
    dv = [d[t] for t in range(H + 1)]
    shadow2 = qe(z3.Exists(rv + dv, z3.And(tyr, z3.And([absle(x, 1) for x in dv]), A_P, SR, SD)))
    eq2, _ = valid(z3.Implies(tym, shadow == shadow2))
    report("iv.ancestors", "pi_m(A_P & S_R & S_D) == pi_m(A_P & S_R)  (only ancestors shape A_D)", eq2)
    # Display's contract with that assumption: (A_D, G_D) with G_D = S_D; (C1) still holds with saturated S_D'
    SDc = z3.Implies(fwd, SD)
    ok, _ = valid(z3.Implies(z3.And(ty, A_P, SR, SDc), G_P))
    report("iv.contract", "(C1) with Display's contract (A_D=fwd, G_D=S_D) saturated", ok)
    report("iv.A_R", "Radio's assumption: pi_r(A_P & S_D) == A_P (Display receptive, not an ancestor)",
           valid(z3.Implies(tyr, qe(z3.Exists([m[t] for t in range(H + 1)] + dv,
                                               z3.And(tym, z3.And([absle(x, 1) for x in dv]), A_P, SD))) == A_P))[0])


# ================================================================== [D] an interpreter of the table of D (unrolled form)
# Formula tree (NNF).  Leaves: Own (an atom already split: component -> local part at time t) and
# Env (an environment formula with a certificate: component -> local guard at time t that implies it).
# Disjunctive nodes carry a name; the annotation maps names to modes:
#   ("stat", j)                         branch j (for Ev/Until: relative offset)
#   ("dec", k, J)                       decider k over the branch subset J (None = all); others cover J
#   ("ann", k, J, sigma, recv, relays)  decider k raises sigma(j,t) (over out(k)); receiver i assumes recv[i](j,t)
#                                       (over in(i)); relays[c](t) are extra local obligations carrying the flag
class Own:
    def __init__(self, parts): self.parts = parts                # comp -> (t -> expr)
class Env:
    def __init__(self, phi, cert): self.phi, self.cert = phi, cert   # phi: t -> expr ; cert: comp -> (t -> expr)
class AndN:
    def __init__(self, *ch): self.ch = ch
class AlwN:
    def __init__(self, a, b, ch): self.a, self.b, self.ch = a, b, ch
class OrN:
    def __init__(self, name, *ch): self.name, self.ch = name, ch
class EvN:
    def __init__(self, name, a, b, ch): self.name, self.a, self.b, self.ch = name, a, b, ch
class UntilN:
    def __init__(self, name, a, b, c1, c2): self.name, self.a, self.b, self.c1, self.c2 = name, a, b, c1, c2


def _conj(ds):
    out = {}
    for dct in ds:
        for c, e in dct.items():
            out[c] = z3.And(out[c], e) if c in out else e
    return out


def D(node, t, kappa, comps, side):
    """Returns {comp: local obligation at evaluation time t}; appends delivery/certificate side conditions to side."""
    if isinstance(node, Own):
        return {c: f(t) for c, f in node.parts.items()}
    if isinstance(node, Env):
        side.append(("cert", z3.Implies(z3.And([g(t) for g in node.cert.values()]), node.phi(t))))
        return {c: g(t) for c, g in node.cert.items()}
    if isinstance(node, AndN):
        return _conj([D(ch, t, kappa, comps, side) for ch in node.ch])
    if isinstance(node, AlwN):
        return _conj([D(node.ch, t + s, kappa, comps, side) for s in range(node.a, node.b + 1)])
    if isinstance(node, OrN):
        branches = {j: D(ch, t, kappa, comps, side) for j, ch in enumerate(node.ch)}
    elif isinstance(node, EvN):
        branches = {tau: D(node.ch, t + tau, kappa, comps, side) for tau in range(node.a, node.b + 1)}
    elif isinstance(node, UntilN):
        branches = {tau: _conj([D(node.c2, t + tau, kappa, comps, side)] +
                               [D(node.c1, t + s, kappa, comps, side) for s in range(tau)]) for tau in range(node.a, node.b + 1)}
    else:
        raise TypeError(node)
    mode = kappa[node.name]
    part = lambda j, c: branches[j].get(c, z3.BoolVal(True))
    if mode[0] == "stat":
        return dict(branches[mode[1]])
    k, J = mode[1], (mode[2] if mode[2] is not None else list(branches))
    if mode[0] == "dec":
        out = {c: z3.And([part(j, c) for j in J]) for c in comps if c != k}
        out[k] = z3.Or([part(j, k) for j in J])
        return out
    if mode[0] == "ann":
        sigma, recv, relays = mode[3], mode[4], mode[5]
        out = {}
        for c in comps:
            if c == k:
                out[c] = z3.Or([z3.And(part(j, k), sigma(j, t)) for j in J])
            elif c in recv:
                out[c] = z3.And([z3.Implies(recv[c](j, t), part(j, c)) for j in J])
            else:
                out[c] = z3.And([part(j, c) for j in J])
        rel = {c: f(t) for c, f in relays.items()}
        for j in J:
            for c in recv:
                side.append(("deliver", z3.Implies(z3.And([sigma(j, t)] + list(rel.values())), recv[c](j, t))))
        return _conj([out, rel])
    raise ValueError(mode)


def run_D(node, kappa, comps, ctx):
    side = []
    out = D(node, 0, kappa, comps, side)
    ok = all(valid(z3.Implies(ctx, sc))[0] for _, sc in side)
    return {c: out.get(c, z3.BoolVal(True)) for c in comps}, ok


def auto():
    print("\n[D] the table of D run mechanically (unrolled interpreter) on the three examples; outputs compared to the hand-derived ones")
    # ---- (i) EARS chain, both delay settings, G_P & Q
    T, k, H = 2, 2, 5
    bounds = {"r": 1, "m": 1, "d": 1}
    S = Sig(["r", "m", "d"], H); r, m, d = S["r"], S["m"], S["d"]; ty = types_of(S, bounds)
    for (dR, dD) in [(0, 0), (1, 1)]:
        Dl = dR + dD
        trig = lambda t: absgt(r[t], 0.5)
        resp = Own({"Display": lambda t: absge(d[t], 0.4)})
        dq = Own({"Display": lambda t: absle(d[t], 0.1)})
        # G_P: Alw_[0,T]( not trig  OR  Ev_[0,k] resp ); env branch certified by Radio; inner Ev decided by Display
        GP = AlwN(0, T, OrN("trig", Env(lambda t: z3.Not(trig(t)), {"Radio": lambda t: z3.Not(trig(t))}),
                                    EvN("resp", 0, k, resp)))
        # Q: Alw_[0,T]( not Alw_[0,k] quiet OR d quiet at +k ); guard weakened to the causally visible sample t+k-Dl
        GQ = AlwN(0, T, OrN("quiet", Env(lambda t: z3.Not(z3.And([absle(r[t + s], 0.2) for s in range(k + 1)])),
                                         {"Radio": lambda t: z3.Not(absle(r[t + k - Dl], 0.2))}),
                                     AlwN(k, k, dq)))
        kappa = {
            "trig": ("ann", "Radio", None, lambda j, t: (absge(m[t + dR], 0.5) if j == 1 else z3.BoolVal(True)),
                     {"Display": lambda j, t: (absge(m[t + dR], 0.5) if j == 1 else z3.BoolVal(True))}, {}),
            "resp": ("stat", Dl),                     # earliest causal witness (preference P0)
            "quiet": ("ann", "Radio", None, lambda j, t: (absle(m[t + k - dD], 0.1) if j == 1 else z3.BoolVal(True)),
                      {"Display": lambda j, t: (absle(m[t + k - dD], 0.1) if j == 1 else z3.BoolVal(True))}, {}),
        }
        out, side_ok = run_D(AndN(GP, GQ), kappa, ["Radio", "Display"], ty)
        G_P = Alw(0, T, Imp(trig, Ev(0, k, lambda t: absge(d[t], 0.4), H)), H)(0)
        Q = Alw(0, T, Imp(Alw(0, k, lambda t: absle(r[t], 0.2), H), Alw(k, k, lambda t: absle(d[t], 0.1), H)), H)(0)
        c1, _ = valid(z3.Implies(z3.And(ty, out["Radio"], out["Display"]), z3.And(G_P, Q)))
        hand_R = z3.And(Alw(0, T, Imp(trig, Alw(dR, dR, lambda t: absge(m[t], 0.5), H)), H)(0),
                        Alw(k - Dl, T + k - Dl, Imp(lambda t: absle(r[t], 0.2), Alw(dR, dR, lambda t: absle(m[t], 0.1), H)), H)(0))
        hand_D = z3.And(Alw(dR, T + dR, Imp(lambda t: absge(m[t], 0.5), Alw(dD, dD, lambda t: absge(d[t], 0.4), H)), H)(0),
                        Alw(k - dD, T + k - dD, Imp(lambda t: absle(m[t], 0.1), Alw(dD, dD, lambda t: absle(d[t], 0.1), H)), H)(0))
        same = valid(z3.Implies(ty, z3.And(out["Radio"] == hand_R, out["Display"] == hand_D)))[0]
        real = receptive_causal(S, ["r"], ["m"], dR, out["Radio"], bounds) and receptive_causal(S, ["m"], ["d"], dD, out["Display"], bounds)
        report(f"D.i d=({dR},{dD})", "auto-D: side conditions, (C1) for G_P&Q, equals hand obligations, realizable",
               side_ok and c1 and same and real)
    # ---- (ii-b) relay eventually with data-dependent witness
    H = 1; bounds = {"r": 1, "m": 2, "d": 3}
    S = Sig(["r", "m", "d"], H); r, m, d = S["r"], S["m"], S["d"]; ty = types_of(S, bounds)
    small = lambda t: absle(r[t], 0.5); a, b = 0.2, 0.3
    split = Own({"Radio": lambda t: absle(m[t] - r[t], a), "Display": lambda t: absle(d[t] - m[t], b)})
    A_P = Ev(0, 1, small, H)(0)
    G_P = Ev(0, 1, lambda t: z3.And(small(t), absle(d[t] - r[t], 0.5)), H)(0)
    for dec, cert, exp_real in (("Radio", {"Radio": small}, True), ("Display", {"Display": lambda t: absle(m[t], 0.5 - a)}, False)):
        node = EvN("w", 0, 1, AndN(Env(small, cert), split))
        out, side_ok = run_D(node, {"w": ("dec", dec, None)}, ["Radio", "Display"], z3.And(ty, A_P) if dec == "Radio" else z3.And(ty, A_P, out_R_cover(m, r, a)))
        c1, _ = valid(z3.Implies(z3.And(ty, A_P, out["Radio"], out["Display"]), G_P))
        if exp_real:
            real = receptive_causal(S, ["r"], ["m"], 0, out["Radio"], bounds, assumption=A_P) and receptive_causal(S, ["m"], ["d"], 0, out["Display"], bounds)
        else:
            real = sat(z3.And(ty, m[0] == 0.6, m[1] == 0.6, out["Display"]))[0]
        report(f"D.ii-b dec({dec}) sound", "auto-D: side conditions & (C1) hold", side_ok and c1)
        report(f"D.ii-b dec({dec}) real", "realizable" if exp_real else "Display has an output at reachable m=(0.6,0.6)",
               real, expect=exp_real)
    # ---- (iii) fork: enumerate all annotations without edge; one annotation with the edge
    x, y, u, v = z3.Reals("x y u v")
    tyf = z3.And(absle(x, 1), absle(y, 1), absle(u, 1), absle(v, 1))
    Pp = Own({"C1": lambda t: u >= 0.5, "C2": lambda t: v >= 0.5}); Pm = Own({"C1": lambda t: u <= -0.5, "C2": lambda t: v <= -0.5})
    nEp = lambda cert: Env(lambda t: z3.Or(x < 0.5, y < 0.5), cert)
    nEm = lambda cert: Env(lambda t: z3.Or(x > -0.5, y > -0.5), cert)
    Gf = z3.And(z3.Or(z3.And(u >= 0.5, v >= 0.5), z3.And(u <= -0.5, v <= -0.5)),
                z3.Implies(z3.And(x >= 0.5, y >= 0.5), z3.And(u >= 0.5, v >= 0.5)),
                z3.Implies(z3.And(x <= -0.5, y <= -0.5), z3.And(u <= -0.5, v <= -0.5)))

    def recv_ok(comp, ob):
        inp, outv = ({"C1": (x, u), "C2": (y, v)})[comp]
        return decide_sentence(z3.ForAll([inp], z3.Implies(absle(inp, 1), z3.Exists([outv], z3.And(absle(outv, 1), ob)))))
    n_ok, n_tot = 0, 0
    for c2cert, c3cert in itertools.product(("C1", "C2"), repeat=2):
        tree = AndN(OrN("agree", Pp, Pm),
                    OrN("plus", nEp({c2cert: (lambda t: x < 0.5) if c2cert == "C1" else (lambda t: y < 0.5)}), Pp),
                    OrN("minus", nEm({c3cert: (lambda t: x > -0.5) if c3cert == "C1" else (lambda t: y > -0.5)}), Pm))
        modes = [("stat", 0), ("stat", 1), ("dec", "C1", None), ("dec", "C2", None)]
        for m1, m2, m3 in itertools.product(modes, repeat=3):
            out, side_ok = run_D(tree, {"agree": m1, "plus": m2, "minus": m3}, ["C1", "C2"], tyf)
            n_tot += 1
            sound = valid(z3.Implies(z3.And(tyf, out["C1"], out["C2"]), Gf))[0]
            assert sound or not side_ok, "D produced an unsound delegation"
            if recv_ok("C1", out["C1"]) and recv_ok("C2", out["C2"]):
                n_ok += 1
    report("D.iii fork", f"auto-D over all {n_tot} annotations (stat/dec at 3 nodes x 4 certificate choices): every output sound; realizable ones",
           n_ok, expect=0)
    # with the edge C1 -> C2: decider C1 at all three nodes, flag = sign region of u (derived), receiver C2
    sig = lambda j, t: z3.BoolVal(True)
    tree = AndN(OrN("agree", Pp, Pm), OrN("plus", nEp({"C1": lambda t: x < 0.5}), Pp), OrN("minus", nEm({"C1": lambda t: x > -0.5}), Pm))
    kappa = {"agree": ("ann", "C1", None, sig, {"C2": lambda j, t: (u >= 0.5) if j == 0 else (u <= -0.5)}, {}),
             "plus": ("ann", "C1", None, sig, {"C2": lambda j, t: z3.BoolVal(True) if j == 0 else (u >= 0.5)}, {}),
             "minus": ("ann", "C1", None, sig, {"C2": lambda j, t: z3.BoolVal(True) if j == 0 else (u <= -0.5)}, {})}
    # the flag is derived: sigma = true because the decider's own branch part already sets the sign of u;
    # delivery is then 'branch part of C1 |= receiver guard', checked here directly
    out, side_ok = run_D(tree, kappa, ["C1", "C2"], tyf)
    # side_ok (sigma=true |= guard) fails by design for a derived flag; the real delivery premise is the decider's branch part
    deliver = all(valid(z3.Implies(tyf, z3.Implies(p, g)))[0] for p, g in ((u >= 0.5, u >= 0.5), (u <= -0.5, u <= -0.5)))
    c1 = valid(z3.Implies(z3.And(tyf, out["C1"], out["C2"]), Gf))[0]
    report("D.iii edge", "auto-D with decider C1 and derived flag: delivery, (C1), both receptive",
           deliver and c1 and recv_ok("C1", out["C1"]) and decide_sentence(z3.ForAll([u, y], z3.Implies(z3.And(absle(u, 1), absle(y, 1)), z3.Exists([v], z3.And(absle(v, 1), out["C2"]))))))


def out_R_cover(m, r, a):
    """Radio's cover obligation when Display decides in (ii-b): it relays at both times (used as the context
    in which Display's derived guard |m|<=0.5-a certifies |r|<=0.5)."""
    return z3.And([absle(m[t] - r[t], a) for t in range(len(m))])


if __name__ == "__main__":
    t_all = time.time()
    schemas()
    ears()
    ears3()
    ears_tracking()
    eventually()
    fork()
    assumptions()
    auto()
    n_fail = sum(1 for _, s in RESULTS if s == "FAIL")
    print(f"\n{len(RESULTS)} checks, {n_fail} failed, {time.time()-t_all:.1f}s total")
