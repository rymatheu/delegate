#!/usr/bin/env python3
"""The procedure of docs/complete.tex, executable.  Run from the directory root:

    .venv/bin/python scripts/delegate.py

Every step prints what it computes.  Only z3 is needed; its version is printed first, because the clause order
inside printed formulas, and the atoms from which witnesses are built after the first elimination, are those of
Z3's simplifier and of its qe2 tactic.  Set DELEGATE_TRACE=1 to also print, for every witness, the formula it is
built from and its ordered candidate list (see `witness`).  The exit code is 0 iff every verdict is as expected."""
import itertools, os, sys
from fractions import Fraction
from z3 import *

TRACE = bool(os.environ.get("DELEGATE_TRACE"))

# ---------- tiny PolySTL layer: formulas over symbols v_t (value of v at time t) ----------
SYM = {}
def V(v, t):
    k = f"{v}_{t}"
    if k not in SYM: SYM[k] = Real(k)
    return SYM[k]
def Alw(a, b, f):        # f: t -> z3 formula ; returns formula at time 0 for horizon window
    return lambda t: And([f(t + s) for s in range(a, b + 1)])
def Ev(a, b, f):
    return lambda t: Or([f(t + s) for s in range(a, b + 1)])
def absle(e, c): return And(e <= c, -e <= c)

def qe(f):
    """Quantifier elimination, cross-checked.  Z3's model-based tactic 'qe2' eliminates the quantifiers of f; the
    result g is accepted only if Z3's default solver proves f <-> g (Not(f == g) unsatisfiable; this solver is
    sound, and 'unknown' is not accepted), or failing that if Then('qe2','smt') decides Not(f == g) to be false.
    Z3 5.3.1's virtual-substitution tactic 'qe' is NOT used: on the speed-governor Actuator step it returned a
    non-equivalent formula (too strong), and a cross-check built on 'qe' itself confirmed it (regression 5 below).
    The trust base is Z3's default solver on linear real arithmetic with the quantifiers of Not(f == g); the final
    (V1), (V2), receptiveness and causality verdicts of the emitted contracts are checked separately."""
    g = simplify(Tactic('qe2')(f).as_expr())
    if 'ForAll' in str(g) or 'Exists' in str(g): raise AssertionError("qe2 left quantifiers")
    s = Solver(); s.set("timeout", 300000); s.add(Not(f == g))
    if s.check() == unsat: return g
    if is_false(Then('qe2', 'smt')(Not(f == g)).as_expr()): return g
    raise AssertionError("quantifier elimination could not be cross-checked")
def valid(f):
    s = Solver(); s.add(Not(f)); return s.check() == unsat
def fmt(f): return str(simplify(f)).replace("\n", " ")

# ---------- architecture ----------
class Arch:
    def __init__(self, comps, env, H):
        self.comps, self.env, self.H = comps, env, H       # comps: name -> (inputs, outputs)
        self.writer = {v: c for c, (i, o) in comps.items() for v in o}
    def ports(self, c):
        i, o = self.comps[c]; return set(i) | set(o)
    def edges(self):
        return {(self.writer[v], c) for c, (i, o) in self.comps.items() for v in i if v in self.writer}
    def support(self, GP_vars):
        """N: writers of a variable of G_P, and every component with a directed path to one of them."""
        N = {self.writer[v] for v in GP_vars if v in self.writer}
        changed = True
        while changed:
            changed = False
            for (u, w) in self.edges():
                if w in N and u not in N: N.add(u); changed = True
        return N
    def topo_orders(self, N):
        """Topological orderings of N: permutations of sorted(N) in lexicographic order, filtered."""
        E = {(u, w) for (u, w) in self.edges() if u in N and w in N}
        for perm in itertools.permutations(sorted(N)):
            pos = {c: i for i, c in enumerate(perm)}
            if all(pos[u] < pos[w] for (u, w) in E): yield list(perm)

def syms_of(f):
    """The free symbols (timed variables) of a Z3 term or formula, found by traversing the term."""
    out = {}; seen = set()
    def walk(e):
        i = e.get_id()
        if i in seen: return
        seen.add(i)
        if is_const(e) and e.decl().kind() == Z3_OP_UNINTERPRETED: out[str(e)] = e
        for ch in e.children(): walk(ch)
    walk(f); return out
def vars_of(f):
    """The variables v (not the timed variables v_t) mentioned by f."""
    return {s.rsplit("_", 1)[0] for s in syms_of(f)}

# ---------- affine expressions, exact and canonical ----------
def affine(e):
    """Exact affine form of a linear Z3 real term: (dict timed-variable name -> Fraction, Fraction constant)."""
    if is_rational_value(e): return {}, Fraction(e.as_fraction())
    k = e.decl().kind()
    if is_const(e) and k == Z3_OP_UNINTERPRETED: return {str(e): Fraction(1)}, Fraction(0)
    ch = [affine(c) for c in e.children()]
    def lin(pairs):                                        # sum of (scale, (coeffs, const))
        co, c0 = {}, Fraction(0)
        for s, (cf, cc) in pairs:
            for n, a in cf.items(): co[n] = co.get(n, Fraction(0)) + s * a
            c0 += s * cc
        return {n: a for n, a in co.items() if a != 0}, c0
    if k == Z3_OP_ADD: return lin([(1, x) for x in ch])
    if k == Z3_OP_SUB: return lin([(1, ch[0])] + [(-1, x) for x in ch[1:]])
    if k == Z3_OP_UMINUS: return lin([(-1, ch[0])])
    if k == Z3_OP_TO_REAL: return ch[0]
    if k == Z3_OP_MUL:
        acc = ({}, Fraction(1))
        for x in ch:
            if not acc[0]: acc = lin([(acc[1], x)])
            elif not x[0]: acc = lin([(x[1], acc)])
            else: raise ValueError(f"nonlinear term {e}")
        return acc
    if k == Z3_OP_DIV and not ch[1][0] and ch[1][1] != 0: return lin([(1 / ch[1][1], ch[0])])
    raise ValueError(f"not an affine term: {e}")
def canon(aff):
    """Canonical printing of an affine expression: the terms `c*v` for the timed variables v with a nonzero
    coefficient c, in alphabetical order of v, then the constant term; numbers as reduced fractions p/q (integers
    without /1); joined by ' + '.  Example: r_0 - 3/8 prints as '1*r_0 + -3/8', and 2 r_0 as '2*r_0 + 0'."""
    co, c0 = aff
    return " + ".join([f"{co[n]}*{n}" for n in sorted(co)] + [str(c0)])
def term_of(aff):
    co, c0 = aff
    return simplify(Sum([RealVal(c0)] + [RealVal(co[n]) * SYM[n] for n in sorted(co)]))

# ---------- witness for one existential timed variable (Lemma: elimination with witnesses) ----------
ATOM_KINDS = (Z3_OP_LE, Z3_OP_LT, Z3_OP_GE, Z3_OP_GT, Z3_OP_EQ, Z3_OP_DISTINCT)
def witness(R, y):
    """Witness s_y for `exists y. R`: an if-then-else term with (exists y. R) -> R[y:=s_y] valid (asserted).

    Bounds.  The formula R is first put through Z3's simplify.  Its atoms are visited in the order Z3 presents them
    (depth first, left to right).  Every atom  lhs ~ rhs  in which y has a nonzero coefficient a, after writing
    lhs - rhs exactly as  a*y + rest  with rest affine, contributes the bound  -rest/a  (the value of y at which the
    atom holds with equality).  Bounds that are the same affine expression are kept once, at their first occurrence.

    Candidates.  Five tiers, in this order:
      1. the midpoints (b_i + b_j)/2 of all pairs of distinct bounds,
      2. the bounds b_i,
      3. the bounds plus one, b_i + 1,
      4. the bounds minus one, b_i - 1,
      5. the constant 0.
    Within a tier the candidates are sorted: first those whose value is a constant, by increasing absolute value,
    and a negative constant before the positive constant of the same absolute value; then the non-constant ones,
    in increasing character-code (ASCII) order of their canonical printing (see `canon`: alphabetical variables,
    reduced fractions, e.g. '1*r_0 + -3/8' < '1*r_0 + 3/8' < '2*r_0 + 0').  A candidate equal (as an affine
    expression) to one met earlier in this list is dropped.  So the order of the bounds affects nothing but the
    duplicates, and the list depends only on the set of bounds.

    Witness.  s_y = If(R[y:=c_1], c_1, If(R[y:=c_2], c_2, ... If(R[y:=c_n], c_n, 0))): the first candidate, in the
    order above, at which R holds, and 0 if there is none.

    To reproduce a witness by hand a reader needs: (i) the formula R exactly as the script passes it; for the first
    elimination this is simplify(A_P -> G_P), and after that it is the output of Z3's qe2 tactic on the previous
    quantifier, simplified, so it depends on the Z3 version printed at the top (DELEGATE_TRACE=1 prints R and the
    candidate list for every witness); (ii) the bounds of its atoms, as above; (iii) the order above; (iv) for each
    candidate, the formula R[y:=c].  Nothing else enters."""
    R = simplify(R); yn = str(y)
    bounds = []; seen = set()
    def walk(e):
        i = e.get_id()
        if i in seen: return
        seen.add(i)
        if is_app(e) and e.decl().kind() in ATOM_KINDS and len(e.children()) == 2 and is_arith(e.children()[0]):
            lhs, rhs = e.children()
            (cl, kl), (cr, kr) = affine(lhs), affine(rhs)
            co = {n: cl.get(n, Fraction(0)) - cr.get(n, Fraction(0)) for n in set(cl) | set(cr)}
            a = co.pop(yn, Fraction(0))
            if a != 0:
                b = ({n: -x / a for n, x in co.items() if x != 0}, -(kl - kr) / a)
                if all(canon(b) != canon(b2) for b2 in bounds): bounds.append(b)
            return
        for ch in e.children(): walk(ch)
    walk(R)
    def shift(b, s): return (dict(b[0]), b[1] + s)
    def mid(b1, b2):
        co = {n: (b1[0].get(n, Fraction(0)) + b2[0].get(n, Fraction(0))) / 2 for n in set(b1[0]) | set(b2[0])}
        return ({n: x for n, x in co.items() if x != 0}, (b1[1] + b2[1]) / 2)
    def key(c):
        return (0, abs(c[1]), 0 if c[1] < 0 else 1, "") if not c[0] else (1, 0, 0, canon(c))
    tiers = [[mid(b1, b2) for b1, b2 in itertools.combinations(bounds, 2)], list(bounds),
             [shift(b, 1) for b in bounds], [shift(b, -1) for b in bounds], [({}, Fraction(0))]]
    cands, seen = [], set()
    for tier in tiers:
        for c in sorted(tier, key=key):
            if canon(c) not in seen: seen.add(canon(c)); cands.append(c)
    if TRACE:
        print(f"      [witness {yn}] R = {fmt(R)}")
        print(f"      [witness {yn}] candidates: {[canon(c) for c in cands]}")
    term = RealVal(0)
    for c in reversed(cands):
        ct = term_of(c); term = If(substitute(R, (y, ct)), ct, term)
    assert valid(Implies(Exists([y], R), substitute(R, (y, term)))), "witness construction failed"
    return simplify(term)

# ---------- the procedure ----------
def delegate(arch, AP, GP, name):
    """Steps 1-9 of docs/complete.tex.  Returns a dict on success, None otherwise; delegate.status says which."""
    H, comps = arch.H, arch.comps
    print("=" * 78); print(name); print(f"  A_P = {fmt(AP)}\n  G_P = {fmt(GP)}")
    # step 1: relevance, and the (Scope) condition
    N = arch.support(vars_of(GP)); print(f"  N = {sorted(N)}")
    portsN = set().union(*[arch.ports(c) for c in N]) if N else set()
    outside = sorted((vars_of(AP) | vars_of(GP)) - portsN)
    if outside:
        print(f"  (Scope) fails: {outside} of A_P or G_P is not a port of any component of N; the procedure does not apply")
        delegate.status = "does not apply (Scope)"; return None
    # step 2: the first nested topological ordering
    nested = None
    for order in arch.topo_orders(N):
        ok = True
        for k in range(len(order) - 1):
            a, b = order[k], order[k + 1]
            ia, oa = comps[a]; ib, ob = comps[b]
            if (a, b) not in arch.edges(): ok = False; break                                  # (E)
            priv = (set(ia) | set(oa)) - (set(ib) | set(ob)); edge = set(oa) & set(ib)
            if len(priv) > len(edge): ok = False; break                                       # (Cap)
            if any(v in vars_of(AP) | vars_of(GP) for v in edge): ok = False; break           # (Pure)
            if H > 0 and any(v not in arch.writer or arch.writer[v] not in order[:k + 1] for v in ib):
                ok = False; break                                                             # (Info)
        if ok: nested = order; break
    if nested is None:
        print("  no nested topological ordering: the procedure does not apply"); delegate.status = "does not apply (not nested)"
        return None
    order = nested; p = len(order); print(f"  nested ordering: {order}")
    pos = {c: k for k, c in enumerate(order)}
    # forwarding maps sigma_k: priv_k -> edge_k, pairing the two sorted lists
    priv, edge, sigma = {}, {}, {}
    for k in range(p - 1):
        a, b = order[k], order[k + 1]; ia, oa = comps[a]; ib, ob = comps[b]
        priv[a] = sorted((set(ia) | set(oa)) - (set(ib) | set(ob))); edge[a] = sorted(set(oa) & set(ib))
        sigma[a] = dict(zip(priv[a], edge[a]))
        print(f"  priv({a}) = {priv[a]}, edge({a}) = {edge[a]}, forwarding {sigma[a]}")
    # step 3: fresh inputs E_k and terminal outputs Y_k (each in declaration order)
    seen = set()
    E, Y = {}, {}
    for k, c in enumerate(order):
        i_, o_ = comps[c]
        E[c] = [v for v in i_ if v not in seen]
        Y[c] = [v for v in o_ if c not in edge or v not in edge[c]]
        seen |= set(i_) | set(o_)
    print("  fresh inputs E_k:", {c: E[c] for c in order}, " terminal outputs Y_k:", {c: Y[c] for c in order})
    # step 4: eliminate inside-out, recording the witness of every existential
    body = Implies(AP, GP)
    blocks = [(t, c) for t in range(H + 1) for c in order]
    sk = {}
    cur = body
    for (t, c) in reversed(blocks):
        for y in reversed([V(v, t) for v in Y[c]]):                # last first
            sk[str(y)] = (c, t, witness(cur, y))
            cur = qe(Exists([y], cur))
        es = [V(v, t) for v in E[c]]
        if es: cur = qe(ForAll(es, cur))
    print(f"  Phi (linearised sentence) = {fmt(cur)}")
    # step 5: decision
    if not valid(cur):
        print("  Phi is false: NO acceptable delegation exists (necessity theorem)")
        delegate.status = "none exists"; return None
    # step 6: substitute witnesses for outputs of later components, by term traversal, until none is left
    def resolve(term, k):
        for _ in range(len(sk) + 1):                               # each round strictly lowers the latest prefix position
            later = {n: s for n, s in syms_of(term).items()
                     if n.rsplit("_", 1)[0] in arch.writer and arch.writer[n.rsplit("_", 1)[0]] in pos
                     and pos[arch.writer[n.rsplit("_", 1)[0]]] > k}
            if not later: return term
            assert all(n in sk for n in later), f"later output without a witness: {sorted(later)}"
            term = simplify(substitute(term, *[(s, sk[n][2]) for n, s in later.items()]))
        raise AssertionError("step 6 did not terminate")
    # decoding delta_k via the carriers kappa_k of the carrier lemma
    pts = {c: arch.ports(c) for c in order}
    def kappa(v, j, k):
        """Carrier lemma: v a port of order[j], j < k.  For jj = j, ..., k-1: keep v if it is a port of order[jj+1],
        otherwise (v is then in priv_jj) replace it by sigma_jj(v).  The result is an input of order[k]."""
        for jj in range(j, k):
            if v not in pts[order[jj + 1]]: v = sigma[order[jj]][v]
        assert v in comps[order[k]][0], f"carrier {v} is not an input of {order[k]}"
        return v
    decode = {}
    for k, c in enumerate(order):
        dmap = {}
        for v in sorted(set().union(*[pts[order[j]] for j in range(k)]) - pts[c]) if k else []:
            j = max(j for j in range(k) if v in pts[order[j]])  # start from the latest earlier component seeing v
            dmap[v] = kappa(v, j, k)
        decode[c] = dmap
    # step 7: seed
    contracts = {}
    for k, c in enumerate(order):
        G = []
        if c in sigma:
            G += [V(e, t) == V(v, t) for t in range(H + 1) for v, e in sigma[c].items()]
        for t in range(H + 1):
            for v in Y[c]:
                s = resolve(sk[f"{v}_{t}"][2], k)
                subs = [(V(u, tt), V(w, tt)) for u, w in decode[c].items() for tt in range(H + 1)]
                s = simplify(substitute(s, *subs)) if subs else s
                G.append(V(v, t) == s)
        contracts[c] = And(G) if G else BoolVal(True)
        assert vars_of(contracts[c]) <= pts[c], f"seed of {c} mentions {sorted(vars_of(contracts[c]) - pts[c])}, not ports"
        print(f"  contract {c}: A = true ; G = {fmt(contracts[c])}")
    for c in comps:
        if c not in N: contracts[c] = BoolVal(True); print(f"  contract {c}: (true, true)")
    # verify the seed
    def rk(c, S_c):                                                # (K): forall in(0) exists out(0) ... forall in(H) exists out(H)
        i_, o_ = comps[c]; q = S_c
        for t in reversed(range(H + 1)):
            outs = [V(v, t) for v in o_]; ins = [V(v, t) for v in i_]
            if outs: q = Exists(outs, q)
            if ins: q = ForAll(ins, q)
        return valid(q)
    verdicts = {}
    verdicts["seed V1"] = valid(Implies(And(AP, *contracts.values()), GP)); print(f"  (V1) A_P & all G_i -> G_P : {verdicts['seed V1']}")
    for c in order:
        verdicts[f"seed RK {c}"] = rk(c, contracts[c]); print(f"  {c} receptive & causal: {verdicts[f'seed RK {c}']}")
    # step 8: S_{i_k} := forall hid(ports(i_k)) (R_k -> G_P), R_k = A_P & AND_{j != k} S_j, one pass in order
    # Functional elimination (an identity, not an approximation): if some S_j has a top-level conjunct y == tau with
    # y hidden and tau free of y, then  forall y ((y == tau & rest) -> G)  ==  (rest -> G)[y := tau]  and
    # exists y (y == tau & rest) == rest[y := tau].  Seeds consist of such equations, so most hidden variables are
    # removed by substitution; quantifier elimination is applied only to what remains.
    def top_conjuncts(f):
        if is_and(f): return [g for ch in f.children() for g in top_conjuncts(ch)]
        return [f]
    def defs_in(formulas, hidden):
        hid = {str(h) for h in hidden}; out = {}
        for f in formulas:
            for c in top_conjuncts(f):
                if not is_eq(c): continue
                a, b = c.children()
                for y, tau in ((a, b), (b, a)):
                    if is_const(y) and y.decl().kind() == Z3_OP_UNINTERPRETED and str(y) in hid and str(y) not in out \
                            and str(y) not in {str(z) for z in z3util_free(tau)}:
                        out[str(y)] = (y, tau); break
        return out
    def z3util_free(e):
        return set(syms_of(e).values())
    def functional_eliminate(formulas, hidden):
        """returns (formulas with defined hidden variables substituted away, remaining hidden)."""
        formulas = list(formulas); hidden = list(hidden)
        while True:
            defs = defs_in(formulas, hidden)
            if not defs: break
            y, tau = next(iter(defs.values()))
            formulas = [simplify(substitute(f, (y, tau))) for f in formulas]
            hidden = [h for h in hidden if str(h) != str(y)]
        return formulas, hidden
    print("  sweep to a maximal delegation (order", order, "):")
    S = dict(contracts)
    allsyms = {V(v, t) for v in set(arch.env) | set(arch.writer) for t in range(H + 1)}
    def hidden_of(c):
        return sorted(allsyms - {V(v, t) for v in pts[c] for t in range(H + 1)}, key=str)
    def R_parts(c): return [AP] + [S[j] for j in S if j != c]
    for c in order:
        parts, hidden = functional_eliminate(R_parts(c) + [GP], hidden_of(c))
        R_k, G_k = And(parts[:-1]), parts[-1]
        S[c] = qe(ForAll(hidden, Or(G_k, Not(R_k)))) if hidden else simplify(Or(G_k, Not(R_k)))
    # step 9: A_{i_k} := exists hid(ports(i_k)) R_k, with the FINAL S_j
    sweep_out = {}
    for c in order:
        parts, hidden = functional_eliminate(R_parts(c), hidden_of(c))
        R_k = And(parts)
        A_c = qe(Exists(hidden, R_k)) if hidden else simplify(R_k)
        sweep_out[c] = (A_c, S[c])
        assert vars_of(A_c) <= pts[c] and vars_of(S[c]) <= pts[c], f"swept contract of {c} is not over its ports"
        print(f"    {c}: A = {fmt(A_c)} ; G = {fmt(S[c])}")
    allA = And([sweep_out[c][0] for c in order])
    verdicts["sweep V1"] = valid(Implies(And(AP, *S.values()), GP)); print(f"  (V1) after sweep: {verdicts['sweep V1']}")
    verdicts["sweep V2"] = valid(Implies(And(AP, *S.values()), allA)); print(f"  (V2) after sweep: {verdicts['sweep V2']}")
    verdicts["sweep RK"] = all(rk(c, S[c]) for c in order)
    print(f"  receptive & causal after sweep (every component): {verdicts['sweep RK']}")
    delegate.status = "delegation"
    return {"order": order, "phi": cur, "seed": contracts, "sweep": sweep_out, "skolem": sk, "N": N,
            "decode": decode, "verdicts": verdicts}
delegate.status = None

# ---------- forks, budget B = 1 (affine strategies), decided over the reals by Z3 ----------
def fork_affine(arch, AP, GP, name, timeout_ms=60000):
    print("=" * 78); print(name, "-- fork semi-decision procedure with affine strategies (B = 1)")
    H = arch.H; assert H == 0
    theta = []; strat = {}
    for c, (i_, o_) in arch.comps.items():
        for v in o_:
            coeffs = [Real(f"th_{v}_{u}") for u in i_] + [Real(f"th_{v}_c")]; theta += coeffs
            strat[v] = Sum([a * V(u, 0) for a, u in zip(coeffs, i_)] + [coeffs[-1]])
    # substitute strategies in topological order so outputs become functions of env
    N = arch.support(vars_of(GP)); order = next(arch.topo_orders(N))
    body = Implies(AP, GP)
    for c in reversed(order):
        for v in arch.comps[c][1]:
            body = substitute(body, (V(v, 0), strat[v]))
    env = [V(v, 0) for v in arch.env]
    s = Solver(); s.set("timeout", timeout_ms); s.add(ForAll(env, body))
    r = s.check(); print("  exists theta forall env (A_P -> G_P)[strategies]:", r)
    fork_affine.last, fork_affine.ok = {}, False
    if r == sat:
        m = s.model()
        subs = [(th, m.eval(th, model_completion=True)) for th in theta]
        for c in order:
            for v in arch.comps[c][1]:
                fork_affine.last[v] = simplify(substitute(strat[v], *subs)); print(f"  contract {c}: G = {v} = {fmt(fork_affine.last[v])}")
        chk = substitute(body, *subs); fork_affine.ok = valid(ForAll(env, chk)); print("  check forall env:", fork_affine.ok)

if __name__ == "__main__":
    print(f"z3 version {get_version_string()}")
    expected = []                                                  # (label, verdict) pairs that must all be True
    def ok_run(res):
        return res is not None and all(res["verdicts"].values())
    # E1 relay, H = 0
    A = Arch({"Radio": (["r"], ["m"]), "Display": (["m"], ["d"])}, env=["r"], H=0)
    expected.append(("relay", ok_run(delegate(A, absle(V("r", 0), 1), absle(V("d", 0) - V("r", 0), Fraction(1, 2)), "relay, H = 0"))))
    # three-stage chain, H = 0
    A3 = Arch({"C1": (["r"], ["m1"]), "C2": (["m1"], ["m2"]), "C3": (["m2"], ["d"])}, env=["r"], H=0)
    expected.append(("chain", ok_run(delegate(A3, absle(V("r", 0), 1), absle(V("d", 0) - V("r", 0), Fraction(1, 2)), "three-stage chain, H = 0"))))
    # disjunctive query on the relay
    r, d = V("r", 0), V("d", 0)
    GP4 = Or(And(Implies(r >= 0, d >= 1), Implies(r < 0, d <= -1)), absle(d - 2 * r, Fraction(1, 4)))
    expected.append(("disjunctive", ok_run(delegate(A, absle(r, 1), GP4, "relay, disjunctive query, H = 0"))))
    # relay with H = 2 and a temporal query (Info holds: Display reads no fresh input)
    A2 = Arch({"Radio": (["r"], ["m"]), "Display": (["m"], ["d"])}, env=["r"], H=2)
    GPt = And(Alw(0, 1, lambda t: Implies(V("r", t) >= Fraction(1, 2), Ev(0, 1, lambda u: V("d", u) >= Fraction(1, 2))(t)))(0),
              Alw(0, 2, lambda t: absle(V("d", t), 1))(0))
    expected.append(("H = 2", ok_run(delegate(A2, Alw(0, 2, lambda t: absle(V("r", t), 1))(0), GPt,
             "relay, H = 2, alw_[0,1](r >= 1/2 -> ev_[0,1] d >= 1/2) and alw_[0,2] |d| <= 1"))))
    # same graph, unrealizable query: alw |d - r| <= 1/2 and ev d >= 1/4 (r = -1 throughout defeats it)
    GPu = And(Alw(0, 2, lambda t: absle(V("d", t) - V("r", t), Fraction(1, 2)))(0), Ev(0, 2, lambda t: V("d", t) >= Fraction(1, 4))(0))
    res = delegate(A2, Alw(0, 2, lambda t: absle(V("r", t), 1))(0), GPu, "relay, H = 2, unrealizable query")
    expected.append(("unrealizable: none exists", res is None and delegate.status == "none exists"))
    # fan-in: not nested -> affine fork procedure
    AF = Arch({"A": (["s1"], ["a"]), "B": (["s2"], ["b"]), "Fuser": (["a", "b"], ["f"]), "Logger": (["f"], ["l"])},
              env=["s1", "s2"], H=0)
    GPf = absle(V("f", 0) - V("s1", 0) - V("s2", 0), 1)
    res = delegate(AF, BoolVal(True), GPf, "fan-in, H = 0")
    expected.append(("fan-in: not nested", res is None and delegate.status == "does not apply (not nested)"))
    if res is None:
        fork_affine(AF, BoolVal(True), GPf, "fan-in"); expected.append(("fan-in: fork B = 1", fork_affine.ok))

    # ---------- timed example: speed governor chain, H = 2 ----------
    SG = Arch({"Perception": (["o"], ["e"]), "Controller": (["e"], ["u"]), "Actuator": (["u"], ["v"])}, env=["o"], H=2)
    o_ = lambda t: V("o", t); v_ = lambda t: V("v", t)
    AP_sg = Alw(0, 2, lambda t: And(o_(t) >= 0, o_(t) <= 5))(0)
    GP_sg = And(Alw(0, 2, lambda t: And(v_(t) >= 0, v_(t) <= 2))(0),
                Alw(0, 1, lambda t: Implies(o_(t) <= 1, Ev(0, 1, lambda s: v_(s) <= Fraction(1, 4))(t)))(0),
                Alw(0, 1, lambda t: Implies(o_(t) >= 3, Ev(0, 1, lambda s: v_(s) >= 1)(t)))(0))
    res_sg = delegate(SG, AP_sg, GP_sg, "speed governor chain, H = 2: alw v in [0,2]; alw_[0,1](o<=1 -> ev_[0,1] v<=1/4); alw_[0,1](o>=3 -> ev_[0,1] v>=1)")
    # regression 5: the swept Actuator set must be the maximal one of docs/example.tex (Z3 5.3.1's 'qe' tactic once
    # returned a strictly stronger, non-equivalent set that its own cross-check accepted; qe() no longer uses it)
    u_ = lambda t: V("u", t); q = Fraction(1, 4)
    ubox_sg = And(*[And(u_(t) >= 0, u_(t) <= 5) for t in range(3)]); vbox_sg = And(*[And(v_(t) >= 0, v_(t) <= 2) for t in range(3)])
    GA_doc = And(vbox_sg, Or(v_(0) >= 1, v_(1) >= 1), Or(v_(0) <= q, v_(1) <= q), Or(v_(1) <= q, v_(2) <= q),
                 Implies(And(ubox_sg, u_(1) >= 3), Or(v_(1) >= 1, v_(2) >= 1)))
    sg_max = res_sg is not None and valid(res_sg["sweep"]["Actuator"][1] == GA_doc)
    print(f"  regression 5: swept Actuator set equals the maximal set of docs/example.tex: {sg_max}")
    expected.append(("regression 5: swept Actuator set is the documented maximal one", sg_max))
    GP_sgu = And(Alw(0, 2, lambda t: And(v_(t) >= 0, v_(t) <= 2))(0),
                 Alw(0, 2, lambda t: Implies(o_(t) <= 1, v_(t) <= Fraction(1, 4)))(0),
                 Alw(0, 1, lambda t: Implies(o_(t) >= 3, Ev(1, 1, lambda s: v_(s) >= 1)(t)))(0))
    delegate(SG, AP_sg, GP_sgu, "speed governor chain, unrealizable variant: alw(o<=1 -> v<=1/4) and alw_[0,1](o>=3 -> ev_[1,1] v>=1)")
    # ---------- regression instances from review ----------
    print("=" * 78); print("regression instances from review"); reg = []
    # (1) carrier lemma: a carrier that an intermediate component reads must still be followed (Reviewer A)
    AC = Arch({"C1": (["r"], ["e"]), "C2": (["e"], ["f"]), "C3": (["e", "f"], ["g1", "g2"]), "C4": (["g1", "g2"], ["d"])},
              env=["r"], H=0)
    res = delegate(AC, absle(r, 1), absle(d - r, Fraction(1, 2)), "regression 1a: four-stage chain C1..C4 (carrier lemma)")
    reg.append(("1a seeds over ports, C4 seed is d = g1, all verdicts true", ok_run(res)
                and valid(res["seed"]["C4"] == (d == V("g1", 0)))))
    AX = Arch({"X": (["r"], ["e"]), "Y": (["e"], ["y1"]), "Z": (["e", "y1"], ["z1", "z2"]), "W": (["z1", "z2"], ["d"])},
              env=["r"], H=0)
    res = delegate(AX, absle(r, 1), absle(d - r, Fraction(1, 2)), "regression 1b: X/Y/Z/W (carrier lemma)")
    reg.append(("1b seeds over ports, W seed is d = z1, all verdicts true", ok_run(res)
                and valid(res["seed"]["W"] == (d == V("z1", 0)))))
    # (2) step 9 from the final sets: A_P mentions an output (Reviewer A)
    res = delegate(A, d >= r, d >= r - 1, "regression 2: relay, A_P = d >= r, G_P = d >= r - 1 (step 9, (V2))")
    reg.append(("2 (V2) holds and A_Radio == true, A_Display == true", ok_run(res)
                and valid(res["sweep"]["Radio"][0]) and valid(res["sweep"]["Display"][0])))
    # (3) (Scope) fails: Q writes o, read by no one, o occurs in A_P (Reviewer C)
    o = V("o", 0)
    AQ = Arch({"Radio": (["r"], ["m"]), "Display": (["m"], ["d"]), "Q": ([], ["o"])}, env=["r"], H=0)
    res = delegate(AQ, Implies(o >= 0, r <= 1), And(d == 0, r <= 1), "regression 3: relay + Q, (Scope) fails")
    reg.append(("3 does not apply (Scope), no refutation", res is None and delegate.status == "does not apply (Scope)"))
    # (4) step 6 by term traversal: output named d, environment variable named ad (Reviewer C)
    AS = Arch({"Radio": (["ad"], ["m1", "m2", "q"]), "Display": (["m1", "m2"], ["d"])}, env=["ad"], H=0)
    ad = V("ad", 0)
    res = delegate(AS, absle(ad, 1), And(absle(d - ad, Fraction(1, 2)), absle(V("q", 0) - ad, Fraction(1, 2))),
                   "regression 4: symbol names d and ad (step 6 terminates)")
    reg.append(("4 terminates, all verdicts true", ok_run(res)))
    # (4b) step 6 actually substitutes: H = 1, Radio's terminal output q(1) is constrained against Display's d(0)
    AS1 = Arch({"Radio": (["r"], ["m1", "m2", "q"]), "Display": (["m1", "m2"], ["d"])}, env=["r"], H=1)
    res = delegate(AS1, Alw(0, 1, lambda t: absle(V("r", t), 1))(0),
                   And(Alw(0, 1, lambda t: absle(V("d", t) - V("r", t), Fraction(1, 2)))(0), absle(V("q", 1) - d, Fraction(1, 4))),
                   "regression 4b: H = 1, witness of q(1) mentions d(0) (step 6 substitutes)")
    reg.append(("4b witness of q_1 mentions d_0, seed of Radio is over its ports, all verdicts true", ok_run(res)
                and "d_0" in syms_of(res["skolem"]["q_1"][2])))
    print("  regression verdicts:")
    for lbl, v in reg: print(f"    {lbl}: {v}")
    expected += [("regression " + lbl, v) for lbl, v in reg]
    print("=" * 78)
    bad = [lbl for lbl, v in expected if not v]
    print("all verdicts as expected" if not bad else f"UNEXPECTED VERDICTS: {bad}")
    sys.exit(1 if bad else 0)
