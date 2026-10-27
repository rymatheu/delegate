#!/usr/bin/env python3
"""Decompose a global PolySTL contract over an architecture graph (design spec sections 2, 3, 5).
Run from the directory root: .venv/bin/python scripts/decompose.py   (--tex adds LaTeX forms).
Prints intermediate formulas, emitted contracts and Z3 verdicts; exit 0 iff all are as expected."""
import math
import re
import sys
import textwrap
from fractions import Fraction as Fr
import z3

TOL = Fr(1, 1024)            # bisection tolerance for the tolerance eps
FAILS = []                   # unexpected outcomes
TEX = '--tex' in sys.argv
STATS = {'proj': 0}

def say(s=''):
    for ln in s.split('\n'):        # keep every printed line within 96 columns
        lead = ' ' * (len(ln) - len(ln.lstrip()) + 4)
        print(textwrap.fill(ln, 96, subsequent_indent=lead, break_long_words=False,
                            break_on_hyphens=False) if len(ln) > 96 and "TeX:" not in ln else ln,
              flush=True)
def fr(x): return x if isinstance(x, Fr) else Fr(x)
def fstr(q):
    return str(fr(q).numerator) if fr(q).denominator == 1 else f"{fr(q).numerator}/{fr(q).denominator}"

def expect(label, got, want):
    ok, txt = got == want, lambda v: fstr(v) if isinstance(v, Fr) else str(v).lower()
    say(f"  [{'ok' if ok else 'UNEXPECTED'}] {label}: {txt(got)}" + ('' if ok else f"   (expected {txt(want)})"))
    FAILS.extend([] if ok else [label])

# ---------------------------------------------------------------- PolySTL syntax
class Lin:
    """Linear expression sum_v c_v * v + k over variable names; comparisons build atoms."""
    def __init__(self, c=None, k=0):
        self.c, self.k = {v: fr(a) for v, a in (c or {}).items() if fr(a) != 0}, fr(k)
    @staticmethod
    def of(x): return x if isinstance(x, Lin) else Lin({}, x)
    def __add__(self, o):
        o = Lin.of(o)
        return Lin({v: self.c.get(v, 0) + o.c.get(v, 0) for v in set(self.c) | set(o.c)}, self.k + o.k)
    __radd__ = __add__
    def __mul__(self, s): return Lin({v: a * fr(s) for v, a in self.c.items()}, self.k * fr(s))
    __rmul__ = __mul__
    def __neg__(self): return self * -1
    def __sub__(self, o): return self + (-Lin.of(o))
    def __rsub__(self, o): return Lin.of(o) - self
    # an atom ('atom', e, strict) means  e <= 0  (e < 0 if strict)
    def __le__(self, o): return ('atom', self - o, False)
    def __lt__(self, o): return ('atom', self - o, True)
    def __ge__(self, o): return ('atom', Lin.of(o) - self, False)
    def __gt__(self, o): return ('atom', Lin.of(o) - self, True)

def V(name): return Lin({name: 1})
def AND(*f): return ('and', list(f))
def OR(*f): return ('or', list(f))
def IMP(f, g): return ('imp', f, g)
def ALW(a, b, f): return ('alw', a, b, f)
def EV(a, b, f): return ('ev', a, b, f)
def ABSLE(e, c): return AND(e <= c, e >= -c)
def ABSGT(e, c): return OR(e > c, e < -c)
def ABSGE(e, c): return OR(e >= c, e <= -c)

TRUE = ('and', [])

def fvars(f):
    if f[0] == 'atom':
        return set(f[1].c)
    subs = {'and': f[1], 'or': f[1], 'not': f[1:], 'imp': f[1:]}.get(f[0], f[3:])
    return set().union(set(), *[fvars(g) for g in subs])

COLS = {}
def col(v, t): return COLS.setdefault(f"{v}@{t}", z3.Real(f"{v}@{t}"))
def zq(q): return z3.Q(fr(q).numerator, fr(q).denominator)

def unroll(f, t, H):
    """Boolean combination of time-stamped atoms (a Z3 formula over columns v@t)."""
    tag = f[0]
    if tag == 'atom':
        e = f[1]
        lhs = z3.Sum([zq(a) * col(v, t) for v, a in sorted(e.c.items())]) if e.c else zq(0)
        return lhs < zq(-e.k) if f[2] else lhs <= zq(-e.k)
    if tag in ('and', 'or'):
        return (z3.And if tag == 'and' else z3.Or)([unroll(g, t, H) for g in f[1]])
    if tag == 'not':
        return z3.Not(unroll(f[1], t, H))
    if tag == 'imp':
        return z3.Implies(unroll(f[1], t, H), unroll(f[2], t, H))
    a, b, g = f[1], f[2], f[3]
    assert t + b <= H, "formula horizon exceeds H"
    parts = [unroll(g, s, H) for s in range(t + a, t + b + 1)]
    return z3.And(parts) if tag == 'alw' else z3.Or(parts)

# ---------------------------------------------------------------- reading Z3 terms back
def colkey(n):
    return (int(n.partition('@')[2] or -1), n.partition('@')[0])

def num(e):
    if z3.is_rational_value(e): return Fr(e.numerator_as_long(), e.denominator_as_long())
    return Fr(e.as_long()) if z3.is_int_value(e) else None

def zlin(e):
    """Z3 linear term -> (dict name -> Fr, constant)."""
    q = num(e)
    if q is not None:
        return {}, q
    if z3.is_app_of(e, z3.Z3_OP_TO_REAL):
        return zlin(e.arg(0))
    if z3.is_const(e):
        return {str(e): Fr(1)}, Fr(0)
    if z3.is_add(e) or z3.is_sub(e):
        c, k = zlin(e.arg(0))
        c = dict(c)
        for i in range(1, e.num_args()):
            c2, k2 = zlin(e.arg(i))
            s = 1 if z3.is_add(e) else -1
            for v, a in c2.items():
                c[v] = c.get(v, 0) + s * a
            k += s * k2
        return {v: a for v, a in c.items() if a != 0}, k
    if z3.is_app_of(e, z3.Z3_OP_UMINUS):
        c, k = zlin(e.arg(0))
        return {v: -a for v, a in c.items()}, -k
    if z3.is_mul(e):
        s = math.prod(num(x) for x in e.children() if num(x) is not None)
        terms = [x for x in e.children() if num(x) is None]
        assert len(terms) <= 1, f"nonlinear term {e}"
        c, k = zlin(terms[0]) if terms else ({}, Fr(1))
        return {v: a * s for v, a in c.items()}, k * s
    if z3.is_div(e):
        c, k = zlin(e.arg(0))
        d = num(e.arg(1))
        return {v: a / d for v, a in c.items()}, k / d
    raise ValueError(f"not linear: {e}")

CMP = (z3.Z3_OP_LE, z3.Z3_OP_LT, z3.Z3_OP_GE, z3.Z3_OP_GT, z3.Z3_OP_EQ)

def is_cmp(e):
    return z3.is_app(e) and e.decl().kind() in CMP and z3.is_arith(e.arg(0))

def zatoms(e):
    """A comparison -> list of (coeffs, b, strict) meaning coeffs.x <= b (< b)."""
    k = e.decl().kind()
    c1, k1 = zlin(e.arg(0))
    c2, k2 = zlin(e.arg(1))
    c = {v: c1.get(v, 0) - c2.get(v, 0) for v in set(c1) | set(c2)}
    c = {v: a for v, a in c.items() if a != 0}
    b = k2 - k1
    neg = {v: -a for v, a in c.items()}
    if k == z3.Z3_OP_LE: return [(c, b, False)]
    if k == z3.Z3_OP_LT: return [(c, b, True)]
    if k == z3.Z3_OP_GE: return [(neg, -b, False)]
    if k == z3.Z3_OP_GT: return [(neg, -b, True)]
    return [(c, b, False), (neg, -b, False)]

def walk(e, seen=None):
    """Subterms of e, each once, depth first, left to right."""
    seen = set() if seen is None else seen
    if e.get_id() in seen:
        return
    seen.add(e.get_id())
    yield e
    for x in ([e.body()] if z3.is_quantifier(e) else e.children()):
        yield from walk(x, seen)

def atom_occurrences(e):
    """Atoms of a formula in order of first occurrence."""
    return [a for x in walk(e) if is_cmp(x) for a in zatoms(x)]

def zcols(e):
    return {str(x) for x in walk(e) if z3.is_const(x) and num(x) is None and '@' in str(x)}

def times_of(c): return {colkey(n)[0] for n in c}

# ---------------------------------------------------------------- printing formulas as PolySTL
SHOW_T = [False]       # print '@t:' prefixes (horizon > 0)
READABLE = [True]      # contextual simplification for printing (off inside the bisection)

def tree(e):
    if z3.is_true(e): return ('T',)
    if z3.is_false(e): return ('F',)
    if z3.is_and(e): return ('and', [tree(x) for x in e.children()])
    if z3.is_or(e): return ('or', [tree(x) for x in e.children()])
    if z3.is_not(e):
        t = tree(e.arg(0))
        return ('lit', t[1], not t[2]) if t[0] == 'lit' else ('not', t)
    if z3.is_implies(e): return ('or', [tree(z3.Not(e.arg(0))), tree(e.arg(1))])
    if is_cmp(e):
        ats = zatoms(e)
        lits = [('lit', a, True) for a in ats]
        return lits[0] if len(lits) == 1 else ('and', lits)
    raise ValueError(f"cannot print {e}")

def bound(lit):
    """literal -> (expr key, side, value, strict) with leading coefficient +1."""
    (c, b, strict), pos = lit[1], lit[2]
    keys = sorted(c, key=colkey)
    if not keys:
        return ((), 'const', (b, strict, pos), False)
    a0 = c[keys[0]]
    s = 1 / abs(a0)
    e = tuple((v, c[v] * s * (1 if a0 > 0 else -1)) for v in keys)
    if pos:
        return (e, 'up', b * s, strict) if a0 > 0 else (e, 'lo', -b * s, strict)
    return (e, 'lo', b * s, not strict) if a0 > 0 else (e, 'up', -b * s, not strict)

SYM = {'and': (' and ', r' \wedge '), 'or': (' or ', r' \vee '), 'imp': (' -> ', r' \rightarrow '),
       'not': ('not ', r'\neg '), '<=': (' <= ', r' \le '), '<': (' < ', ' < '),
       '>=': (' >= ', r' \ge '), '>': (' > ', ' > '), 'true': ('true', r'\mathit{true}'),
       'false': ('false', r'\mathit{false}')}

def sym(k, tex): return SYM[k][1 if tex else 0]

def qtxt(q, tex):
    q = fr(q)
    if not tex or q.denominator == 1:
        return fstr(q)
    sg = '-' if q < 0 else ''
    return f"{sg}\\tfrac{{{abs(q.numerator)}}}{{{q.denominator}}}"

def vtxt(n, tex):
    v = n.split('@')[0] if SHOW_T[0] or n.endswith('@0') else n
    if tex:
        base = v.rstrip('0123456789')
        idx = v[len(base):]
        return base + (f"_{{{idx}}}" if idx else '')
    return v

def etxt(e, tex):
    s = ''
    for i, (v, a) in enumerate(e):
        mag = abs(a)
        sg = ('-' if a < 0 else '') if i == 0 else (' - ' if a < 0 else ' + ')
        co = '' if mag == 1 else (qtxt(mag, tex) + ('' if tex else '*'))
        s += sg + co + vtxt(v, tex)
    return s

def tpre(e, tex):
    if not SHOW_T[0] or not e:
        return ''
    ts = sorted({colkey(v)[0] for v, _ in e})
    t = ','.join(map(str, ts))
    return f"@{{{t}}}{{:}}\\," if tex else f"@{t}: "

def btxt(e, side, v, strict, tex):
    op = ('<' if strict else '<=') if side == 'up' else ('>' if strict else '>=')
    return tpre(e, tex) + etxt(e, tex) + sym(op, tex) + qtxt(v, tex)

def group(lits, tex, conj):
    """Render literals joined by and (conj) / or, merging bounds on the same expression."""
    order, g, out = [], {}, []
    for l in lits:
        e, side, v, st = bound(l)
        if side == 'const':
            b, strict, pos = v
            truth = (0 < b or (0 == b and not strict)) == pos
            out.append(sym('true' if truth else 'false', tex))
            continue
        if e not in g:
            order.append(e)
            g[e] = []
        g[e].append((side, v, st))
    bar = '|'
    order.sort(key=lambda e: (colkey(e[0][0]), [(colkey(v), a) for v, a in e]))
    for e in order:
        bs = g[e]
        lo = [b for b in bs if b[0] == 'lo']
        up = [b for b in bs if b[0] == 'up']
        if len(lo) == 1 and len(up) == 1 and lo[0][2] == up[0][2]:
            (_, l, st), (_, u, _) = lo[0], up[0]
            if conj and l == -u and u >= 0:
                op = ('<' if st else '<=')
                out.append(tpre(e, tex) + bar + etxt(e, tex) + bar + sym(op, tex) + qtxt(u, tex))
                continue
            if conj and l <= u:
                op = ('<' if st else '<=')
                out.append(tpre(e, tex) + qtxt(l, tex) + sym(op, tex) + etxt(e, tex) + sym(op, tex)
                           + qtxt(u, tex))
                continue
            if not conj and u == -l and l > 0:
                op = ('>' if st else '>=')
                out.append(tpre(e, tex) + bar + etxt(e, tex) + bar + sym(op, tex) + qtxt(l, tex))
                continue
        out.extend(btxt(e, s, v, st, tex) for s, v, st in bs)
    return out

def tmin(t):
    if t[0] == 'lit': return min((colkey(v)[0] for v in t[1][0]), default=-1)
    if t[0] in ('and', 'or'): return min((tmin(x) for x in t[1]), default=-1)
    return {'not': lambda: tmin(t[1]), 'imp': lambda: min(tmin(t[1]), tmin(t[2]))}.get(t[0], lambda: -1)()

def as_imp(kids):
    """Disjuncts -> (antecedent, consequent) when they read as an implication, else None."""
    isneg = lambda x: x[0] == 'not' or (x[0] == 'lit' and not x[2])
    neg, oth = [x for x in kids if isneg(x)], [x for x in kids if not isneg(x)]
    early = [x for x in kids if tmin(x) == tmin(kids[0])]
    if not neg and len(early) == 1 and early[0][0] == 'lit' and len(kids) > 1:
        neg, oth = early, kids[1:]          # a or b printed as (not a) -> b
    if not (neg and oth):
        return None
    pos = []
    for x in neg:
        y = ('lit', x[1], not x[2]) if x[0] == 'lit' else x[1]
        pos.extend(y[1] if y[0] == 'and' else [y])
    return ('and', pos), ('or', oth)

def fmt(t, tex=False, top=True):
    if isinstance(t, z3.ExprRef):
        t = tree(t)
    k = t[0]
    if k == 'T': return sym('true', tex)
    if k == 'F': return sym('false', tex)
    if k == 'lit':
        return group([t], tex, True)[0]
    if k == 'not':
        return sym('not', tex) + '(' + fmt(t[1], tex, True) + ')'
    par = (lambda s: s) if top else (lambda s: '(' + s + ')')
    if k == 'imp':
        wrap = lambda s: '(' + s + ')' if any(sym(o, tex) in s for o in ('and', 'or', 'imp')) else s
        return par(wrap(fmt(t[1], tex)) + sym('imp', tex) + wrap(fmt(t[2], tex)))
    kids = t[1]
    if len(kids) == 1:
        return fmt(kids[0], tex, top)
    kids = sorted(kids, key=lambda x: (tmin(x), fmt(x)))
    if k == 'or':
        imp = as_imp(kids)
        if imp:
            return fmt(('imp',) + imp, tex, top)
        lits = [x for x in kids if x[0] == 'lit']
        parts = group(lits, tex, False) + [fmt(x, tex, False) for x in kids if x[0] != 'lit']
        return parts[0] if len(parts) == 1 else par(sym('or', tex).join(parts))
    groups, merged = {}, []                 # (A -> x) and (A -> y) printed as A -> (x and y)
    for x in kids:
        imp = as_imp(sorted(x[1], key=lambda y: (tmin(y), fmt(y)))) if x[0] == 'or' else None
        if imp is None:
            merged.append(x)
            continue
        key = fmt(imp[0])
        if key not in groups:
            groups[key] = ['imp', imp[0], ('and', [])]
            merged.append(groups[key])
        groups[key][2][1].append(imp[1][1][0] if len(imp[1][1]) == 1 else imp[1])
    kids = [tuple(x) if isinstance(x, list) else x for x in merged]
    if len(kids) == 1:
        return fmt(kids[0], tex, top)
    lits = [x for x in kids if x[0] == 'lit']
    parts = group(lits, tex, True) + [fmt(x, tex, False) for x in kids if x[0] != 'lit']
    return parts[0] if len(parts) == 1 else par(sym('and', tex).join(parts))

def wrap(text, hang, width=94):
    """Break a long line after ' and ', ' or ' or ' -> ' with a hanging indent."""
    lines, cur = [], ''
    for tok in re.split(r'(?<= and )|(?<= or )|(?<= -> )', text):
        if cur and len(cur) + len(tok) > width:
            lines.append(cur.rstrip())
            cur = hang
        cur += tok
    return '\n'.join(lines + [cur])

def show(label, f, indent='    '):
    say(wrap(f"{indent}{label}{fmt(f)}", ' ' * (len(indent) + len(label))))
    if TEX:
        say(f"{indent}  TeX: {fmt(f, True)}")

# ---------------------------------------------------------------- Z3: simplification, QE, decisions
def entails(C, F):
    return valid(z3.Implies(C, F))[0]

def csimp(F, C):
    """Simplify a quantifier-free F in the context C: returns F' with C |= (F <-> F')."""
    if entails(C, F): return z3.BoolVal(True)
    if entails(C, z3.Not(F)): return z3.BoolVal(False)
    if z3.is_not(F): return z3.Not(csimp(F.arg(0), C))
    if not (z3.is_and(F) or z3.is_or(F)): return F
    conj = z3.is_and(F)
    kids = [csimp(k, C) for k in F.children()]
    kids = [k for k in kids if not (z3.is_true(k) if conj else z3.is_false(k))]
    i = 0
    while i < len(kids):                      # drop children made redundant by the others
        oth = kids[:i] + kids[i + 1:]
        red = entails(z3.And(C, *oth), kids[i]) if conj else entails(z3.And(C, kids[i]), z3.Or(oth))
        if red: kids.pop(i)
        else: i += 1
    return kids[0] if len(kids) == 1 else (z3.And(kids) if conj else z3.Or(kids))

def disjuncts(c):
    """Flatten a clause: or-children, and not(and(...)) into negated conjuncts."""
    if z3.is_or(c):
        return [x for k in c.children() for x in disjuncts(k)]
    if z3.is_not(c) and z3.is_and(c.arg(0)):
        return [x for k in c.arg(0).children() for x in disjuncts(z3.Not(k))]
    if z3.is_not(c) and z3.is_not(c.arg(0)):
        return disjuncts(c.arg(0).arg(0))
    return [c]

def minimize(F, C):
    """Under context C: shorten clauses while C and F entail them; drop duplicate and entailed clauses."""
    cls = [disjuncts(c) for c in (F.children() if z3.is_and(F) else [F])]
    s = z3.Solver()
    s.add(C, F)
    for i in range(len(cls)):
        j = 0
        while j < len(cls[i]) and len(cls[i]) > 1:
            short = cls[i][:j] + cls[i][j + 1:]
            s.push()
            s.add(z3.Not(z3.Or(short)))
            red = s.check() == z3.unsat
            s.pop()
            if red:
                cls[i] = short
                s.add(z3.Or(short))
            else:
                j += 1
    out = list({frozenset(x.get_id() for x in c): z3.Or(c) if len(c) > 1 else c[0] for c in cls}.values())
    s = z3.Solver()
    tags = [z3.Bool(f"keep_{k}") for k in range(len(out))]
    s.add(C, *[z3.Implies(b, c) for b, c in zip(tags, out)])
    keep = [True] * len(out)
    for i in range(len(out)):
        assume = [tags[k] for k in range(len(out)) if keep[k] and k != i]
        s.push()
        s.add(z3.Not(out[i]))
        if s.check(*assume) == z3.unsat:
            keep[i] = False
        s.pop()
    fs = [c for c, k in zip(out, keep) if k]
    return z3.BoolVal(True) if not fs else (fs[0] if len(fs) == 1 else z3.And(fs))

def simp(f, ctx=None):
    f = z3.Then('simplify', 'ctx-solver-simplify', 'simplify')(goal(f)).as_expr()
    if not READABLE[0]:
        return f
    C = z3.BoolVal(True) if ctx is None else ctx
    f = csimp(f, C)
    return f if z3.is_true(f) or z3.is_false(f) else minimize(f, C)

def valid(f):
    """Validity of a (possibly quantified) formula.  Returns (bool, solver)."""
    for s in (z3.Solver(), z3.Then('qe', 'smt').solver()):
        s.add(z3.Not(f))
        r = s.check()
        if r != z3.unknown:
            return r == z3.unsat, s
    raise RuntimeError("validity query returned unknown")

def qe2(f):
    return z3.Tactic('qe2')(goal(f)).as_expr()

def goal(f):
    g = z3.Goal()
    g.add(f)
    return g

def project(kind, phi, keep, label, quiet=False, ctx=None):
    """Universal (kind 'A', Pi) or existential (kind 'E', pi) projection of phi onto the columns
    in keep: every other column of phi is eliminated by qe2; the result is cross-checked."""
    elim = sorted(zcols(phi) - set(keep), key=colkey)
    if not elim:
        return simp(phi)
    vs = [COLS[n] for n in elim]
    q = z3.ForAll(vs, phi) if kind == 'A' else z3.Exists(vs, phi)
    if ctx is None:
        res = simp(qe2(q))
    else:      # phi = ante -> body: Pi(ante -> body) = W -> Pi(...), W = pi(ante); body split at its conjuncts
        ante, body = ctx
        W = simp(qe2(z3.Exists(vs, ante)))
        parts = body.children() if z3.is_and(body) else [body]
        inner = z3.And([simp(qe2(z3.ForAll(vs, z3.Implies(ante, b)))) for b in parts])
        inner = simp(inner, W)
        res = inner if z3.is_true(W) else z3.Implies(W, inner)
    STATS['proj'] += 1
    ok, _ = valid(res == q)
    if not ok:
        FAILS.append('qe2 cross-check ' + label)
    mixed = [a for a in atom_occurrences(res) if len(times_of(a[0])) > 1]
    if mixed:
        FAILS.append('single-time atoms ' + label)
    if not quiet:
        say(f"    qe2 cross-check {'ok' if ok else 'FAILED'}: {label}"
            + ('' if not mixed else '   (FACT VIOLATED: cross-time atom)'))
    return res

def decide(sentence):
    """Truth of a closed LRA sentence: qe2 reduces it to true or false."""
    r = simp(qe2(sentence))
    assert z3.is_true(r) or z3.is_false(r), "qe2 did not decide a closed sentence"
    return z3.is_true(r)

# ---------------------------------------------------------------- architecture
class Comp:
    def __init__(self, name, ins, outs, delay=0):
        self.name, self.ins, self.outs, self.delay = name, list(ins), list(outs), delay

class Arch:
    def __init__(self, env, comps, H):
        self.env, self.comps, self.H = list(env), {c.name: c for c in comps}, H
        owners = list(self.env) + [v for c in comps for v in c.outs]
        assert len(owners) == len(set(owners)), "each variable has exactly one owner"
        self.writer = {v: c.name for c in comps for v in c.outs}

    def cols(self, vs): return {f"{v}@{t}" for v in vs for t in range(self.H + 1)}
    def ports(self, names): return self.cols({v for n in names for v in self.comps[n].ins + self.comps[n].outs})

    def support(self, gvars):
        targets = {self.writer[v] for v in gvars if v in self.writer}
        N, frontier = set(targets), list(targets)
        while frontier:
            i = frontier.pop()
            for j, c in self.comps.items():
                if j not in N and set(c.outs) & set(self.comps[i].ins):
                    N.add(j)
                    frontier.append(j)
        return N

    def topo(self, N):
        order, left = [], set(N)
        while left:
            ready = sorted(i for i in left if not any(
                j in left and j != i and set(self.comps[j].outs) & set(self.comps[i].ins) for j in left))
            assert ready, "the support is not acyclic"
            order.append(ready[0])
            left.remove(ready[0])
        return order

def at(cs, t): return sorted((c for c in cs if colkey(c)[0] == t), key=colkey)
def lin_txt(row, cols_): return etxt(tuple((c, a) for c, a in zip(cols_, row) if a != 0), False) or '0'

def independent(basis, row):
    """Gaussian elimination over Fractions: add row to the echelon basis if it raises the rank."""
    r = list(row)
    for piv, b in basis:
        r = [x - r[piv] / b[piv] * y for x, y in zip(r, b)]
    nz = [i for i, x in enumerate(r) if x != 0]
    basis.extend([(nz[0], r)] if nz else [])
    return bool(nz)

# ---------------------------------------------------------------- the method (spec sections 2 and 3)
def decompose(arch, AP, GP, eps, verbose):
    """Returns dict with order, contracts {name: (A, G)} and stop (None or report)."""
    H = arch.H
    SHOW_T[0] = H > 0
    zAP, Q = unroll(AP, 0, H), unroll(GP, 0, H)
    READABLE[0] = verbose
    N = arch.support(fvars(GP))
    order = arch.topo(N)
    res = {'N': N, 'order': order, 'stop': None, 'contracts': {}}
    p = say if verbose else (lambda *a: None)
    q = not verbose
    p(f"  support N = {{{', '.join(sorted(N))}}};  order: {', '.join(order)} (topological, ties by name)")
    for n in sorted(set(arch.comps) - N):
        p(f"  {n} is outside N: contract (true, true)")
        res['contracts'][n] = (z3.BoolVal(True), z3.BoolVal(True))
    for k, ik in enumerate(order):
        c = arch.comps[ik]
        Pk = arch.ports([ik])
        p(f"  k = {k + 1}: component {ik} (delay {c.delay})")
        Ak = project('E', zAP, arch.cols(c.ins), f"A_{ik} = pi_in({ik})(A_P)", q)
        if verbose:
            show(f"Q_{k + 1} = ", Q)
            show(f"A_{ik} = ", Ak)
        if k == len(order) - 1:
            G = Q if zcols(Q) <= Pk else project('A', z3.Implies(zAP, Q), Pk, f"G_{ik}", q)
            res['contracts'][ik] = (Ak, G)
            break
        rest = order[k + 1:]
        R = arch.ports(rest)
        priv = Pk - R
        rd = {v for j in rest for v in arch.comps[j].ins}
        edge = sorted(v for v in c.outs if v in rd)
        envk = sorted({v for v in arch.env if v in rd and v not in c.ins})
        p(f"    private_{k + 1} = {{{', '.join(sorted({x.split('@')[0] for x in priv}))}}}, "
          f"edge_{k + 1} = {{{', '.join(edge)}}}, env_{k + 1} = {{{', '.join(envk)}}}")
        atoms = atom_occurrences(Q)
        I = []
        if c.delay == 0:
            for t in range(H + 1):
                pc = at(priv, t)
                basis, forms = [], []
                for (cf, b, st) in atoms:
                    row = [cf.get(x, Fr(0)) for x in pc]
                    if any(row) and independent(basis, row):
                        lead = next(x for x in row if x != 0)
                        forms.append([x / lead for x in row])
                rho = len(forms)
                if not rho:
                    continue
                ftxt = ', '.join(lin_txt(f, pc) for f in forms)
                p(f"    needed forms L_{k + 1}({t}) (rank {rho}): {ftxt}")
                if rho > len(edge):
                    names = '{' + ', '.join(x.split('@')[0] for x in pc) + '}'
                    res['stop'] = (f"component {ik} must forward {rho} independent linear forms of {names} "
                                   f"at time {t} but has only {len(edge)} edge variable"
                                   f"{'s' if len(edge) != 1 else ''} (forms: {ftxt}); "
                                   f"not delegable by forwarding")
                    p("    STOP: " + res['stop'])
                    return res
                for m, f in zip(edge, forms):
                    e = col(m, t) - z3.Sum([zq(a) * COLS[x] for x, a in zip(pc, f) if a != 0])
                    I += [e <= zq(eps), -e <= zq(eps)]
        else:
            mixed = [a for a in atoms if set(a[0]) & priv and not set(a[0]) <= priv]
            if mixed:
                cf = mixed[0][0]
                res['stop'] = (f"forwarding the form {lin_txt([cf[x] for x in sorted(cf, key=colkey)], sorted(cf, key=colkey))} "
                               f"across the delay-1 edge of {ik} is not expressible in PolySTL")
                p("    STOP: " + res['stop'])
                return res
            pol = {}
            for t in range(H):
                mus, keys = [], set()
                for (cf, b, st) in atoms:
                    if set(cf) & priv and times_of(cf) == {t}:
                        ks = sorted(cf, key=colkey)
                        s = abs(cf[ks[0]]) * (1 if cf[ks[0]] > 0 else -1)
                        key = (tuple((x, cf[x] / s) for x in ks), b / s, st == (s > 0))
                        if key not in keys:
                            keys.add(key)
                            tk = (tuple((x.split('@')[0], a) for x, a in key[0]), key[1], key[2])
                            if tk not in pol:
                                pol[tk] = s > 0
                            if pol[tk] != (s > 0):          # use the polarity of the first occurrence
                                cf, b, st = {x: -a for x, a in cf.items()}, -b, not st
                            mus.append((cf, b, st))
                if not mus:
                    continue
                if not edge:
                    res['stop'] = f"component {ik} has no edge variable to forward atoms at time {t}"
                    p("    STOP: " + res['stop'])
                    return res
                zm = [z3.Sum([zq(a) * COLS[x] for x, a in sorted(cf.items())]) for cf, b, st in mus]
                zm = [(e < zq(b)) if st else (e <= zq(b)) for e, (cf, b, st) in zip(zm, mus)]
                if verbose:
                    say(f"    atoms of Q_{k + 1} on private_{k + 1} at time {t} (q = {len(mus)}): "
                        + ', '.join(fmt(x) for x in zm))
                m = col(edge[0], t + 1)
                for cc in range(2 ** len(mus)):
                    lits = [zm[j] if (cc >> j) & 1 else z3.Not(zm[j]) for j in range(len(mus))]
                    I.append(z3.Implies(z3.And(lits), z3.And(m >= 2 * cc, m <= 2 * cc + 1)))
        I = z3.And(I)
        if c.delay and verbose:          # readable equivalent form (impossible assignments drop out)
            I2 = simp(I)
            if not valid(I2 == I)[0]:
                FAILS.append('simplification of I')
            I = I2
        if verbose:
            show(f"I_{k + 1} = ", I)
        outs_rest = arch.cols({v for j in rest for v in arch.comps[j].outs})
        T1 = project('E', z3.Implies(zAP, Q), zcols(z3.Implies(zAP, Q)) - outs_rest,
                     f"pi over out(rest_{k + 2}) for Sigma_{k + 1}", q)
        Sig = project('A', T1, Pk, f"Pi over env_{k + 1} for Sigma_{k + 1}", q)
        if verbose:
            show(f"Sigma_{k + 1} = ", Sig)
        res['contracts'][ik] = (Ak, I if z3.is_true(Sig) else z3.And(I, Sig))
        ante = z3.And(zAP, I, Sig)
        Q = project('A', z3.Implies(ante, Q), R, f"Q_{k + 2} = Pi_ports(rest_{k + 2})", q, (ante, Q))
    return res

# ---------------------------------------------------------------- verdicts
def S_of(A, G): return z3.Implies(A, G)

def io(arch, n, t=None):
    c = arch.comps[n]
    ts = range(arch.H + 1) if t is None else [t]
    return ([col(v, s) for s in ts for v in c.ins], [col(v, s) for s in ts for v in c.outs])

def Q_(kind, vs, body):
    return body if not vs else (z3.ForAll(vs, body) if kind == 'A' else z3.Exists(vs, body))

def alternation(arch, n, body):
    for t in reversed(range(arch.H + 1)):
        i, o = io(arch, n, t)
        body = Q_('A', i, Q_('E', o, body)) if arch.comps[n].delay == 0 else Q_('E', o, Q_('A', i, body))
    return body

def receptive(arch, n, S): return decide(Q_('A', io(arch, n)[0], Q_('E', io(arch, n)[1], S)))
def causal(arch, n, S): return decide(alternation(arch, n, S))

def slack_at_least(arch, n, S, delta):
    _, o = io(arch, n)
    etas = [z3.Real('eta_' + str(x)) for x in o]
    body = z3.Implies(z3.And([z3.And(e <= zq(delta), -e <= zq(delta)) for e in etas]),
                      z3.substitute(S, *[(x, x + e) for x, e in zip(o, etas)]))
    return decide(alternation(arch, n, Q_('A', etas, body)))

def verify(arch, AP, GP, contracts, want=True, names=None):
    zAP, zGP = unroll(AP, 0, arch.H), unroll(GP, 0, arch.H)
    S = {n: S_of(*contracts[n]) for n in contracts}
    ok1, _ = valid(z3.Implies(z3.And(zAP, *S.values()), zGP))
    ok2 = all(valid(z3.Implies(z3.And(zAP, *S.values()), contracts[n][0]))[0] for n in contracts)
    expect("(C1), (C2)", (ok1, ok2), (want, True))
    for n in names or sorted(contracts):
        expect(f"{n} receptive, causal (delay {arch.comps[n].delay})",
               (receptive(arch, n, S[n]), causal(arch, n, S[n])), (True, True))

def print_contracts(arch, res, ref=None):
    say("  emitted contracts (A_i, G_i):")
    for n in sorted(res['contracts'], key=lambda n: (n not in res['order'],
                                                     res['order'].index(n) if n in res['order'] else n)):
        A, G = res['contracts'][n]
        if ref and all(valid(x == y)[0] for x, y in zip((A, G), ref[1][n])):
            say(f"    {n}:  same contract as for {ref[0]} (Z3: equivalent)")
            continue
        show(f"{n}:  A = ", A)
        show(f"{' ' * len(n)}   G = ", G)

def eps_ok(arch, AP, GP, eps):
    r = decompose(arch, AP, GP, eps, False)
    return not r['stop'] and all(slack_at_least(arch, n, S_of(*r['contracts'][n]), eps) for n in r['order'])

def simplest(a, b):
    """Rational with the smallest denominator in [a, b] (0 <= a <= b)."""
    fl = a.numerator // a.denominator
    if fl == a or fl + 1 <= b:
        return Fr(fl) if fl == a else Fr(fl + 1)
    return fl + 1 / simplest(1 / (b - fl), 1 / (a - fl))

def bisect(arch, AP, GP):
    P = lambda e: eps_ok(arch, AP, GP, e)
    trace = []
    assert P(Fr(0)), "no eps >= 0 gives every obligation slack >= eps"
    trace.append((Fr(0), True))
    lo, hi = Fr(0), Fr(1)
    while P(hi):
        lo, hi = hi, 2 * hi
        assert hi <= 64
    trace.append((hi, False))
    while hi - lo > TOL:
        mid = (lo + hi) / 2
        v = P(mid)
        trace.append((mid, v))
        lo, hi = (mid, hi) if v else (lo, mid)
    s = simplest(lo, hi)
    qs = s if s < hi and P(s) else lo
    say("  bisection on eps (slack of every obligation >= eps), tolerance 1/1024:")
    say("    " + ', '.join(f"{fstr(e)}:{'yes' if v else 'no'}" for e, v in trace))
    say(f"    bracket: eps = {fstr(lo)} yes, eps = {fstr(hi)} no; smallest-denominator rational in "
        f"[{fstr(lo)}, {fstr(hi)}) with verdict yes: eps* = {fstr(qs)}")
    return qs

def run_forwarding(title, arch, AP, GP, want_eps=None):
    say('=' * 78)
    say(title)
    say(f"  H = {arch.H};  A_P and G_P unrolled:")
    SHOW_T[0] = arch.H > 0
    show("A_P = ", simp(unroll(AP, 0, arch.H)))
    show("G_P = ", unroll(GP, 0, arch.H))
    e = bisect(arch, AP, GP)
    if want_eps is not None:
        expect("eps*", e, want_eps)
    say(f"  intermediate formulas at eps = {fstr(e)}:")
    r = decompose(arch, AP, GP, e, True)
    print_contracts(arch, r)
    verify(arch, AP, GP, r['contracts'], names=r['order'])
    return r, e

# ---------------------------------------------------------------- examples
r, m, d = V('r'), V('m'), V('d')
HALF = Fr(1, 2)

def relay(H=0, delays=(0, 0)):
    return Arch(['r'], [Comp('Radio', ['r'], ['m'], delays[0]), Comp('Display', ['m'], ['d'], delays[1])], H)

def e1_shape():
    """E1: Q_2 with eps symbolic, compared with the expected four-piece formula on 0 <= eps <= 1/2."""
    say("  E1 shape check: Q_2 computed by qe2 with eps symbolic, compared on 0 <= eps <= 1/2 with")
    say("    {|m| <= 1-eps and |d-m| <= 1/2-eps} or {1-eps < m <= 1+eps and 1/2 <= d <= m+1/2-eps}")
    say("    or {-1-eps <= m < -1+eps and m-1/2+eps <= d <= -1/2} or {|m| > 1+eps}")
    e = z3.Real('eps')
    rr, mm, dd = col('r', 0), col('m', 0), col('d', 0)
    ab = lambda x, c: z3.And(x <= c, -x <= c)
    h = zq(HALF)
    q = z3.ForAll([rr], z3.Implies(z3.And(ab(rr, 1), ab(mm - rr, e)), ab(dd - rr, h)))
    res = qe2(q)
    okx, _ = valid(res == q)
    say(f"    qe2 cross-check {'ok' if okx else 'FAILED'}: parametric Q_2")
    exp = z3.Or(z3.And(ab(mm, 1 - e), ab(dd - mm, h - e)),
                z3.And(1 - e < mm, mm <= 1 + e, h <= dd, dd <= mm + h - e),
                z3.And(-1 - e <= mm, mm < -1 + e, mm - h + e <= dd, dd <= -h),
                z3.Or(mm > 1 + e, mm < -1 - e))
    ok, _ = valid(z3.Implies(z3.And(0 <= e, e <= h), res == exp))
    expect("E1 parametric Q_2 equals the expected formula", ok and okx, True)

def main():
    say("Decomposition of a global PolySTL contract over an architecture graph")
    say("'@t:' marks an atom at time t (omitted when H = 0); |e| <= c means e <= c and -e <= c.")

    # Lemma: pure projection cannot choose
    say('=' * 78)
    say("Lemma (relay, H = 0): universal projections of A_P -> G_P on single components")
    SHOW_T[0] = False
    A = relay()
    zA, zG = unroll(ABSLE(r, 1), 0, 0), unroll(ABSLE(d - r, HALF), 0, 0)
    for n in ('Display', 'Radio'):
        f = project('A', z3.Implies(zA, zG), A.ports([n]), f"Pi_ports({n})(A_P -> G_P)")
        show(f"Pi_ports({n})(A_P -> G_P) = ", f)
        expect(f"Pi_ports({n})(A_P -> G_P) and A_P is unsatisfiable", valid(z3.Not(z3.And(f, zA)))[0], True)

    # no greatest element
    say('=' * 78)
    say("No greatest acceptable delegation (relay): (eps_R, eps_D) = (1/5, 3/10) and (3/10, 1/5)")
    AP, GP = ABSLE(r, 1), ABSLE(d - r, HALF)
    Ss = []
    for er, ed in ((Fr(1, 5), Fr(3, 10)), (Fr(3, 10), Fr(1, 5))):
        ct = {'Radio': (zA, unroll(ABSLE(m - r, er), 0, 0)),
              'Display': (z3.BoolVal(True), unroll(ABSLE(d - m, ed), 0, 0))}
        say(f"  delegation (eps_R, eps_D) = ({fstr(er)}, {fstr(ed)}):")
        print_contracts(A, {'contracts': ct, 'order': ['Radio', 'Display']})
        verify(A, AP, GP, ct)
        Ss.append({n: S_of(*ct[n]) for n in ct})
    U = z3.And(zA, z3.Or(Ss[0]['Radio'], Ss[1]['Radio']), z3.Or(Ss[0]['Display'], Ss[1]['Display']))
    ok, s = valid(z3.Implies(U, zG))
    expect("(C1) for the componentwise union of the two", ok, False)
    mo = s.model() if not ok else None
    say("    Z3 counterexample: " + ', '.join(f"{v} = {mo.eval(col(v, 0), True)}" for v in 'rmd') if mo else '')
    pt = [(col('r', 0), zq(0)), (col('m', 0), zq(Fr(3, 10))), (col('d', 0), zq(Fr(3, 5)))]
    sat_u = z3.is_true(z3.simplify(z3.substitute(z3.And(U, z3.Not(zG)), *pt)))
    expect("point r = 0, m = 3/10, d = 3/5 satisfies A_P, both unions, and violates G_P", sat_u, True)

    # E1
    run_forwarding("E1 relay: r env; Radio r->m; Display m->d; A_P = |r| <= 1; G_P = |d - r| <= 1/2",
                   relay(), AP, GP, Fr(1, 4))
    e1_shape()

    # E2
    s1, s2, a, b, f = V('s1'), V('s2'), V('a'), V('b'), V('f')
    A2 = Arch(['s1', 's2'], [Comp('A', ['s1'], ['a']), Comp('B', ['s2'], ['b']),
                             Comp('Fuser', ['a', 'b'], ['f']), Comp('Logger', ['f'], ['l'])], 0)
    run_forwarding("E2 fan-in: A s1->a; B s2->b; Fuser a,b->f; Logger f->l; A_P = true; "
                   "G_P = |f - s1 - s2| <= 1", A2, TRUE, ABSLE(f - s1 - s2, 1), Fr(1, 3))

    # E3
    A3 = Arch(['r'], [Comp('C1', ['r'], ['m1']), Comp('C2', ['m1'], ['m2']), Comp('C3', ['m2'], ['d'])], 0)
    run_forwarding("E3 chain: C1 r->m1; C2 m1->m2; C3 m2->d; A_P = |r| <= 1; G_P = |d - r| <= 1/2",
                   A3, AP, GP, Fr(1, 6))

    # E4
    G4 = OR(AND(IMP(r >= 0, d >= 1), IMP(r < 0, d <= -1)), ABSLE(d - 2 * r, Fr(1, 4)))
    run_forwarding("E4 disjunctive query on the relay: A_P = |r| <= 1; "
                   "G_P = ((r >= 0 -> d >= 1) and (r < 0 -> d <= -1)) or |d - 2r| <= 1/4", relay(), AP, G4)

    # E5
    say('=' * 78)
    say("E5 capacity: Radio r1,r2->m; Display m->d1,d2; A_P = |r1| <= 1 and |r2| <= 1; "
        "G_P = |d1 - r1| <= 1/2 and |d2 - r2| <= 1/2")
    r1, r2, d1, d2 = V('r1'), V('r2'), V('d1'), V('d2')
    A5 = Arch(['r1', 'r2'], [Comp('Radio', ['r1', 'r2'], ['m']), Comp('Display', ['m'], ['d1', 'd2'])], 0)
    r5 = decompose(A5, AND(ABSLE(r1, 1), ABSLE(r2, 1)),
                   AND(ABSLE(d1 - r1, HALF), ABSLE(d2 - r2, HALF)), Fr(0), True)
    expect("E5 stops with the forwarding obstruction", 'must forward 2' in (r5['stop'] or ''), True)

    # E6
    def G6(k, quiet=True):
        trig = ALW(0, 2, IMP(ABSGT(r, HALF), EV(0, k, ABSGE(d, Fr(2, 5)))))
        qu = ALW(0, 2, IMP(ALW(0, k, ABSLE(r, HALF)), EV(k, k, ABSLE(d, Fr(1, 5)))))
        return AND(trig, qu) if quiet else trig

    say('=' * 78)
    say("E6 Lemma: with only the first conjunct, Radio (true, true), Display (true, always d = 1) is acceptable")
    A6 = relay(4, (1, 1))
    SHOW_T[0] = True
    ct = {'Radio': (z3.BoolVal(True), z3.BoolVal(True)),
          'Display': (z3.BoolVal(True), unroll(ALW(0, 4, AND(d <= 1, d >= 1)), 0, 4))}
    print_contracts(A6, {'contracts': ct, 'order': ['Radio', 'Display']})
    verify(A6, TRUE, G6(2, False), ct)
    say("  the same delegation against the full G_P (with the quiet conjunct):")
    ok, _ = valid(z3.Implies(z3.And(*[S_of(*v) for v in ct.values()]), unroll(G6(2), 0, 4)))
    expect("(C1) for the full G_P", ok, False)

    ref = None
    for k in (2, 1):
        say('=' * 78)
        say(f"E6 relay with deadline k = {k}, delays (1, 1), H = 4, A_P = true;"
            f" G_P = alw[0,2](|r| > 1/2 -> ev[0,{k}] |d| >= 2/5) and"
            f" alw[0,2](alw[0,{k}] |r| <= 1/2 -> ev[{k},{k}] |d| <= 1/5)")
        SHOW_T[0] = True
        show("G_P = ", unroll(G6(k), 0, 4))
        r6 = decompose(A6, TRUE, G6(k), Fr(0), True)
        print_contracts(A6, r6, ref)
        ref = ('k = 2', r6['contracts'])
        if k == 2:
            verify(A6, TRUE, G6(k), r6['contracts'], names=r6['order'])
        else:
            S = S_of(*r6['contracts']['Display'])
            say(f"  Display receptive (non-causal): {str(receptive(A6, 'Display', S)).lower()}")
            expect("Display causal (delay 1) at k = 1", causal(A6, 'Display', S), False)

    run_forwarding("E6 with delays (0, 0), deadline k = 2, H = 4: continuous forwarding of r",
                   relay(4, (0, 0)), TRUE, G6(2))

    say('=' * 78)
    say(f"projections computed: {STATS['proj']} (each cross-checked against its quantified input)")
    if FAILS:
        say("UNEXPECTED: " + '; '.join(FAILS))
        return 1
    say("all verdicts as expected")
    return 0

if __name__ == '__main__':
    sys.exit(main())
