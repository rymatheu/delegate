"""Vocabulary for delegate proposals (read by scripts/agentic/check.py).

A proposal is a Python file that defines four functions built ONLY from the operations below, plain arithmetic
(+, -, *, numeric constants) and the comparisons <, <=, >, >=, ==:

    A1(u)        -> planner assumption, over the planner input u
    G1(u, w)     -> planner guarantee, over the input u and the mission w
    A2(w)        -> controller assumption, over the mission w
    G2(w, e, y)  -> controller guarantee, over the mission w, the environment e and the targets y

Arguments (always passed positionally, always of these shapes):
    u = U(s, h, g)       s: fence half-side (the fence is [-s, s]^2); h = (hx, hy) home; g = (gx, gy) goal
    w = W(w1, w2)        w1 = (w1x, w1y), w2 = (w2x, w2y): the two waypoints of the mission
    e = E(p0, dts)       p0 = (px, py) start position; dts: Ticks of H tick lengths dt_0..dt_{H-1}
    y                    Ticks of H+1 targets y_0..y_H, each a pair (x, y)
U, W, E are namedtuples (u.s, u.h, u.g; w.w1, w.w2; e.p0, e.dts) and unpack (s, h, g = u). Points are tuples.

The same function is called by the checker with Z3 terms (symbolic check) and with numbers (sampling, replay of
counterexamples), so it must not use Python `and`, `or`, `not`, `if`, chained comparisons (a <= x <= b),
abs(), max(), min(), math.*, or loops over Z3 values; use And/Or/Not/Implies/Ite/Abs/Max/Min instead.
Loops over a fixed Python range are fine.

Temporal operators: Box(seq, f) holds iff f(x) holds for every element x of seq (seq = y or e.dts), Diamond(seq, f)
iff for some element. A formula is in the POINTWISE CLASS for a sequence when that sequence is used only through
Box/Diamond over all of its ticks, each body f looks at its own element only (plus u, w, p0), and no Box/Diamond is
nested inside another. Then the checker may decide D3 on fewer ticks (see README). Indexing (y[t], y[-1]), iteration
over y or dts, len-dependent formulas or a `ticks=` window make that sequence non-pointwise; the checker then
unrolls the full horizon H = 8. Everything is still checked exactly; only the speed differs.
"""
from collections import namedtuple
from fractions import Fraction
import z3

H = 8                                    # ticks of the validation instance: y_0..y_H, dt_0..dt_{H-1}
U = namedtuple('U', 's h g')
W = namedtuple('W', 'w1 w2')
E = namedtuple('E', 'p0 dts')


# ------------------------------------------------------------------ symbolic or concrete
def _leaves(x):
    if isinstance(x, (tuple, list)):
        for a in x: yield from _leaves(a)
    elif isinstance(x, Ticks):
        for a in x._items: yield from _leaves(a)
    else:
        yield x


def is_sym(*xs):
    """True iff some argument (or a component of a tuple argument) is a Z3 term."""
    return any(isinstance(a, z3.ExprRef) for a in _leaves(xs))


def _zb(x):
    return z3.BoolVal(x) if isinstance(x, bool) else x


def Q(a, b=1):
    """Exact rational constant a/b (use instead of floats such as 0.1 that are not exact in binary)."""
    return Fraction(a, b)


# ------------------------------------------------------------------ Boolean connectives
def And(*a):
    a = [x for x in a]
    if not is_sym(*a): return all(bool(x) for x in a)
    a = [_zb(x) for x in a]
    return z3.And(*a) if len(a) != 1 else a[0]


def Or(*a):
    a = [x for x in a]
    if not is_sym(*a): return any(bool(x) for x in a)
    a = [_zb(x) for x in a]
    return z3.Or(*a) if len(a) != 1 else a[0]


def Not(a):
    return z3.Not(a) if is_sym(a) else (not a)


def Implies(a, b):
    return z3.Implies(_zb(a), _zb(b)) if is_sym(a, b) else ((not a) or bool(b))


def Ite(c, a, b):
    """If c then a else b (numbers, Booleans, or points of equal length)."""
    if isinstance(a, tuple):
        return tuple(Ite(c, x, y) for x, y in zip(a, b))
    if not is_sym(c, a, b): return a if c else b
    if not is_sym(c): return a if c else b
    return z3.If(c, _zb(a), _zb(b))


# ------------------------------------------------------------------ arithmetic
def Abs(x):
    return z3.If(x >= 0, x, -x) if is_sym(x) else abs(x)


def Max(*a):
    r = a[0]
    for x in a[1:]: r = z3.If(r >= x, r, x) if is_sym(r, x) else (r if r >= x else x)
    return r


def Min(*a):
    r = a[0]
    for x in a[1:]: r = z3.If(r <= x, r, x) if is_sym(r, x) else (r if r <= x else x)
    return r


def sub(a, b): return tuple(x - y for x, y in zip(a, b))
def add(a, b): return tuple(x + y for x, y in zip(a, b))
def scale(k, a): return tuple(k * x for x in a)
def mid(a, b): return tuple((x + y) / 2 for x, y in zip(a, b))
def cross(a, b): return a[0] * b[1] - a[1] * b[0]          # NONLINEAR when both arguments are symbolic
def dot(a, b): return a[0] * b[0] + a[1] * b[1]            # NONLINEAR when both arguments are symbolic


def ninf(v):
    """Infinity norm max(|v_x|, |v_y|) as a term (piecewise linear). Prefer the inf_* atoms in comparisons."""
    return Max(Abs(v[0]), Abs(v[1]))


def nsq(v):
    """Squared Euclidean norm v_x^2 + v_y^2 (NONLINEAR). Compare it with a squared constant."""
    return v[0] * v[0] + v[1] * v[1]


def dist_inf(a, b): return ninf(sub(a, b))
def dist_sq(a, b):
    """Squared Euclidean distance (NONLINEAR). Compare it with a squared constant, e.g. dist_sq(y, g) <= 3 * 3; the
    checker then also reasons with the triangle inequality between such distances (see README)."""
    t = nsq(sub(a, b))
    rec = _REC[0]
    if rec is not None and isinstance(t, z3.ExprRef): rec.dist[t.get_id()] = (tuple(a), tuple(b), t)
    return t


# linear atoms for the infinity norm (no case split on signs; these keep a query in linear arithmetic)
def inf_le(v, c): return And(v[0] <= c, -v[0] <= c, v[1] <= c, -v[1] <= c)      # |v|_inf <= c
def inf_lt(v, c): return And(v[0] < c, -v[0] < c, v[1] < c, -v[1] < c)          # |v|_inf <  c
def inf_ge(v, c): return Or(v[0] >= c, -v[0] >= c, v[1] >= c, -v[1] >= c)       # |v|_inf >= c
def inf_gt(v, c): return Or(v[0] > c, -v[0] > c, v[1] > c, -v[1] > c)           # |v|_inf >  c


def in_box(p, lo, hi):
    """lo <= p_x <= hi and lo <= p_y <= hi."""
    return And(lo <= p[0], p[0] <= hi, lo <= p[1], p[1] <= hi)


def near_segment_inf(p, a, b, r):
    """p lies within infinity-distance r of the segment [a, b] (derived from the operations above, NONLINEAR):
    p is in the bounding box of a, b grown by r, and |(p - a) x (b - a)| <= r (|b_x - a_x| + |b_y - a_y|)."""
    d = sub(b, a); c = cross(sub(p, a), d)
    k = r * (Abs(d[0]) + Abs(d[1]))
    return And(Min(a[0], b[0]) - r <= p[0], p[0] <= Max(a[0], b[0]) + r,
               Min(a[1], b[1]) - r <= p[1], p[1] <= Max(a[1], b[1]) + r, c <= k, -c <= k)


# ------------------------------------------------------------------ tick sequences and temporal operators
class Recorder:
    """Collects, while a formula is built symbolically, how each tick sequence is used (pointwise class test)."""
    def __init__(self):
        self.reasons = {}        # sequence name -> list of reasons it is not pointwise
        self.ops = {}            # z3 ast id -> (kind, sequence name, term); kind 'box' | 'diamond'
        self.depth = 0
        self.dist = {}           # z3 ast id of a dist_sq term -> (point a, point b, term)
    def bad(self, name, why):
        self.reasons.setdefault(name, [])
        if why not in self.reasons[name]: self.reasons[name].append(why)


_REC = [None]


def recording(rec):
    """Context: install a Recorder for the formulas built inside the `with` block."""
    class _Ctx:
        def __enter__(self): _REC[0] = rec; return rec
        def __exit__(self, *a): _REC[0] = None
    return _Ctx()


class Ticks:
    """Read-only sequence of per-tick values (y or dts). Use it through Box/Diamond; direct access is allowed but
    makes the sequence non-pointwise (full unrolling)."""
    def __init__(self, items, name):
        self._items, self.name = list(items), name
    def __len__(self): return len(self._items)
    def __getitem__(self, i):
        if _REC[0] is not None: _REC[0].bad(self.name, 'indexed directly (%s[%r])' % (self.name, i))
        return self._items[i]
    def __iter__(self):
        if _REC[0] is not None: _REC[0].bad(self.name, 'iterated directly')
        return iter(self._items)
    def __repr__(self): return 'Ticks(%s, %r)' % (self.name, self._items)


def _vars(x):
    from z3.z3util import get_vars
    out = set()
    for a in _leaves(x):
        if isinstance(a, z3.ExprRef): out |= {str(v) for v in get_vars(a)}
    return out


def _temporal(kind, seq, f, ticks):
    rec = _REC[0]
    if isinstance(seq, Ticks):
        items, name = seq._items, seq.name
    else:
        items, name = list(seq), None
    if rec is not None:
        if name is None: rec.bad('?', '%s over a plain list' % kind)
        if ticks is not None: rec.bad(name, '%s over a window of ticks' % kind)
        if rec.depth > 0: rec.bad(name, '%s nested inside another temporal operator' % kind)
    idx = list(range(len(items))) if ticks is None else list(ticks)
    if rec is not None: rec.depth += 1
    try:
        bodies = [f(items[t]) for t in idx]
    finally:
        if rec is not None: rec.depth -= 1
    if rec is not None and name is not None and is_sym(*bodies):
        tv = [_vars(it) for it in items]
        for t, bd in zip(idx, bodies):
            if not isinstance(bd, z3.ExprRef): continue
            other = set().union(*[tv[k] for k in range(len(items)) if k != t]) - tv[t]
            if _vars(bd) & other:
                rec.bad(name, '%s body at tick %d refers to another tick' % (kind, t)); break
    r = And(*bodies) if kind == 'Box' else Or(*bodies)
    if rec is not None and isinstance(r, z3.ExprRef) and name is not None:
        rec.ops[r.get_id()] = (kind, name, r)
    return r


def Box(seq, f, ticks=None):
    """Always: f(x) for every element x of seq (optionally only at the tick indices in `ticks`)."""
    return _temporal('Box', seq, f, ticks)


def Diamond(seq, f, ticks=None):
    """Eventually: f(x) for some element x of seq (optionally only at the tick indices in `ticks`)."""
    return _temporal('Diamond', seq, f, ticks)


# ------------------------------------------------------------------ adapter for code written over vcore's `op`
def vc_op(*args):
    """An arithmetic interface of scripts/vcore.py matching the arguments: Sym() for Z3 terms, Num() otherwise.
    Lets a proposal or witness call vcore functions (A1, G1, Vw, planner, ...) on the checker's arguments."""
    import os, sys
    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    from vcore import Num, Sym
    return Sym() if is_sym(*args) else Num()


def flat_u(u): return (u.s, u.h[0], u.h[1], u.g[0], u.g[1])
def flat_w(w): return (w.w1[0], w.w1[1], w.w2[0], w.w2[1])
def mk_u(f): return U(f[0], (f[1], f[2]), (f[3], f[4]))
def mk_w(f): return W((f[0], f[1]), (f[2], f[3]))
