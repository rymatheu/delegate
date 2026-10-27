"""Core models for scripts/validate.py: arithmetic interfaces, controller M2, planner revisions M1, contracts."""
import math
import z3

Q = lambda a, b=1: z3.Q(a, b) if b != 1 else z3.RealVal(a)
# ---------------------------------------------------------------- parameters (validation instance)
CTRL = dict(vmax=40, amax=18, dtnom=1, R=2, lmin=5, lmax=100, D=10, K=10, dtmin=(1, 2), dtmax=(3, 2), B=100)
TOP = dict(slo=25, shi=50, hm=3, gout=(1, 2), delta=1, eps=3, dtlo=(9, 10), dthi=(11, 10), eta=(1, 2))
fr = lambda x: x[0] / x[1] if isinstance(x, tuple) else x


class Num:
    """Concrete arithmetic on Python floats (or Fractions)."""
    sym = False
    def ite(self, c, a, b): return a if c else b
    def And(self, *a): return all(a)
    def Or(self, *a): return any(a)
    def Not(self, a): return not a
    def min(self, a, b): return a if a <= b else b
    def max(self, a, b): return a if a >= b else b
    def let(self, x, name=''): return x
    def c(self, x): return fr(x)


class Sym:
    """Symbolic arithmetic on Z3 Reals; `let` names an intermediate value (one state variable per tick)."""
    sym = True
    def __init__(self, pre=''): self.side, self.k, self.pre = [], 0, pre
    def ite(self, c, a, b): return z3.If(c, a, b)
    def And(self, *a): return z3.And(*a)
    def Or(self, *a): return z3.Or(*a)
    def Not(self, a): return z3.Not(a)
    def min(self, a, b): return z3.If(a <= b, a, b)
    def max(self, a, b): return z3.If(a >= b, a, b)
    def let(self, x, name='v'):
        self.k += 1; z = z3.Real('%s%s_%d' % (self.pre, name, self.k)); self.side.append(z == x); return z
    def c(self, x): return Q(*x) if isinstance(x, tuple) else Q(x)


def le_inf(d, c, op):  # |d|_inf <= c as four linear atoms (no case split on signs)
    return op.And(d[0] <= c, -d[0] <= c, d[1] <= c, -d[1] <= c)


def lt_inf(d, c, op):  # |d|_inf < c
    return op.And(d[0] < c, -d[0] < c, d[1] < c, -d[1] < c)


def controller(w, p0, dts, op, P=CTRL):
    """M2: targets y_0..y_H (H=len(dts)) for mission w=(w1x,w1y,w2x,w2y), start p0, measured tick lengths dts.
    Guards and what they feed. [V] leg 2: l_min<=|w2-w1|_inf<=l_max; waypoints inside the box |.|_inf<=B (upload
    range check). [P] leg 1: l_min<=|w1-p0|_inf<=l_max; start inside the box. A mission failing a length or box
    guard is rejected: the target holds at p0. [P] dt is clamped into [dt_min,dt_max]; a tick whose measured dt
    the clamp changes is held (no advance), so P keeps dt inside the range. [tube chain] fast-waypoint handover
    when the rest of leg 1 is below WP_RADIUS R (inf-norm): leg 2 starts and the rest of leg 1 is blended out over
    two ticks (halved, then dropped), which moves the target off the polyline by less than R/2."""
    vmax, amax, R, lmin, lmax, D, K, B = (P[k] for k in ('vmax', 'amax', 'R', 'lmin', 'lmax', 'D', 'K', 'B'))
    w1, w2 = (w[0], w[1]), (w[2], w[3])
    d1 = (w1[0] - p0[0], w1[1] - p0[1]); d2 = (w2[0] - w1[0], w2[1] - w1[1])
    ok = op.And(op.Not(lt_inf(d2, lmin, op)), le_inf(d2, lmax, op), le_inf(w1, B, op), le_inf(w2, B, op),
                op.Not(lt_inf(d1, lmin, op)), le_inf(d1, lmax, op), le_inf(p0, B, op))
    def cls(d):                    # length class: |d|_inf in ((n-1)D, nD]; returns 1/(nD), bounded loop over K
        inv = op.c((1, K * D))
        for n in range(K - 1, 0, -1): inv = op.ite(le_inf(d, n * D, op), op.c((1, n * D)), inv)
        return inv
    r1, r2 = cls(d1), cls(d2)                                   # fraction of a leg per metre (class bound)
    a, b, v, sw, bl = 0, 0, 0, False, False                     # leg fractions, speed (m/s), handover, blending
    tgt = lambda a, b: (op.ite(ok, p0[0] + a * d1[0] + b * d2[0], p0[0]), op.ite(ok, p0[1] + a * d1[1] + b * d2[1], p0[1]))
    ys = [tgt(a, b)]
    dv, T0 = amax * P['dtnom'], P['dtnom']                      # speed change per tick (acceleration cap)
    for dtm in dts:
        dt = op.min(op.max(dtm, op.c(P['dtmin'])), op.c(P['dtmax']))      # clamp of the measured dt
        run = op.And(dt <= dtm, dtm <= dt)                      # clamp active: tick held
        brake = op.And(sw, v * v * r2 >= 2 * amax * (1 - b))    # trapezoid: decelerate before w2
        vn = op.ite(brake, op.max(v - dv, dv), op.min(v + dv, vmax))
        an = op.ite(sw, op.ite(bl, 1, 1 - (1 - a) / 2), op.min(a + vn * T0 * r1, 1))   # leg 1, blend-out
        bn = op.ite(sw, op.min(b + vn * T0 * r2, 1), 0)         # leg 2 runs once handed over
        swn = op.Or(sw, lt_inf(((1 - an) * d1[0], (1 - an) * d1[1]), R, op))           # handover inside R
        a, b, v, bl, sw = (op.ite(run, an, a), op.ite(run, bn, b), op.ite(run, vn, v),
                           op.ite(run, sw, bl), op.ite(run, swn, sw))
        ys.append(tgt(a, b))
    return ys


# ---------------------------------------------------------------- planner revisions M1 (functions of u only)
def planner(rev, u, op, m, P=CTRL, T=TOP):
    """M1 revision rev in 1..4 for u=(s,hx,hy,gx,gy); m is the inward margin the designer reads off G1 (rho_j*).
    R1: straight line home->goal, cut at the midpoint (the wire carries two legs); no margin, no short-leg case.
    R2: goal clipped into the fence shrunk by m, w1 = midpoint of home and w2; legs too short when goal near home.
    R3: R4 with the margin applied with the wrong sign (clip to s+m): goals just outside the fence are kept.
    R4: R2 plus a short-leg branch: if |h-w2|_inf < 2(l_min+delta), w1 := h moved 20 m along x towards the centre."""
    s, hx, hy, gx, gy = u
    if rev == 1:
        return ((hx + gx) / 2, (hy + gy) / 2, gx, gy)
    mm = -m if rev == 3 else m
    clip = lambda x: op.min(op.max(x, -(s - mm)), s - mm)
    w2 = (clip(gx), clip(gy))
    mid = ((hx + w2[0]) / 2, (hy + w2[1]) / 2)
    if rev == 2:
        return (mid[0], mid[1], w2[0], w2[1])
    near = op.And(w2[0] - hx < 12, hx - w2[0] < 12, w2[1] - hy < 12, hy - w2[1] < 12)   # 12 = 2(l_min+delta)
    side = op.ite(hx < 0, 20, -20)
    return (op.ite(near, hx + side, mid[0]), op.ite(near, hy, mid[1]), w2[0], w2[1])


# ---------------------------------------------------------------- closed-form contracts (validation instance)
def inorm(z, op):
    ab = lambda x: op.max(x, -x)
    return op.max(ab(z[0]), ab(z[1]))


def A1(u, op, T=TOP):
    """A1 = exists_{E,Y} A: the planner-input part of A (the dt range of A is nonempty)."""
    s, hx, hy, gx, gy = u
    return op.And(T['slo'] <= s, s <= T['shi'], inorm((hx, hy), op) <= s - T['hm'], inorm((gx, gy), op) <= s + op.c(T['gout']))


def Vw(w, op, P=CTRL):
    L2 = inorm((w[2] - w[0], w[3] - w[1]), op)
    return op.And(P['lmin'] <= L2, L2 <= P['lmax'], inorm(w[:2], op) <= P['B'], inorm(w[2:], op) <= P['B'])


def G1(u, w, rho, op, P=CTRL, T=TOP):
    """G1 = V and (not A1 or [(ii) and (iii) and (iv)]), Section 6 recomputed for the inf-norm start box and tube.
    (ii) every start in A gives l_min<=|w1-p0|_inf<=l_max; (iii) the rho-tube around every start and both legs
    lies in the fence; (iv) the eta-disc at w2 lies in the eps-disc at g."""
    s, hx, hy, gx, gy = u
    dl, eps, eta = T['delta'], T['eps'], op.c(T['eta'])
    L = inorm((w[0] - hx, w[1] - hy), op)
    core = op.And(P['lmin'] + dl <= L, L <= P['lmax'] - dl, inorm((hx, hy), op) <= s - rho - dl,
                  inorm(w[:2], op) <= s - rho, inorm(w[2:], op) <= s - rho,
                  (w[2] - gx) * (w[2] - gx) + (w[3] - gy) * (w[3] - gy) <= (eps - eta) * (eps - eta))
    return op.And(Vw(w, op, P), op.Or(op.Not(A1(u, op, T)), core))


def bad_closed(u, rho, T=TOP, P=CTRL):
    """Bad = A1 and no mission meets G1 (closed form): ||h||_inf > s-rho-delta, or no w2 in F_{s-rho} within
    eps-eta of g. (A w1 always exists for s>=25: shown by the R4 construction.)"""
    s, hx, hy, gx, gy = u
    if not A1(u, Num(), T): return False
    c = s - rho; q = (min(max(gx, -c), c), min(max(gy, -c), c))
    return max(abs(hx), abs(hy)) > s - rho - T['delta'] or (gx - q[0]) ** 2 + (gy - q[1]) ** 2 > (T['eps'] - fr(T['eta'])) ** 2


# ---------------------------------------------------------------- bounded model checking by path enumeration
class Infeasible(Exception):
    pass


class Fork:
    """Symbolic arithmetic that splits on every data-dependent branch (ite/min/max on a symbolic condition).
    Values are exact rationals or Z3 terms; along one path every quantity the code computes from guards is a
    rational, and positions are linear in (w, p0). A Z3 solver holding the assumptions prunes infeasible branches.
    explore() enumerates all feasible paths (depth first); this is exhaustive bounded model checking."""
    sym = True
    def __init__(self, solver, prefix, deadline=None):
        self.s, self.prefix, self.dec, self.alts, self.pc = solver, prefix, [], [], []
        self.deadline = deadline
    def _chk(self):
        if self.deadline is not None:
            rem = self.deadline - __import__('time').time()
            if rem <= 0: raise TimeoutError()
            self.s.set('timeout', max(1, int(rem * 1000)))
        r = self.s.check()
        if r == z3.unknown and self.deadline is not None and __import__('time').time() >= self.deadline: raise TimeoutError()
        return r
    def c(self, x): return fr_exact(x)
    def _b(self, c):
        if isinstance(c, (bool, z3.BoolRef)): return c
        return bool(c)
    def branch(self, c):
        c = self._b(c)
        if isinstance(c, bool): return c
        c = z3.simplify(c)
        if z3.is_true(c): return True
        if z3.is_false(c): return False
        k = len(self.dec)
        if k < len(self.prefix):
            d = self.prefix[k]
        else:
            self.s.push(); self.s.add(c); t = self._chk() != z3.unsat; self.s.pop()        # unknown: keep the branch
            self.s.push(); self.s.add(z3.Not(c)); f = self._chk() != z3.unsat; self.s.pop()
            if not (t or f): raise Infeasible()
            d = t
            if t and f: self.alts.append(self.dec + [False])
        self.dec.append(d)
        lit = c if d else z3.Not(c)
        self.s.add(lit); self.pc.append(lit)
        return d
    def ite(self, c, a, b): return a if self.branch(c) else b
    def And(self, *a):
        a = [self._b(x) for x in a]
        if any(x is False for x in a): return False
        r = [x for x in a if not isinstance(x, bool)]
        return True if not r else (r[0] if len(r) == 1 else z3.And(*r))
    def Or(self, *a):
        a = [self._b(x) for x in a]
        if any(x is True for x in a): return True
        r = [x for x in a if not isinstance(x, bool)]
        return False if not r else (r[0] if len(r) == 1 else z3.Or(*r))
    def Not(self, a):
        a = self._b(a); return (not a) if isinstance(a, bool) else z3.Not(a)
    def min(self, a, b): return a if self.branch(a <= b) else b
    def max(self, a, b): return a if self.branch(a >= b) else b
    def let(self, x, name=''): return x


from fractions import Fraction
def fr_exact(x):
    return Fraction(x[0], x[1]) if isinstance(x, tuple) else Fraction(x)


def explore(base, fn, tmo_ms=None, deadline=None):
    """Yield (path condition, output of fn(op)) for every feasible path; base = list of assumption formulas."""
    stack = [[]]
    while stack:
        if deadline is not None and __import__('time').time() > deadline: raise TimeoutError()
        prefix = stack.pop()
        s = z3.Solver()
        if tmo_ms: s.set('timeout', tmo_ms)
        s.add(*base)
        op = Fork(s, prefix, deadline)
        try:
            out = fn(op)
        except Infeasible:
            continue
        stack.extend(op.alts)
        yield op.pc, out, s
