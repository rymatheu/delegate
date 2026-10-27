"""Alternative monolithic encodings: one Z3 formula for planner R4 composed with controller M2 unrolled over H ticks,
u free, query A and not G. Variants:
  enc=ite   : the code run on vcore.Sym (nested If terms, as the paper's single-formula encoding of E2)
  enc=state : standard BMC transition encoding, one fresh Real/Bool per state variable per tick
  split=0/1/2 : whole not-G in one query; one query per disjunct of not-G (fence side x tick, goal); as 1 but the
              goal disjunct replaced by its last-tick atom |y_H-g|^2>9 (unsat of it implies unsat of the goal disjunct)
  solver    : default | nlsat (Then('simplify','qfnra-nlsat')) | arith2 (smt.arith.solver=2)
Every variable is bounded (A bounds u, p0, dt; state variables bounded by their ranges).
Usage: alt_single.py H enc split solver timeout_s"""
import sys, time, json
sys.path.insert(0, '/Users/ryan/Research/delegate/scripts')
import z3
from fractions import Fraction as Fr
import vcore
from vcore import CTRL, TOP, Sym, planner, le_inf, lt_inf, A1
from validate import A_f, fence_viol, d2, zv, EPS

H, enc, split, solver, tmo = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), sys.argv[4], float(sys.argv[5])
rho = Fr(104, 100)

class StateSym(Sym):
    """Sym whose controller loop state is named per tick (transition-relation BMC)."""
    pass

def controller_state(w, p0, dts, op, P=CTRL):
    """Same code as vcore.controller, but the loop state (a,b,v,sw,bl) is a fresh variable per tick with an
    equality to its update (standard BMC unrolling), and bounds on each state variable."""
    vmax, amax, R, lmin, lmax, D, K, B = (P[k] for k in ('vmax', 'amax', 'R', 'lmin', 'lmax', 'D', 'K', 'B'))
    w1, w2 = (w[0], w[1]), (w[2], w[3])
    d1 = (w1[0] - p0[0], w1[1] - p0[1]); d2_ = (w2[0] - w1[0], w2[1] - w1[1])
    ok = op.And(op.Not(lt_inf(d2_, lmin, op)), le_inf(d2_, lmax, op), le_inf(w1, B, op), le_inf(w2, B, op),
                op.Not(lt_inf(d1, lmin, op)), le_inf(d1, lmax, op), le_inf(p0, B, op))
    okv = z3.Bool('ok'); side = [okv == ok]
    def cls(d):
        inv = op.c((1, K * D))
        for n in range(K - 1, 0, -1): inv = op.ite(le_inf(d, n * D, op), op.c((1, n * D)), inv)
        return inv
    r1v, r2v = z3.Real('r1'), z3.Real('r2'); side += [r1v == cls(d1), r2v == cls(d2_)]
    side += [r1v >= Fr(1, 100), r1v <= Fr(1, 10), r2v >= Fr(1, 100), r2v <= Fr(1, 10)]
    a, b, v, sw, bl = z3.RealVal(0), z3.RealVal(0), z3.RealVal(0), z3.BoolVal(False), z3.BoolVal(False)
    tgt = lambda a, b: (z3.If(okv, p0[0] + a * d1[0] + b * d2_[0], p0[0]), z3.If(okv, p0[1] + a * d1[1] + b * d2_[1], p0[1]))
    ys = [tgt(a, b)]
    dv, T0 = amax * P['dtnom'], P['dtnom']
    for t, dtm in enumerate(dts):
        dt = op.min(op.max(dtm, op.c(P['dtmin'])), op.c(P['dtmax']))
        run = op.And(dt <= dtm, dtm <= dt)
        brake = op.And(sw, v * v * r2v >= 2 * amax * (1 - b))
        vn = op.ite(brake, op.max(v - dv, dv), op.min(v + dv, vmax))
        an = op.ite(sw, op.ite(bl, 1, 1 - (1 - a) / 2), op.min(a + vn * T0 * r1v, 1))
        bn = op.ite(sw, op.min(b + vn * T0 * r2v, 1), 0)
        swn = op.Or(sw, lt_inf(((1 - an) * d1[0], (1 - an) * d1[1]), R, op))
        A_, B_, V_ = z3.Real('a%d' % (t + 1)), z3.Real('b%d' % (t + 1)), z3.Real('v%d' % (t + 1))
        SW, BL = z3.Bool('sw%d' % (t + 1)), z3.Bool('bl%d' % (t + 1))
        side += [A_ == z3.If(run, an, a), B_ == z3.If(run, bn, b), V_ == z3.If(run, vn, v),
                 BL == z3.If(run, sw, bl), SW == z3.If(run, swn, sw),
                 A_ >= 0, A_ <= 1, B_ >= 0, B_ <= 1, V_ >= 0, V_ <= vmax]
        a, b, v, sw, bl = A_, B_, V_, SW, BL
        ys.append(tgt(a, b))
    return ys, side

u = [z3.Real('s'), z3.Real('hx'), z3.Real('hy'), z3.Real('gx'), z3.Real('gy')]
p0 = [z3.Real('px'), z3.Real('py')]; dts = [z3.Real('dt%d' % t) for t in range(H)]
S = Sym()
A = A_f(u, p0, dts, S)
w = planner(4, u, S, rho)
side = []
if enc == 'ite':
    ys = vcore.controller(w, p0, dts, S)
else:
    wv = [z3.Real('w%d' % i) for i in range(4)]
    side += [wv[i] == w[i] for i in range(4)] + [x >= -100 for x in wv] + [x <= 100 for x in wv]
    ys, sd = controller_state(wv, p0, dts, S); side += sd
s_ = u[0]; g = (u[3], u[4])
parts = [fence_viol(y, s_) for y in ys] if split else []
goal = z3.And(*[d2(y, g) > EPS * EPS for y in ys])
if split == 2:   # fence parts per (side, tick); goal part strengthened to the last tick only (sound if unsat)
    parts = [y[0] > s_ for y in ys] + [-y[0] > s_ for y in ys] + [y[1] > s_ for y in ys] + [-y[1] > s_ for y in ys] + [d2(ys[-1], g) > EPS * EPS]
elif split:
    parts = [y[0] > s_ for y in ys] + [-y[0] > s_ for y in ys] + [y[1] > s_ for y in ys] + [-y[1] > s_ for y in ys] + [goal]
else:
    parts = [z3.Or(*[fence_viol(y, s_) for y in ys], goal)]

def mk():
    if solver == 'default': sv = z3.Solver()
    elif solver == 'nlsat': sv = z3.Then('simplify', 'qfnra-nlsat').solver()
    elif solver == 'arith2': sv = z3.Solver(); sv.set('arith.solver', 2) if False else None; z3.set_param('smt.arith.solver', 2); sv = z3.Solver()
    elif solver == 'nlsat2': sv = z3.Then('simplify', 'elim-term-ite', 'purify-arith', 'qfnra-nlsat').solver()
    return sv

t0 = time.time(); deadline = t0 + tmo; verdict = 'accept'; detail = []
for i, part in enumerate(parts):
    rem = deadline - time.time()
    if rem <= 0: verdict = 'timeout'; break
    sv = mk(); sv.set('timeout', max(1, int(rem * 1000)))
    sv.add(A, *S.side, *side, part)
    t1 = time.time()
    try:
        r = sv.check()
    except z3.Z3Exception as ex:
        r = 'error: %s' % ex
    detail.append((i, str(r), round(time.time() - t1, 3)))
    if str(r) == 'sat': verdict = 'reject'; break
    if str(r) != 'unsat':
        verdict = 'timeout' if time.time() >= deadline - 0.5 else 'unknown/' + str(r); break
res = dict(H=H, enc=enc, split=split, solver=solver, verdict=verdict, time=round(time.time() - t0, 3), nparts=len(parts), detail=detail[-5:], nq=len(detail))
print(json.dumps(res), flush=True)
