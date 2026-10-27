"""Alternative path-enumeration monolithic checks (u free), same machinery as validate.mono_check except how the
property queries are discharged. mode:
  orig    : validate.mono_check itself (shared incremental solver, push/pop)        -- reference
  fresh   : every property query on a fresh default z3.Solver() holding the same assertions (non-incremental,
            so Z3 picks its QF_NRA strategy, nlsat)
  nlsat   : every property query on Then('simplify','qfnra-nlsat').solver()
  last    : as orig (shared incremental solver, push/pop), but the goal query first tries single ticks, last
            tick first: if (path and |y_t-g|^2>9) is unsat for some t, the conjunction is unsat (sound shortcut)
  lastfresh: 'last' with fresh solvers
  lastor  : 'last', and the fence atoms of all ticks of a path in one disjunctive query
  outer   : planner branches enumerated first (outer loop, own Fork), then the controller paths for each planner
            path with w bound to that path's linear terms; property queries as in 'fresh'
Usage: alt_path.py H mode timeout_s [rev]"""
import sys, time, json
sys.path.insert(0, '/Users/ryan/Research/delegate/scripts')
import z3, vcore, validate
from fractions import Fraction as Fr
from vcore import explore, planner, controller, Sym
from validate import A_f, fence_viol, d2, zv, EPS, simp, symbols

H, mode, tmo = int(sys.argv[1]), sys.argv[2], float(sys.argv[3]); rev = int(sys.argv[4]) if len(sys.argv) > 4 else 4
rho = Fr(104, 100)
stats = dict(prop_calls=0, prop_time=0.0, max_prop=0.0)

def prop_check(s, extra, deadline):
    rem = deadline - time.time()
    if rem <= 0: raise TimeoutError()
    if mode in ('last', 'lastor'):
        s.push(); s.set('timeout', max(1, int(rem * 1000))); s.add(extra); t = time.time(); r = s.check(); dt = time.time() - t; s.pop()
        stats['prop_calls'] += 1; stats['prop_time'] += dt; stats['max_prop'] = max(stats['max_prop'], dt)
        if r == z3.unknown and time.time() >= deadline: raise TimeoutError()
        return r
    if mode == 'nlsat': sv = z3.Then('simplify', 'qfnra-nlsat').solver()
    else: sv = z3.Solver()
    sv.set('timeout', max(1, int(rem * 1000)))
    sv.add(*s.assertions()); sv.add(extra)
    t = time.time(); r = sv.check(); dt = time.time() - t
    stats['prop_calls'] += 1; stats['prop_time'] += dt; stats['max_prop'] = max(stats['max_prop'], dt)
    if r == z3.unknown and time.time() >= deadline: raise TimeoutError()
    return r

def run():
    t0 = time.time(); deadline = t0 + tmo
    if mode == 'orig':
        r = validate.mono_check(None, rev, rho, H, deadline, u_free=True); r['mode'] = mode; return r
    w_, p0, dts = symbols(H)
    S = Sym()
    uu = [z3.Real('s'), z3.Real('hx'), z3.Real('hy'), z3.Real('gx'), z3.Real('gy')]
    base = [A_f(uu, p0, dts, S)]
    s_ = uu[0]; g = (uu[3], uu[4])
    npaths = 0
    def props(ys, s):
        ys = [(simp(y[0]), simp(y[1])) for y in ys]; seen = set()
        if mode == 'lastor':
            r = prop_check(s, z3.Or(*[fence_viol(y, s_) for y in ys]), deadline)
            if r != z3.unsat: return ('reject' if r == z3.sat else 'unknown', 'fence', None)
            ys_f = []
        else: ys_f = ys
        for t, y in enumerate(ys_f):
            key = (y[0].sexpr(), y[1].sexpr())
            if key in seen: continue
            seen.add(key)
            r = prop_check(s, fence_viol(y, s_), deadline)
            if r != z3.unsat: return ('reject' if r == z3.sat else 'unknown', 'fence', t)
        if mode in ('last', 'lastfresh', 'lastor'):
            for y in reversed(ys):
                if prop_check(s, d2(y, g) > EPS * EPS, deadline) == z3.unsat: return None
        r = prop_check(s, z3.And(*[d2(y, g) > EPS * EPS for y in ys]), deadline)
        if r != z3.unsat: return ('reject' if r == z3.sat else 'unknown', 'goal', None)
        return None
    try:
        if mode in ('fresh', 'nlsat', 'last', 'lastfresh', 'lastor'):
            for pc, (w, ys), s in explore(base, lambda op: (lambda w: (w, controller(w, p0, dts, op)))(planner(rev, uu, op, rho)), deadline=deadline):
                npaths += 1
                v = props(ys, s)
                if v: return dict(mode=mode, status=v[0], why=v[1], tick=v[2], paths=npaths, time=time.time() - t0, **stats)
        elif mode == 'outer':
            nplan = 0
            for pc1, w, s1 in explore(base, lambda op: planner(rev, uu, op, rho), deadline=deadline):
                nplan += 1
                w = [simp(x) for x in w]
                for pc, ys, s in explore(base + pc1, lambda op: controller(w, p0, dts, op), deadline=deadline):
                    npaths += 1
                    v = props(ys, s)
                    if v: return dict(mode=mode, status=v[0], why=v[1], tick=v[2], paths=npaths, planner_paths=nplan, time=time.time() - t0, **stats)
    except TimeoutError:
        return dict(mode=mode, status='timeout', paths=npaths, time=time.time() - t0, **stats)
    return dict(mode=mode, status='accept', paths=npaths, time=time.time() - t0, **stats)

r = run(); r.update(H=H, rev=rev)
print(json.dumps(r, default=str), flush=True)
