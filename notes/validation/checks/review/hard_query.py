"""Dump the first goal query of the u-free monolithic check that the shared incremental solver cannot decide in
10 s, then decide the same query four ways: incremental (push/pop) solver, fresh default solver, qfnra-nlsat,
and the last-tick atom alone on the incremental solver."""
import sys, time
sys.path.insert(0, '/Users/ryan/Research/delegate/scripts')
import z3, validate
from fractions import Fraction as Fr
class Found(Exception): pass
dump = {}
orig = validate.tcheck
def tch(s, deadline):
    last = s.assertions()[-1]
    if z3.is_and(last) and last.num_args() > 2:     # the goal conjunction
        s.set('timeout', 10000); r = s.check()
        if r == z3.unknown:
            dump['asserts'] = list(s.assertions()); raise Found()
        return r
    return orig(s, deadline)
validate.tcheck = tch
try: validate.mono_check(None, 4, Fr(104, 100), 8, time.time() + 600, u_free=True)
except Found: pass
a = dump['asserts']; goal = a[-1]; rest = a[:-1]
open('/Users/ryan/Research/delegate/notes/validation/checks/review/hard_query.smt2', 'w').write(z3.Solver().from_string('') or '' if False else '')
sv = z3.Solver(); sv.add(*a); open('/Users/ryan/Research/delegate/notes/validation/checks/review/hard_query.smt2', 'w').write(sv.sexpr() + '\n(check-sat)\n')
def run(name, mk, extra):
    s = mk(); s.set('timeout', 60000)
    if name == 'incremental':
        s.add(*rest); s.push(); s.add(extra)
    else: s.add(*rest, extra)
    t = time.time(); r = s.check(); print('%-28s %-8s %.2f s' % (name, r, time.time() - t), flush=True)
lastatom = goal.arg(goal.num_args() - 1)
print('goal conjunction has', goal.num_args(), 'atoms; last atom:', lastatom)
run('incremental', z3.Solver, goal)
run('fresh default', z3.Solver, goal)
run('qfnra-nlsat', lambda: z3.Then('simplify', 'qfnra-nlsat').solver(), goal)
run('incremental, last atom only', lambda: z3.Solver(), lastatom)
