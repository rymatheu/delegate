"""Profile the monolithic u-free check of scripts/validate.py: time every solver call (branch checks and property
queries) and report the slowest one, to find why it times out. Read-only use of scripts/."""
import sys, time, os, json
sys.path.insert(0, '/Users/ryan/Research/delegate/scripts')
import z3, vcore, validate
from fractions import Fraction as Fr

H = int(sys.argv[1]); TMO = float(sys.argv[2]); out = sys.argv[3]
log = []
orig_chk = vcore.Fork._chk
def chk(self):
    t = time.time(); r = orig_chk(self); dt = time.time() - t
    log.append(('branch', len(self.dec), str(r), dt))
    if dt > 5: print('slow branch check %.1fs at depth %d -> %s' % (dt, len(self.dec), r), flush=True); print(self.s.assertions()[-3:], flush=True)
    return r
vcore.Fork._chk = chk
orig_t = validate.tcheck
def tch(s, deadline):
    t = time.time(); r = orig_t(s, deadline); dt = time.time() - t
    log.append(('prop', None, str(r), dt))
    if dt > 5: print('slow property query %.1fs -> %s' % (dt, r), flush=True); print(s.assertions()[-1], flush=True)
    return r
validate.tcheck = tch
rho = Fr(104, 100)
t0 = time.time()
r = validate.mono_check(None, 4, rho, H, time.time() + TMO, u_free=True)
r['wall'] = time.time() - t0
slow = sorted(log, key=lambda x: -x[3])[:10]
r['slowest'] = slow; r['n_calls'] = len(log); r['sum_branch'] = sum(x[3] for x in log if x[0] == 'branch'); r['sum_prop'] = sum(x[3] for x in log if x[0] == 'prop')
print(json.dumps(r, default=str, indent=1))
json.dump(r, open(out, 'w'), default=str, indent=1)
