"""Find the call that hangs in the u-free monolithic check: record the call in flight when the deadline hits."""
import sys, time, json
sys.path.insert(0, '/Users/ryan/Research/delegate/scripts')
import z3, vcore, validate
from fractions import Fraction as Fr
H = int(sys.argv[1]); TMO = float(sys.argv[2])
cur = {}; done = []
orig_chk = vcore.Fork._chk
def chk(self):
    cur.clear(); cur.update(kind='branch', depth=len(self.dec), t=time.time(), last=str(self.s.assertions()[-1])[:600], npc=len(self.pc))
    r = orig_chk(self); done.append(('branch', time.time() - cur['t'])); cur.clear(); return r
vcore.Fork._chk = chk
orig_t = validate.tcheck
def tch(s, deadline):
    cur.clear(); cur.update(kind='prop', t=time.time(), last=str(s.assertions()[-1])[:600])
    r = orig_t(s, deadline); done.append(('prop', time.time() - cur['t'])); cur.clear(); return r
validate.tcheck = tch
t0 = time.time()
r = validate.mono_check(None, 4, Fr(104, 100), H, time.time() + TMO, u_free=True)
print('result', {k: v for k, v in r.items()})
print('completed calls', len(done), 'solver time %.2f' % sum(d for _, d in done), 'wall %.1f' % (time.time() - t0))
if cur: print('IN FLIGHT at deadline:', cur['kind'], 'for %.1f s' % (time.time() - cur['t']), cur.get('depth'), '\n', cur['last'])
