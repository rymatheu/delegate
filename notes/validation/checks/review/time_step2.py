"""Time step 2 (validate.step2) and the planner check at one horizon, single process, for a like-for-like
comparison with alt_path.py on the same machine state. Usage: time_step2.py H"""
import sys, time, json
sys.path.insert(0, '/Users/ryan/Research/delegate/scripts')
import validate
from fractions import Fraction as Fr
H = int(sys.argv[1])
chain = [Fr(94, 100) + j * Fr(1, 20) for j in range(8)]
t0 = time.time(); r = validate.step2(H, chain, 300); t2 = time.time() - t0
pc = validate.planner_check(4, Fr(104, 100), Fr(104, 100), time.time() + 600)
print(json.dumps(dict(H=H, jstar=r['jstar'], certified=r['certified'], reach=r['reach']['status'], step2_total=round(r['total_time'], 2), wall=round(t2, 2),
                      checks=[(c['j'], c['status'], round(c['time'], 2)) for c in r['checks']], planner=pc['status'], planner_time=round(pc['time'], 3))), flush=True)
