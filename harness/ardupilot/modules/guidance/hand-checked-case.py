# hand-checked-case.py: the working of the guidance hand-checked case, and the case file it writes.
#
#   python3 -I ardupilot/modules/guidance/hand-checked-case.py     (from the harness directory)
#
# Independent binary32 working of the guidance hand-checked case (stock WPNAV/ATC/PSC parameters,
# one 100 m straight leg north from rest, three ticks), following AC_WPNav.cpp and SCurve.cpp
# operation by operation. Every float operation is rounded to binary32 (f); a product or sum of
# two binary32 values computed in binary64 and rounded once is the correctly rounded binary32
# result. sinf, cosf, powf, sqrtf: binary64 result rounded once (assumed correctly rounded).
import math, struct, json
def f(x): return struct.unpack('<f', struct.pack('<f', x))[0]
def hx(x): return '0x%08x' % struct.unpack('<I', struct.pack('<f', x))[0]
PI = f(3.141592653589793)                 # M_PI under -cl-single-precision-constant
def mul(a,b): return f(a*b)
def div(a,b): return f(a/b)
def add(a,b): return f(a+b)
def sub(a,b): return f(a-b)
def sinf(x): return f(math.sin(x))
def cosf(x): return f(math.cos(x))
def powf(x,y): return f(x**y)
def sqrtf(x): return f(math.sqrt(x))
log = []
def note(s): log.append(s)

# --- AC_WPNav::calc_scurve_jerk_and_snap (AC_WPNav.cpp:1070-1092), ATC_RATE_R/P_MAX 0,
# ATC_INPUT_TC 0.1, ATC_ACC_R/P_MAX 1100 deg/s/s, WP_JERK 1
jerk = 1.0          # MIN(0*g, 0*g) = 0 is_zero -> WP_JERK
snap = div(mul(jerk, PI), mul(2.0, f(0.1)))
DEG_TO_RAD = div(PI, 180.0)
snap_acc = mul(mul(1100.0, DEG_TO_RAD), f(9.80665))
assert snap_acc > snap
snap = mul(snap, 0.5)
note(f'snap_max = 0.5 * (1 * pi_f) / (2 * 0.1f) = {snap!r} ({hx(snap)}); jerk_max = 1; ATC_ACC limit {snap_acc:.4g} > snap, unused')

# --- SCurve::calculate_track: origin (0,0,-10), destination (100,0,-10): seg_delta (100,0,0),
# straight, seg_length 100; generate_path: vel_max = kinematic_limit(100, 0, 10, 2.5, 1.5) = 10
# (pure horizontal), accel_max = kinematic_limit(100, 0, 2.5, 1, 1) = 2.5
Sm, Jm, Am, Vm, L = snap, jerk, 2.5, 10.0, 100.0
segs = [dict(t=0.0, typ='C', j=0.0, a=0.0, v=0.0, p=0.0)]
def calculate_path(Sm, Jm, V0, Am, Vm, L):
    tj = div(mul(Jm, PI), mul(2.0, Sm))
    At = min(min(Am, div(sub(Vm, V0), mul(2.0, tj))), div(sub(L, mul(mul(4.0, V0), tj)), mul(4.0, mul(tj, tj))))
    assert At > 0 and not (abs(At) < mul(Jm, tj))
    c1 = add(add(V0, mul(Am, tj)), div(mul(Am, Am), Jm))
    c2r = add(add(mul(div(1.0, mul(Jm, Jm)), add(mul(mul(Am, Am), Am), mul(mul(Am, Jm), add(mul(V0, 2.0), mul(mul(Am, tj), 2.0))))), mul(mul(V0, tj), 2.0)), mul(Am, mul(tj, tj)))
    assert not (Vm < c1 or L < c2r)   # solution 7: t6 t4 t2 = 1 1 1
    t2 = sub(div(Am, Jm), tj)
    a = sub(add(add(sub(V0, Vm), mul(Am, tj)), div(mul(Am, Am), Jm)), 0.0)
    first = div(-a, Am)
    A2 = mul(Am, Am); J2 = mul(Jm, Jm)
    rad = add(add(add(add(add(add(mul(mul(mul(mul(Am, Am), Am), Am), f(1.0/4.0)), mul(J2, mul(V0, V0))),
              mul(mul(mul(A2, J2), mul(tj, tj)), f(1.0/4.0))), mul(mul(mul(Am, J2), L), 2.0)),
              -mul(mul(A2, Jm), V0)), mul(mul(mul(mul(mul(Am, Am), Am), Jm), tj), f(1.0/2.0))),
              -mul(mul(mul(Am, J2), V0), tj))
    s = sqrtf(rad)
    base = mul(A2, f(-3.0/2.0))
    tailv = add(mul(Jm, V0), mul(mul(mul(Am, Jm), tj), f(3.0/2.0)))
    r1 = div(sub(sub(add(base, s), mul(Jm, V0)), mul(mul(mul(Am, Jm), tj), f(3.0/2.0))), mul(Am, Jm))
    r2 = div(sub(sub(sub(base, s), mul(Jm, V0)), mul(mul(mul(Am, Jm), tj), f(3.0/2.0))), mul(Am, Jm))
    t4 = max(min(first, max(r1, r2)), 0.0)
    return Jm, tj, t2, t4, t2
def seg_incr(tj, Jm):
    pv = segs[-1]
    Beta = div(PI, tj); Alpha = mul(Jm, 0.5)
    AT = mul(Alpha, tj)
    VT = mul(Alpha, sub(mul(mul(tj, tj), 0.5), div(2.0, mul(Beta, Beta))))
    PT = mul(Alpha, add(mul(div(-1.0, mul(Beta, Beta)), tj), mul(div(1.0, 6.0), powf(tj, 3.0))))
    segs.append(dict(t=add(pv['t'], tj), typ='P', j=Jm, a=add(pv['a'], AT),
        v=add(add(pv['v'], mul(pv['a'], tj)), VT),
        p=add(add(add(pv['p'], mul(pv['v'], tj)), mul(mul(0.5, pv['a']), mul(tj, tj))), PT)))
def seg_const(tj, J0):
    pv = segs[-1]
    if not tj >= 1.1920929e-07:
        segs.append(dict(t=pv['t'], typ='C', j=J0, a=pv['a'], v=pv['v'], p=pv['p'])); return
    segs.append(dict(t=add(pv['t'], tj), typ='C', j=J0, a=add(pv['a'], mul(J0, tj)),
        v=add(add(pv['v'], mul(pv['a'], tj)), mul(mul(0.5, J0), mul(tj, tj))),
        p=add(add(add(pv['p'], mul(pv['v'], tj)), mul(mul(0.5, pv['a']), mul(tj, tj))), mul(mul(div(1.0, 6.0), J0), powf(tj, 3.0)))))
def seg_decr(tj, Jm):
    pv = segs[-1]
    Beta = div(PI, tj); Alpha = mul(Jm, 0.5)
    AT = mul(Alpha, tj)
    VT = mul(Alpha, sub(mul(mul(tj, tj), 0.5), div(2.0, mul(Beta, Beta))))
    PT = mul(Alpha, add(mul(div(-1.0, mul(Beta, Beta)), tj), mul(div(1.0, 6.0), powf(tj, 3.0))))
    A2T = mul(Jm, tj); V2T = mul(Jm, mul(tj, tj))
    P2T = mul(Alpha, add(mul(mul(div(-1.0, mul(Beta, Beta)), 2.0), tj), mul(div(4.0, 3.0), powf(tj, 3.0))))
    segs.append(dict(t=add(pv['t'], tj), typ='N', j=Jm, a=add(sub(pv['a'], AT), A2T),
        v=add(add(sub(pv['v'], VT), mul(sub(pv['a'], AT), tj)), V2T),
        p=add(add(add(sub(pv['p'], PT), mul(sub(pv['v'], VT), tj)), mul(mul(0.5, sub(pv['a'], AT)), mul(tj, tj))), P2T)))
def seg_jerk(tj, Jm, Tcj):
    seg_incr(tj, Jm); seg_const(Tcj, Jm); seg_decr(tj, Jm)
Jm2, tj, t2, t4, t6 = calculate_path(Sm, Jm, 0.0, Am, Vm, mul(L, 0.5))
note(f'calculate_path(Sm, 1, 0, 2.5, 10, 50): tj = 1*pi_f/(2 Sm) = {tj!r}; At = 2.5 >= Jm*tj, Vm and L/2 large: solution 7, t2 = t6 = Am/Jm - tj = {t2!r}, t4 = {t4!r}')
seg_jerk(tj, Jm2, t2); seg_const(t4, 0.0); seg_jerk(tj, -Jm2, t6)
segs[7]['a'] = 0.0
for _ in range(8, 15): seg_const(0.0, 0.0)
t15 = max(0.0, div(sub(L, mul(2.0, segs[14]['p'])), segs[14]['v']))
seg_const(t15, 0.0)
seg_jerk(tj, -Jm2, t6); seg_const(t4, 0.0); seg_jerk(tj, Jm2, t2)
segs[22]['a'] = 0.0; segs[22]['v'] = 0.0
assert len(segs) == 23
peak = max(s['v'] for s in segs)
note(f'segment 1 (raised-cosine jerk up): end time tj, jerk 1; peak end speed of the 23 segments = {peak!r} (segment {max(range(23), key=lambda i: segs[i]["v"])})')

# --- the first ticks: dt = 0.0025f, track and speed scalars 1, so SCurve time += dt per tick;
# for t < tj the active segment is 1 (POSITIVE_JERK, T0 = A0 = V0 = P0 = 0):
dt = f(0.0025)
def incr(t, tj, Jm, A0, V0, P0):
    Alpha = mul(Jm, 0.5); Beta = div(PI, tj)
    bt = mul(Beta, t); sb = sinf(bt); cb = cosf(bt)
    At = sub(add(A0, mul(Alpha, t)), mul(div(Alpha, Beta), sb))
    BB = mul(Beta, Beta)
    Vt = sub(add(add(add(V0, mul(A0, t)), mul(mul(Alpha, 0.5), mul(t, t))), mul(div(Alpha, BB), cb)), div(Alpha, BB))
    Pt = add(add(add(add(add(P0, mul(V0, t)), mul(mul(0.5, A0), mul(t, t))), mul(div(-Alpha, BB), t)),
             div(mul(Alpha, mul(mul(t, t), t)), 6.0)), mul(div(Alpha, mul(BB, Beta)), sb))
    return At, Vt, max(0.0, Pt)
time = 0.0; rows = []
for k in range(3):
    time = min(add(time, mul(mul(1.0, 1.0), dt)), segs[22]['t'])
    assert time < segs[1]['t']
    A, V, P = incr(time, tj, Jm2, 0.0, 0.0, 0.0)
    rows.append((time, A, V, P))
    note(f'tick {k}: SCurve time {time!r}; A = {A!r}, V = {V!r}, P = max(0, {P!r}) (exact: A ~ Jm pi^2 t^3/(12 tj^2), V ~ A t/4, P ~ V t/5; binary32 cancellation)')

# --- the case file
import os
HERE = os.path.dirname(os.path.abspath(__file__))
H = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
sch=json.load(open(H+'/build/gen/guidance/module_schema.json'))
def rec(schema, d):
    out={}
    for fd in schema:
        v=d.get(fd['name'], 0)
        if fd['type']=='bool': out[fd['name']]='true' if v else 'false'
        elif fd['type']=='f32': out[fd['name']]=hx(f(v))
        else: out[fd['name']]=str(int(v))
    return out
P=dict(wp_spd=10.0, wp_radius_m=2.0, wp_spd_up=2.5, wp_spd_dn=1.5, wp_acc=2.5, wp_acc_z=1.0,
  wp_acc_cnr=0.0, wp_jerk=1.0, wp_ter_margin=10.0, atc_rate_r_max=0.0, atc_rate_p_max=0.0,
  atc_input_tc=0.1, atc_acc_r_max=1100.0, atc_acc_p_max=1100.0, psc_ne_pos_p=1.0, psc_ne_jerk=5.0)
C='cmd_guidance_'
ins=[]; outs=[]
for k,(t,A,V,Pp) in enumerate(rows):
    i=dict(dt=0.0025, now_ms=[1000,1002,1005][k], est_pos_d=-10.0, pc_pos_target_d=-10.0,
           pc_stopping_point_d=-10.0, pc_ne_max_speed=10.0, pc_ne_max_accel=2.5, pc_max_speed_up=2.5,
           pc_max_speed_down=1.5, pc_d_max_accel=1.0)
    i[C+'update_wpnav']=True
    if k==0:
        i[C+'wp_and_spline_init_m']=True; i[C+'wp_and_spline_init_m_stopping_point_d']=-10.0
        i[C+'set_wp_destination_NED_m']=True; i[C+'set_wp_destination_NED_m_destination_n']=100.0
        i[C+'set_wp_destination_NED_m_destination_d']=-10.0
    o=dict(tgt_pos_n=Pp, tgt_pos_d=-10.0, tgt_vel_n=V, tgt_acc_n=A, tgt_valid=True,
           tgt_ne_max_speed=10.0, tgt_ne_max_accel=2.5, tgt_max_speed_down=1.5, tgt_max_speed_up=2.5,
           tgt_d_max_accel=1.0, wp_distance=100.0, wp_bearing=0.0, wp_active=True, wp_update_ok=True,
           wp_origin_d=-10.0, wp_destination_n=100.0, wp_destination_d=-10.0,
           wp_prev_leg_finished=True, wp_leg_peak_speed=peak, wp_leg_vel_max=10.0,
           wp_leg_accel_max=2.5, wp_speed_ne=10.0, wp_offset_vel=10.0, wp_track_dt_scalar=1.0)
    if k==0:
        o.update(tgt_ne_init_stopping_point=True, tgt_d_init_stopping_point=True,
                 tgt_ne_set_max_speed_accel=True, tgt_ne_set_correction_speed_accel=True,
                 tgt_ne_correction_speed=10.0, tgt_ne_correction_accel=2.5,
                 tgt_d_set_max_speed_accel=True, tgt_d_set_correction_speed_accel=True,
                 tgt_d_correction_speed_down=1.5, tgt_d_correction_speed_up=2.5, tgt_d_correction_accel=1.0)
    ins.append(rec(sch['input'], i)); outs.append(rec(sch['output'], o))
note = ("Expected outputs worked out from AC_WPNav.cpp and SCurve.cpp in binary32, operation by operation "
 "(the working: ardupilot/modules/guidance/hand-checked-case.py, which prints it and writes this file; it reads only the schema the build generated). ArduCopter's default parameters: WP_SPD 10, WP_SPD_UP 2.5, "
 "WP_SPD_DN 1.5, WP_ACC 2.5, WP_ACC_Z 1, WP_ACC_CNR 0, WP_JERK 1, WP_RADIUS_M 2, WP_TER_MARGIN 10, ATC_RATE_R/P_MAX 0, "
 "ATC_INPUT_TC 0.1, ATC_ACC_R/P_MAX 1100, PSC_NE_POS_P 1, PSC_NE_JERK 5. Tick 0: wp_and_spline_init_m(0, (0,0,-10)) "
 "pushes the WP limits (NE 10, 2.5; D down 1.5, up 2.5, accel 1) and both stopping-point initializations; "
 "set_wp_destination_NED_m((100,0,-10)) builds a straight S-curve leg north: " + "; ".join(log[:3]) +
 ". The vehicle is at rest at the origin and the position stage reports zero desired velocity, so the track scaler is 1, "
 "the terrain scaler is 1 (no altitude error) and the speed shaper stays at 10 (scalar 1): the S-curve time advances by "
 "dt = 0.0025f per tick and stays in segment 1 (raised-cosine jerk ramp, t < tj = 0.2). " + "; ".join(log[3:]) +
 ". Target = origin + (1,0,0) P, velocity (V,0,0), acceleration (A,0,0) (path unit (100,0,0)/100 = (1,0,0) exactly; "
 "the shaper's acceleration offset is 0). Distance from the estimate (0,0) to (100,0): 100; bearing wrap_2PI(atan2f(0, 100)) = 0. "
 "The values show binary32 cancellation in SCurve's raised-cosine formulas at small t: V and P are 2^-32 and 2^-41 at tick 0 "
 "where the exact values are about 2.0e-10 and 1.0e-13.")
case=dict(module='guidance', code_hash='(computed by hand)', campaign='none', kind='hand-checked', clause='', case=0,
  step=len(rows)-1, note=note, params=rec(sch['params'], P), inputs=ins, outputs=outs)
json.dump(case, open(H+'/modules/guidance/hand-checked-case.json','w'), indent=2)
print('\n'.join(log))
print('wrote ardupilot/modules/guidance/hand-checked-case.json')
