#!/usr/bin/env python3
"""Join the probe's measurements into one table of the proxy surface.

  python3 -I classify_surface.py PROBE_DIR OUT_TSV

Inputs (PROBE_DIR): surface.tsv (undefined symbols, symbols.py), access.tsv (member accesses,
access_scan.py), classes.json (declarations, ast_extract.py). For every member of another stage's
class that the supervisor's code reaches, one row:
  stage, class, member, how it is reached (symbol = out-of-line call nm sees; virtual = through
  the vtable; inline = body in the header; data = field), role, sites, an example site
where role is
  command   non-const, returns void: the call tells the stage to do something
  cmd+ret   non-const, returns a value: a command whose result the caller uses at once
  query     const method or a field read: a value the stage produced
  own-task  the stage's own periodic or boot work (init, update, the IMU wait, the rate loop, the
            mixer output): not run in the supervisor; the stage runs it in its own step
  local     constructors, destructors, parameter tables, singletons, AP:: accessors, parameter
            conversion at boot: exists in the supervisor process, no traffic
"""
import collections, json, os, re, sys

P, OUT = sys.argv[1], sys.argv[2]
classes = json.load(open(os.path.join(P, 'classes.json')))
STAGE = {'AC_PosControl': 'position', 'AC_AttitudeControl': 'attitude',
         'AC_AttitudeControl_Multi': 'attitude', 'AC_CommandModel': 'attitude',
         'AC_WPNav': 'guidance', 'AC_Loiter': 'guidance', 'AC_Circle': 'guidance', 'SCurve': 'guidance',
         'AP_Motors': 'mixer', 'AP_MotorsMulticopter': 'mixer', 'AP_MotorsMatrix': 'mixer',
         'AP_AHRS': 'estimator', 'AP_AHRS_View': 'estimator', 'AP_InertialSensor': 'estimator',
         'AP_GPS': 'estimator', 'AP_Baro': 'estimator', 'Compass': 'estimator', 'AC_PID': 'rate'}
LOCAL_NAMES = {'convert_parameters', 'var_info', '_singleton', 'heli_motors_param_conversions',
               'convert_pwm_min_max_param', 'get_frame_string', 'get_frame_and_type_string'}


def lookup(cls, name):
    """(class where declared, [method dicts] or field dict) following the bases."""
    todo = [cls]
    while todo:
        c = todo.pop(0)
        d = classes.get(c)
        if d is None:
            continue
        ms = [m for m in d['methods'] if m['name'] == name]
        if ms:
            return c, ms
        fs = [f for f in d['fields'] if f['name'] == name]
        if fs:
            return c, fs[0]
        todo += [b.split('<')[0] for b in d['bases']]
    return None, None


OWN_TASK = {'init', 'update', 'periodic', 'wait_for_sample', 'read', 'update_calibration',
            'rate_controller_run_dt', 'rate_controller_run', 'output', 'update_estimates',
            'calibrate', 'update_throttle_range', 'set_update_rate', 'set_dt_s',
            'set_notch_sample_rate', 'update_throttle_hover'}


def role_of(name, ms):
    if name in OWN_TASK:
        return 'own-task'
    if name in LOCAL_NAMES or any(m['kind'] != 'CXXMethodDecl' for m in ms):
        return 'local'
    if all(m['const'] or m['static'] for m in ms):
        return 'query'
    nc = [m for m in ms if not m['const']]
    if any(m['ret'] != 'void' for m in nc):
        return 'cmd+ret' if not name.startswith('get_') else 'query'
    return 'command'


def how(ms):
    if all(m['body'] for m in ms):
        return 'inline'
    if any(m['virtual'] for m in ms if not m['body']):
        return 'virtual'
    return 'symbol'


rows = {}
# accesses found in the sources
ACC_CLASS = {'AP_Motors': 'AP_MotorsMatrix', 'AC_AttitudeControl': 'AC_AttitudeControl_Multi'}
for line in list(open(os.path.join(P, 'access.tsv')))[1:]:
    st, cls, mem, _, n, ex = line.rstrip('\n').split('\t')
    c, d = lookup(ACC_CLASS.get(cls, cls), mem)
    if c is None:
        continue
    if isinstance(d, dict):
        kind, role = ('data', 'local' if mem in LOCAL_NAMES else 'query')
    else:
        kind, role = how(d), role_of(mem, d)
    key = (STAGE.get(c, st), c, mem)
    r = rows.setdefault(key, [kind, role, 0, ex])
    r[2] += int(n)
# undefined symbols (calls nm sees), including those reached from library code by other paths
for line in list(open(os.path.join(P, 'surface.tsv')))[1:]:
    owner, sym, users = line.rstrip('\n').split('\t')
    if owner not in ('estimator', 'guidance', 'position', 'attitude', 'mixer', 'rate'):
        continue
    m = re.match(r'(?:vtable for )?([A-Za-z_]\w*)(?:<[^>]*>)?::(~?\w+)', sym)
    if not m:
        key = (owner, 'AP', sym.split('(')[0])
        rows.setdefault(key, ['symbol', 'local', 0, users.split(',')[0]])
        continue
    cls, mem = m.group(1), m.group(2)
    c, d = lookup(cls, mem)
    if c is None:
        c = cls
        role = 'local'
    elif isinstance(d, dict):
        role = 'local'
    else:
        role = role_of(mem, d)
    key = (owner, c, mem)
    if key not in rows:
        rows[key] = ['symbol', role, 0, users.split(',')[0]]
with open(OUT, 'w') as o:
    o.write('stage\tclass\tmember\treached\trole\tsites\texample\n')
    for k in sorted(rows):
        o.write('\t'.join(list(k) + [str(x) for x in rows[k]]) + '\n')
cnt = collections.Counter()
for (st, c, m), (kind, role, n, ex) in rows.items():
    cnt[(st, role)] += 1
    cnt[(st, 'reach:' + kind)] += 1
stages = sorted({k[0] for k in cnt})
roles = ['command', 'cmd+ret', 'query', 'own-task', 'local', 'reach:symbol', 'reach:virtual', 'reach:inline',
         'reach:data']
print('%-10s' % 'stage' + ''.join('%14s' % r for r in roles) + '%8s' % 'total')
for s in stages:
    tot = sum(cnt[(s, r)] for r in roles[:5])
    print('%-10s' % s + ''.join('%14d' % cnt[(s, r)] for r in roles) + '%8d' % tot)
