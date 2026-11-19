#!/usr/bin/env python3
"""Classify the undefined symbols of the probe's objects by the stage that owns them.

  python3 -I symbols.py OUT ARDUPILOT_ROOT     (OUT = build/modules/supervisor/probe)

Reads OUT/compile_status.txt (objects that compiled), runs nm on them, keeps the symbols that are
undefined in some object and defined in none, demangles them, and assigns each an owner:
estimator, guidance, position, attitude, rate, mixer, hal, libc (C/C++ runtime), or
lib:<library> (an ArduPilot library still to be compiled into the supervisor or stood in for).
The owner is decided by the class (or namespace) the symbol belongs to, looked up in an index of
the classes declared in each library's headers. Writes OUT/surface.tsv and prints counts.
"""
import collections, os, re, subprocess, sys

OUT, ROOT = sys.argv[1], sys.argv[2]
LIB = os.path.join(ROOT, 'libraries')

STAGE_OF_LIB = {
    'AP_AHRS': 'estimator', 'AP_NavEKF3': 'estimator', 'AP_NavEKF2': 'estimator',
    'AP_NavEKF': 'estimator', 'AP_InertialSensor': 'estimator', 'AP_GPS': 'estimator',
    'AP_Baro': 'estimator', 'AP_Compass': 'estimator', 'AP_InertialNav': 'estimator',
    'AP_DAL': 'estimator', 'AP_AccelCal': 'estimator', 'AP_Declination': 'estimator',
    'AC_WPNav': 'guidance',
    'AC_AttitudeControl': 'attitude',   # AC_PosControl is moved to 'position' below
    'AC_PID': 'rate',
    'AP_Motors': 'mixer',
    'AP_HAL': 'hal', 'AP_HAL_SITL': 'hal', 'SITL': 'hal',
}
CLASS_STAGE = {'AC_PosControl': 'position', 'SCurve': 'guidance', 'SplineCurve': 'guidance'}
NS_FUNC_STAGE = {  # AP:: accessors
    'ahrs': 'estimator', 'ins': 'estimator', 'gps': 'estimator', 'baro': 'estimator',
    'compass': 'estimator', 'motors': 'mixer', 'sitl': 'hal', 'FS': 'lib:AP_Filesystem',
}


def class_index():
    idx = {}
    pat = re.compile(r'^\s*(?:class|struct)\s+(?:alignas\([^)]*\)\s+)?([A-Za-z_]\w*)\s*(?:final\s*)?[:{]',
                     re.M)
    for d in sorted(os.listdir(LIB)):
        p = os.path.join(LIB, d)
        if not os.path.isdir(p):
            continue
        for dp, _, fs in os.walk(p):
            if '/examples' in dp or '/tests' in dp:
                continue
            for f in fs:
                if f.endswith('.h'):
                    try:
                        txt = open(os.path.join(dp, f), errors='replace').read()
                    except OSError:
                        continue
                    for m in pat.finditer(txt):
                        idx.setdefault(m.group(1), d)
    return idx


def outer_scope(dem):
    s = dem
    for pre in ('vtable for ', 'typeinfo for ', 'typeinfo name for ', 'VTT for ',
                'guard variable for ', 'non-virtual thunk to '):
        if s.startswith(pre):
            s = s[len(pre):]
    s = re.sub(r'\(.*', '', s)
    depth, out = 0, ''
    for ch in s:   # drop template arguments
        if ch == '<':
            depth += 1
        elif ch == '>':
            depth -= 1
        elif depth == 0:
            out += ch
    return out.split('::')


def main():
    objs = []
    for line in open(os.path.join(OUT, 'compile_status.txt')):
        st, src = line.split()
        if st == 'ok':
            objs.append(os.path.join(OUT, 'obj', '%s_%s.o' % (
                os.path.basename(os.path.dirname(src)), os.path.basename(src)[:-4])))
    und, dfn, users = set(), set(), collections.defaultdict(set)
    for o in objs:
        r = subprocess.run(['nm', o], capture_output=True, text=True).stdout
        for l in r.splitlines():
            parts = l.split()
            if len(parts) == 2 and parts[0] == 'U':
                und.add(parts[1]); users[parts[1]].add(os.path.basename(o)[:-2])
            elif len(parts) == 3 and parts[1] in 'TDSBCVWRtdsbr' and parts[1].isupper():
                dfn.add(parts[2])
    ext = sorted(und - dfn)
    dem = subprocess.run(['c++filt'], input='\n'.join(ext), capture_output=True,
                         text=True).stdout.splitlines()
    idx = class_index()
    rows = []
    for raw, d in zip(ext, dem):
        sc = outer_scope(d)
        owner = None
        if len(sc) == 1:
            owner = 'libc'
        elif sc[0] == 'AP' and len(sc) >= 2:
            owner = NS_FUNC_STAGE.get(sc[1], 'lib:?AP::' + sc[1])
        elif sc[0] in ('std', '__cxxabiv1'):
            owner = 'libc'
        elif sc[0] in ('AP_HAL', 'HALSITL', 'SITL'):
            owner = 'hal'
        else:
            cls = sc[0]
            if cls in CLASS_STAGE:
                owner = CLASS_STAGE[cls]
            else:
                lib = idx.get(cls)
                if lib is None:
                    owner = 'lib:?' + cls
                else:
                    owner = STAGE_OF_LIB.get(lib, 'lib:' + lib)
        rows.append((owner, d, ','.join(sorted(users[raw]))))
    rows.sort()
    with open(os.path.join(OUT, 'surface.tsv'), 'w') as f:
        f.write('owner\tsymbol\tused_by\n')
        for r in rows:
            f.write('\t'.join(r) + '\n')
    c = collections.Counter(r[0] for r in rows)
    for k, v in sorted(c.items(), key=lambda kv: (-kv[1], kv[0])):
        print('%5d  %s' % (v, k))
    print('%5d  total (objects: %d)' % (len(rows), len(objs)))


main()
