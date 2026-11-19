#!/usr/bin/env python3
"""Estimate what nm cannot see: the members of the other stages' classes the vehicle code reaches.

  python3 -I access_scan.py ARDUPILOT_ROOT II_DIR OUT_TSV

Reads the preprocessed sources (preprocess_one.sh), so code switched off by the feature flags is
not counted; a line counts if it comes from ArduCopter/ or a supervisor-side library (SUPERVISOR
below), whichever translation unit included it (each site is counted once).

Scans the probe's sources (ArduCopter/ and the supervisor libraries) for accesses through the
objects that stand for other stages (copter.pos_control->X, ahrs.X, AP::ahrs().X, motors->X, ...),
and classifies each member X by its declaration in the class's headers:
  data      a data member (public field, read or written directly)
  inline    a method with its body in the header (compiled into the caller; nm cannot see it)
  virtual   a virtual method declared without body (called through the vtable; nm cannot see it)
  outline   a non-virtual method declared without body (the call is an undefined symbol)
  ?         not found in the headers (inherited from a base not listed, or a macro)
Writes one line per (stage, class, member, kind, sites, example site).
"""
import collections, os, re, sys

ROOT, SRCS, OUT = sys.argv[1], sys.argv[2], sys.argv[3]
L = os.path.join(ROOT, 'libraries')
H = lambda *p: [os.path.join(L, x) for x in p]

OBJ = [  # (stage, class label, access regex prefix, headers in base-first order)
    ('position', 'AC_PosControl', r'\bpos_control->', H('AC_AttitudeControl/AC_PosControl.h')),
    ('attitude', 'AC_AttitudeControl', r'\battitude_control->',
     H('AC_AttitudeControl/AC_AttitudeControl.h', 'AC_AttitudeControl/AC_AttitudeControl_Multi.h')),
    ('guidance', 'AC_WPNav', r'\bwp_nav->', H('AC_WPNav/AC_WPNav.h')),
    ('guidance', 'AC_Loiter', r'\bloiter_nav->', H('AC_WPNav/AC_Loiter.h')),
    ('guidance', 'AC_Circle', r'\bcircle_nav->', H('AC_WPNav/AC_Circle.h')),
    ('mixer', 'AP_Motors', r'\bmotors->|AP::motors\(\)->|\bmotors\.',
     H('AP_Motors/AP_Motors_Class.h', 'AP_Motors/AP_MotorsMulticopter.h', 'AP_Motors/AP_MotorsMatrix.h')),
    ('estimator', 'AP_AHRS', r'\bahrs\.|AP::ahrs\(\)\.|\b_ahrs\.',
     H('AP_AHRS/AP_AHRS.h', 'AP_AHRS/AP_AHRS_Backend.h')),
    ('estimator', 'AP_AHRS_View', r'\bahrs_view->|\b_ahrs_view\.', H('AP_AHRS/AP_AHRS_View.h')),
    ('estimator', 'AP_InertialSensor', r'\bins\.|AP::ins\(\)\.',
     H('AP_InertialSensor/AP_InertialSensor.h')),
    ('estimator', 'AP_GPS', r'\bgps\.|AP::gps\(\)\.', H('AP_GPS/AP_GPS.h')),
    ('estimator', 'AP_Baro', r'\bbarometer\.|AP::baro\(\)\.|\bbaro\.', H('AP_Baro/AP_Baro.h')),
    ('estimator', 'Compass', r'\bcompass\.|AP::compass\(\)\.', H('AP_Compass/AP_Compass.h')),
]


def declarations(headers):
    """member name -> kind, from a crude reading of the class headers."""
    kinds = {}
    for h in headers:
        txt = open(h, errors='replace').read()
        txt = re.sub(r'//[^\n]*', '', txt)
        txt = re.sub(r'/\*.*?\*/', '', txt, flags=re.S)
        # methods: name ( ... ) [const] [override] { or ;
        for m in re.finditer(r'([~\w][\w:<>,\s\*&]*?)\b(\w+)\s*\(([^;{}()]|\([^()]*\))*\)\s*'
                             r'(const)?\s*(override|final)?\s*(=\s*0\s*)?([{;])', txt):
            name = m.group(2)
            if name in ('if', 'for', 'while', 'switch', 'return', 'sizeof'):
                continue
            pre = m.group(1)
            if m.group(7) == '{':
                k = 'inline'
            elif 'virtual' in pre or m.group(5):
                k = 'virtual'
            else:
                k = 'outline'
            if name not in kinds or kinds[name] == 'data':
                kinds[name] = k
            elif kinds[name] != k and kinds[name] != 'mixed':
                kinds[name] = 'mixed' if {kinds[name], k} != {'outline', 'virtual'} else 'virtual'
        for m in re.finditer(r'^\s*(?:static\s+)?(?:const\s+)?[\w:<>]+[\s\*&]+(\w+)\s*'
                             r'(?:\[[^\]]*\])?\s*(?:[;={]|:\s*\d)', txt, re.M):
            kinds.setdefault(m.group(1), 'data')
        for m in re.finditer(r'\}\s*(\w+)\s*;', txt):   # struct {...} name;
            kinds.setdefault(m.group(1), 'data')
    return kinds


SUPERVISOR = ('ArduCopter/', 'libraries/GCS_MAVLink/', 'libraries/AP_Mission/',
              'libraries/AP_Arming/', 'libraries/RC_Channel/', 'libraries/AP_Scheduler/',
              'libraries/AP_Param/', 'libraries/AP_Vehicle/', 'libraries/AP_Notify/',
              'libraries/AP_BattMonitor/', 'libraries/StorageManager/', 'libraries/SRV_Channel/',
              'libraries/AP_RCMapper/', 'libraries/AP_SerialManager/')


def lines_of_interest(ii_dir):
    """(file, line) -> code, for lines of supervisor-side files in any preprocessed unit."""
    seen = {}
    mk = re.compile(r'^# (\d+) "([^"]+)"')
    for fn in sorted(os.listdir(ii_dir)):
        cur, n = None, 0
        for line in open(os.path.join(ii_dir, fn), errors='replace'):
            m = mk.match(line)
            if m:
                n = int(m.group(1)); cur = os.path.relpath(os.path.realpath(m.group(2)), ROOT)
                continue
            if cur is not None and cur.startswith(SUPERVISOR) and line.strip():
                seen.setdefault((cur, n), line)
            n += 1
    return seen


def main():
    seen = lines_of_interest(SRCS)
    rows = collections.OrderedDict()
    for stage, cls, pre, hdrs in OBJ:
        kinds = declarations(hdrs)
        rx = re.compile(r'(?:' + pre + r')(\w+)(\s*\()?')
        for (f, i), code in sorted(seen.items()):
            for m in rx.finditer(code):
                name = m.group(1)
                called = bool(m.group(2))
                k = kinds.get(name, '?')
                if not called and k != 'data':
                    k = k + '(no call)'
                key = (stage, cls, name, k)
                site = '%s:%d' % (f, i)
                if key not in rows:
                    rows[key] = [0, site]
                rows[key][0] += 1
    with open(OUT, 'w') as o:
        o.write('stage\tclass\tmember\tkind\tsites\texample\n')
        for (st, c, n, k), (cnt, site) in sorted(rows.items()):
            o.write('%s\t%s\t%s\t%s\t%d\t%s\n' % (st, c, n, k, cnt, site))
    agg = collections.Counter()
    sites = collections.Counter()
    for (st, c, n, k), (cnt, _) in rows.items():
        agg[(st, k.split('(')[0])] += 1
        sites[(st, k.split('(')[0])] += cnt
    print('stage       kind      members  sites')
    for (st, k), v in sorted(agg.items()):
        print('%-11s %-9s %7d %6d' % (st, k, v, sites[(st, k)]))
    print('total members', len(rows), 'sites', sum(v[0] for v in rows.values()))


main()
