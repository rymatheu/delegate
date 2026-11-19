#!/usr/bin/env python3
"""Write the shadow classes' stand-ins: gen/out/shadow_<Class>.cpp and gen/out/cmd_table.inc.

  python3 -I gen_shadows.py ARDUPILOT_ROOT CLASSES_JSON HANDWRITTEN_DIR OUT_DIR

For every class of another stage that the supervisor holds (SHADOWS below), one file with:
  * the preamble of the class's real .cpp (its includes and the #defines of parameter defaults),
    its real var_info table and its real constructors, copied as text ("extract"), or an empty
    var_info ("empty": the stage's parameters are not in the supervisor's list);
  * a stand-in for every out-of-line method declared in the class (not inline, not pure, not
    deleted or defaulted) that the hand-written stand-ins (HANDWRITTEN_DIR/*.cpp) do not define:
      own-task  (OWN_TASK names)       empty body, returns the type's zero (the stage runs it)
      command   (non-const, void)      appends (method id, arguments) to the tick's command log
      other     (queries, cmd+ret)     sup_unanswered(): prints the method and aborts
  * definitions of the static data members without an initializer (zero).
cmd_table.inc lists every method id: {id, "stage", "Class::method"}.
"""
import json, os, re, sys

ROOT, CJSON, HAND, OUT = sys.argv[1:5]
L = 'libraries/'

# class -> (stage, real .cpp, var_info policy)
SHADOWS = {
    'AC_WPNav': ('guidance', L + 'AC_WPNav/AC_WPNav.cpp', 'extract'),
    'AC_Loiter': ('loiter', L + 'AC_WPNav/AC_Loiter.cpp', 'extract'),
    'AC_Circle': ('guidance', L + 'AC_WPNav/AC_Circle.cpp', 'extract'),
    'SCurve': ('guidance', L + 'AP_Math/SCurve.cpp', None),
    'AC_PosControl': ('position', L + 'AC_AttitudeControl/AC_PosControl.cpp', 'extract'),
    'AC_AttitudeControl': ('attitude', L + 'AC_AttitudeControl/AC_AttitudeControl.cpp',
                           'extract'),
    'AC_AttitudeControl_Multi': ('attitude',
                                 L + 'AC_AttitudeControl/AC_AttitudeControl_Multi.cpp',
                                 'extract'),
    'AC_CommandModel': ('attitude', L + 'AC_AttitudeControl/AC_CommandModel.cpp', 'extract'),
    'AP_Motors': ('mixer', L + 'AP_Motors/AP_Motors_Class.cpp', None),
    'AP_MotorsMulticopter': ('mixer', L + 'AP_Motors/AP_MotorsMulticopter.cpp', 'extract'),
    'AP_MotorsMatrix': ('mixer', L + 'AP_Motors/AP_MotorsMatrix.cpp', None),
    'Thrust_Linearization': ('mixer', L + 'AP_Motors/AP_Motors_Thrust_Linearization.cpp',
                             'extract'),
    'AC_PID': ('rate', L + 'AC_PID/AC_PID.cpp', 'extract'),
    'AC_P': ('rate', L + 'AC_PID/AC_P.cpp', 'extract'),
    'AC_PI': ('rate', L + 'AC_PID/AC_PI.cpp', 'extract'),
    'AC_PID_2D': ('rate', L + 'AC_PID/AC_PID_2D.cpp', 'extract'),
    'AC_PID_Basic': ('rate', L + 'AC_PID/AC_PID_Basic.cpp', 'extract'),
    'AC_P_1D': ('rate', L + 'AC_PID/AC_P_1D.cpp', 'extract'),
    'AC_P_2D': ('rate', L + 'AC_PID/AC_P_2D.cpp', 'extract'),
    'AP_AHRS': ('estimator', L + 'AP_AHRS/AP_AHRS.cpp', 'extract'),
    'AP_AHRS_View': ('estimator', L + 'AP_AHRS/AP_AHRS_View.cpp', None),
    'AP_InertialSensor': ('estimator', L + 'AP_InertialSensor/AP_InertialSensor.cpp', 'extract'),
    'AP_GPS': ('estimator', L + 'AP_GPS/AP_GPS.cpp', 'extract'),
    'AP_Baro': ('estimator', L + 'AP_Baro/AP_Baro.cpp', 'extract'),
    'Compass': ('estimator', L + 'AP_Compass/AP_Compass.cpp', 'extract'),
    'NavEKF3': ('estimator', L + 'AP_NavEKF3/AP_NavEKF3.cpp', 'extract'),
    'AP_AHRS_Backend': ('estimator', L + 'AP_AHRS/AP_AHRS_Backend.cpp', None),
    'AP_AHRS_DCM': ('estimator', L + 'AP_AHRS/AP_AHRS_DCM.cpp', None),
    'AP_AHRS_NavEKF3': ('estimator', L + 'AP_AHRS/AP_AHRS_NavEKF3.cpp', None),
    'AP_AHRS_SIM': ('estimator', L + 'AP_AHRS/AP_AHRS_SIM.cpp', None),
    'AP_NavEKF_Source': ('estimator', L + 'AP_NavEKF/AP_NavEKF_Source.cpp', 'extract'),
    # the estimator's parameter sub-tables (decision 4: the whole list is served)
    'AP_GPS::Params': ('estimator', L + 'AP_GPS/AP_GPS_Params.cpp', 'extract'),
    'Compass_PerMotor': ('estimator', L + 'AP_Compass/Compass_PerMotor.cpp', 'extract'),
    'AP_InertialSensor_Params': ('estimator', L + 'AP_InertialSensor/AP_InertialSensor_Params.cpp',
                                 'extract'),
}
# the stage's own periodic or boot work: not run here
OWN_TASK = {'init', 'update', 'periodic', 'wait_for_sample', 'read', 'update_calibration',
            'rate_controller_run_dt', 'rate_controller_run', 'output',
            'calibrate', 'set_update_rate', 'set_dt_s', 'set_notch_sample_rate',
            'update_throttle_range',
            'parameter_sanity_check', 'convert_parameters', 'check_param_change',
            'heli_motors_param_conversions', 'set_frame_class_and_type',
            'convert_pwm_min_max_param', 'Log_Write', 'set_dt'}

# methods named like an own task that are commands of their stage: AC_Loiter::update is the
# loiter stage's step, called by the mode code with the pilot's request of the tick (the loiter
# stage executes it at its `_seq`, commands.txt)
NOT_OWN_TASK = {('AC_Loiter', 'update')}

ZERO = 'return {};'

# the controller shadows whose float-valued fields the poison trap (SUP_POISON=1) sets to NaN
POISON = {'AC_PosControl', 'AC_AttitudeControl', 'AC_AttitudeControl_Multi', 'AC_WPNav',
          'AC_Loiter', 'AC_Circle', 'AP_Motors', 'AP_MotorsMulticopter', 'AP_MotorsMatrix'}
POISON_TYPES = {'float', 'double', 'postype_t', 'Vector2f', 'Vector3f', 'Vector2p', 'Vector3p',
                'Vector2d', 'Vector3d', 'Quaternion', 'Matrix3f'}

# methods whose real body is copied: functions of the stage's parameters (the shadow holds them,
# with the same values as the stage when both get the same parameter record) or of constants;
# a method whose body reads the stage's running state must not be listed here
# (class, method) -> the .cpp holding it, if not the class's own
COPY_REAL = {
    ('AC_AttitudeControl', 'lean_angle_max_rad'): None,
    ('AC_AttitudeControl', 'get_slew_yaw_max_rads'): None,
    # functions of the filled AHRS state
    ('AP_AHRS', 'configured_backend_has_status'): None,
    ('AP_AHRS', 'body_to_earth2D'): L + 'AP_AHRS/AP_AHRS_Backend.cpp',
    ('AP_AHRS', 'body_to_earth2D_p'): L + 'AP_AHRS/AP_AHRS_Backend.cpp',
    # the frame strings (set on the shadow at boot from the mixer's fixed frame, stubs_mixer.cpp)
    ('AP_Motors', 'get_frame_and_type_string'): None,
    ('AP_Motors', 'get_frame_string'): None,
    # parameter checks
    ('AC_PosControl', 'pre_arm_checks'): None,
    ('AC_AttitudeControl', 'pre_arm_checks'): None,
    ('AP_MotorsMulticopter', 'check_mot_pwm_params'): None,
    # functions of filled state
    ('AC_AttitudeControl', 'get_althold_lean_angle_max_rad'): None,
    # (AC_Loiter::get_angle_max_rad: answered from the loiter stage's lt_angle_max,
    # stand_ins/stubs_guidance.cpp, so that LOIT_ANG_MAX is the loiter stage's parameter)
    # reads _angle_max_override_rad, which only set_lean_angle_max_rad (a command) changes and the
    # shadow keeps at 0: correct while no covered mode overrides the lean angle
    ('AC_PosControl', 'get_lean_angle_max_rad'): None,
    ('AC_PosControl', 'crosstrack_error_m'): None,
    # ModeLoiter::wp_bearing_deg via AC_Loiter::get_bearing_to_target_rad (NAV_CONTROLLER_OUTPUT):
    # the real body reads _pos_target_ned_m and _pos_estimate_ned_m, both filled
    ('AC_PosControl', 'get_bearing_to_target_rad'): None,
    # the navigator's conversions and stopping point: real bodies on the filled state
    ('AC_WPNav', 'get_vector_NED_m'): None,
    ('AC_WPNav', 'set_wp_destination_loc'): None,
    ('AC_WPNav', 'set_wp_destination_next_loc'): None,
    ('AC_WPNav', 'set_spline_destination_loc'): None,
    ('AC_WPNav', 'set_spline_destination_next_loc'): None,
    ('AC_WPNav', 'get_wp_destination_loc'): None,
    ('AC_WPNav', 'get_wp_stopping_point_NED_m'): None,
    ('AC_WPNav', 'get_terrain_source'): None,
    # GPS_RAW_INT: the real sender and its getters on the filled GPS state
    ('AP_GPS', 'send_mavlink_gps_raw'): None,
    ('AP_GPS', 'speed_accuracy'): None,
    ('AP_GPS', 'horizontal_accuracy'): None,
    ('AP_GPS', 'vertical_accuracy'): None,
    ('AP_GPS', 'gps_yaw_cdeg'): None,
    ('AP_GPS', 'get_undulation'): None,
}


def handwritten():
    """Class::method names (and Class::method(signature) prefixes) defined by hand."""
    names = set()
    for fn in sorted(os.listdir(HAND)):
        if fn.endswith('.cpp'):
            for m in re.finditer(r'^[\w:<>\s\*&,]*?\b(\w+)::(~?\w+)\s*\(', open(os.path.join(HAND, fn)).read(),
                                 re.M):
                names.add(m.group(1) + '::' + m.group(2))
    return names


def strip_comments_strings(txt):
    out, i, n = [], 0, len(txt)
    while i < n:
        c = txt[i]
        if txt.startswith('//', i):
            j = txt.find('\n', i)
            j = n if j < 0 else j
            out.append(' ' * (j - i)); i = j
        elif txt.startswith('/*', i):
            j = txt.find('*/', i + 2)
            j = n if j < 0 else j + 2
            out.append(re.sub(r'[^\n]', ' ', txt[i:j])); i = j
        elif c in '"\'':
            j = i + 1
            while j < n and txt[j] != c:
                j += 2 if txt[j] == '\\' else 1
            out.append(c + ' ' * (j - i - 1) + c); i = j + 1
        else:
            out.append(c); i += 1
    return ''.join(out)


def block_end(clean, start):
    """index just after the brace block that starts at the first '{' at or after start."""
    i = clean.index('{', start)
    depth = 0
    while True:
        if clean[i] == '{':
            depth += 1
        elif clean[i] == '}':
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1


def skip_balanced(clean, i):
    """clean[i] is an opening bracket; index after its match."""
    pairs = {'(': ')', '{': '}', '[': ']'}
    stack = [pairs[clean[i]]]
    i += 1
    while stack:
        c = clean[i]
        if c in pairs:
            stack.append(pairs[c])
        elif c == stack[-1]:
            stack.pop()
        i += 1
    return i


def ctor_end(clean, i):
    """clean[i] is the '(' of a constructor's parameters: index after its body."""
    i = skip_balanced(clean, i)
    while clean[i].isspace():
        i += 1
    if clean[i] == ':':
        i += 1
        while True:
            m = re.compile(r'\s*[\w:<>,\s]*?\s*([({])').match(clean, i)
            i = skip_balanced(clean, m.end(1) - 1)
            while clean[i].isspace():
                i += 1
            if clean[i] != ',':
                break
            i += 1
    while clean[i] != '{':
        i += 1
    return skip_balanced(clean, i)


def extract(cls, path, policy):
    txt = open(os.path.join(ROOT, path)).read()
    clean = strip_comments_strings(txt)
    pieces = []
    m = re.search(r'^\S[^\n;]*::\s*~?\w+\s*\(|^const\s+(struct\s+)?AP_Param::GroupInfo', clean, re.M)
    pre_end = m.start() if m else 0
    # a return type on the line before ("void\nClass::f(...)") belongs to the definition
    prev_start = clean.rfind('\n', 0, max(pre_end - 1, 0)) + 1
    if pre_end > 0 and re.match(r'[ \t]*[A-Za-z_][\w:<>\*& \t]*\n$', clean[prev_start:pre_end]):
        pre_end = prev_start
    pieces.append('// ---- preamble of %s (includes, parameter-default defines)\n' % path)
    libdir = os.path.dirname(path)[len(L):]
    # quoted includes resolve against the real file's directory: name it
    def inc(mm):
        here = os.path.join(ROOT, os.path.dirname(path), mm.group(1))
        return '#include <%s>' % (os.path.relpath(os.path.realpath(here), os.path.join(ROOT, 'libraries'))
                                  if os.path.exists(here) else mm.group(1))
    pre = re.sub(r'#include\s+"([^"]+)"', inc, txt[:pre_end])
    pieces.append(pre)
    # #if blocks the preamble opens and the end of the real file closes
    depth = 0
    for line in strip_comments_strings(pre).splitlines():
        t = line.strip()
        if re.match(r'#\s*if', t):
            depth += 1
        elif re.match(r'#\s*endif', t):
            depth -= 1
    extract.open_ifs = depth
    ecls = re.escape(cls)
    short = cls.split('::')[-1]
    if policy == 'extract':
        found = 0
        for m in re.finditer(r'^const\s+(struct\s+)?AP_Param::GroupInfo\s+%s::(var_info\w*)\s*\[\s*\]\s*='
                             % ecls, clean, re.M):
            e = block_end(clean, m.end())
            e = clean.index(';', e) + 1
            pieces.append('\n// ---- %s::%s, from %s\n' % (cls, m.group(2), path) + txt[m.start():e]
                          + '\n')
            found += 1
        if not found:
            raise SystemExit('no var_info in %s' % path)
    elif policy == 'empty':
        for name in extract.var_info_names:
            pieces.append('\n// ---- %s::%s: empty (its parameters are not served here)\n'
                          'const AP_Param::GroupInfo %s::%s[] = {\n    AP_GROUPEND\n};\n'
                          % (cls, name, cls, name))
    for m in re.finditer(r'^%s::%s\s*\(' % (ecls, short), clean, re.M):
        e = ctor_end(clean, m.end() - 1)
        pieces.append('\n// ---- constructor, from %s\n' % path + txt[m.start():e] + '\n')
    return ''.join(pieces), bool(re.search(r'^%s::%s\s*\(' % (ecls, short), clean, re.M))


def copy_real_method(cls, path, name):
    txt = open(os.path.join(ROOT, path)).read()
    clean = strip_comments_strings(txt)
    m = re.search(r'^[^\n;{}#]*\b%s::%s\s*\(' % (cls, name), clean, re.M)
    if not m:
        raise SystemExit('gen_shadows: no %s::%s in %s' % (cls, name, path))
    i = clean.index('(', m.end() - 1)
    i = skip_balanced(clean, i)
    while clean[i] != '{':
        i += 1
    e = skip_balanced(clean, i)
    return '// real body, from %s\n' % path + txt[m.start():e] + '\n'


def param_list(m):
    ps = []
    for k, (name, ty) in enumerate(m['params']):
        nm = name or 'a%d' % k
        ps.append((nm, ty))
    return ps


def declare(cls, m, ps):
    args = ', '.join(('%s %s' % (ty, nm)) if '(*)' not in ty else ty.replace('(*)', '(*%s)' % nm)
                     for nm, ty in ps)
    if m['variadic']:
        args += ', ...'
    q = ' const' if m['const'] else ''
    short = cls.split('::')[-1]
    if m['kind'] == 'CXXDestructorDecl':
        return '%s::~%s()' % (cls, short)
    if m['kind'] == 'CXXConstructorDecl':
        return '%s::%s(%s)' % (cls, short, args)
    return 'auto %s::%s(%s)%s -> %s' % (cls, m['name'], args, q, m['ret'])


def write_if_changed(path, text):
    if os.path.exists(path) and open(path).read() == text:
        return
    open(path, 'w').write(text)


def main():
    classes = json.load(open(CJSON))
    hand = handwritten()
    os.makedirs(OUT, exist_ok=True)
    table, nid = [], 0
    copied = set()
    for cls, (stage, path, policy) in SHADOWS.items():
        d = classes.get(cls)
        if d is None:
            print('gen_shadows: %s not in %s' % (cls, CJSON), file=sys.stderr)
            continue
        extract.var_info_names = [f['name'] for f in d['fields']
                                  if f['static'] and f['name'].startswith('var_info')]
        text, has_ctor = extract(cls, path, policy)
        body = ['// shadow_%s.cpp: written by gen/gen_shadows.py; do not edit.\n'
                '// Stage: %s. Real code copied from $ARDUPILOT_ROOT/%s; stand-ins below.\n'
                % (cls.replace('::', '__'), stage, path),
                '#include "supervisor_shadow.h"\n', text,
                '\n// ---- stand-ins for the out-of-line methods\n']
        for m in d['methods']:
            if m['body'] or m['pure'] or m['deleted'] or m['defaulted']:
                continue
            if m['kind'] == 'CXXConstructorDecl' and (has_ctor or policy is not None):
                continue
            key = '%s::%s' % (cls, m['name'] if m['kind'] != 'CXXDestructorDecl'
                              else '~' + cls.split('::')[-1])
            if key in hand:
                continue
            if (cls, m['name']) in COPY_REAL:
                if (cls, m['name']) not in copied:
                    copied.add((cls, m['name']))
                    body.append(copy_real_method(cls, COPY_REAL[(cls, m['name'])] or path,
                                                 m['name']))
                continue
            ps = param_list(m)
            sig = declare(cls, m, ps)
            if m['kind'] in ('CXXConstructorDecl', 'CXXDestructorDecl'):
                body.append('%s {}\n' % sig)
                continue
            ret_void = m['ret'] == 'void'
            nm = m['name']
            if nm == 'get_singleton' and m['static']:
                body.append('%s\n{\n    return _singleton;   // as the real accessor\n}\n' % sig)
            elif nm in OWN_TASK and (cls, nm) not in NOT_OWN_TASK:
                stmt = '' if ret_void else ZERO
                body.append('%s\n{\n    // own-task of the %s stage: not run in the supervisor\n'
                            '%s}\n' % (sig, stage, ('    ' + stmt + '\n') if stmt else ''))
            elif not m['const'] and ret_void and not m['static']:
                # a method moved out of OWN_TASK gets a fixed id of its own (1000 + its place in
                # NOT_OWN_TASK), so that the other commands keep their ids (cmd_log_hash)
                if (cls, nm) in NOT_OWN_TASK:
                    cid = 1000 + sorted(NOT_OWN_TASK).index((cls, nm))
                else:
                    nid += 1
                    cid = nid
                table.append('    {%d, "%s", "%s::%s"},' % (cid, stage, cls, nm))
                args = ''.join('    sup_arg(%s);\n' % nm2 for nm2, _ in ps)
                body.append('%s\n{\n    sup_cmd_begin(%d);\n%s    sup_cmd_end();\n}\n'
                            % (sig, cid, args))
            else:
                # not strict (the default): counts the call (output `unanswered`, guaranteed 0)
                # and returns the type's zero; SUP_STRICT=1: aborts
                lenient = ('    if (sup_lenient("%s::%s")) {\n        return%s;\n    }\n'
                           % (cls, nm, '' if ret_void else ' SupZero<%s>::get()' % m['ret']))
                body.append('%s\n{\n%s    sup_unanswered("%s::%s");\n}\n'
                            % (sig, lenient, cls, nm))
        for f in d['fields']:
            if re.search(r'\b%s::%s\b' % (re.escape(cls), f['name']), text):
                continue   # defined in the copied real code
            if f['static'] and not f['init'] and not f['name'].startswith('var_info'):
                body.append('decltype(%s::%s) %s::%s{};\n' % (cls, f['name'], cls, f['name']))
        if cls in POISON:
            pf = [f['name'] for f in d['fields'] if not f['static'] and f['name'] and
                  f['type'].replace('const ', '').strip() in POISON_TYPES]
            body.append('\n// ---- the poison trap: every float-valued field (%d)\n' % len(pf))
            for nm in pf:
                body.append('HARNESS_PADDR(%s, %s)\n' % (cls, nm))
            body.append('void harness_poison_%s(%s &o)\n{\n' % (cls, cls))
            for f in d['fields']:
                if f['name'] in pf:
                    body.append('    sup_poison(*static_cast<%s *>(harness_paddr_%s_%s(o)));\n'
                                % (f['type'].replace('const ', '').strip(), cls, f['name']))
            body.append('}\n')
        body.append('#endif  // closes an #if of the real preamble\n' * extract.open_ifs)
        write_if_changed(os.path.join(OUT, 'shadow_%s.cpp' % cls.replace('::', '__')),
                         ''.join(body))
    write_if_changed(os.path.join(OUT, 'cmd_table.inc'),
        '// written by gen/gen_shadows.py: {id, stage, method} of every generated command\n'
        + '\n'.join(table) + '\n')
    print('gen_shadows: %d classes, %d command methods' % (len(SHADOWS), nid))


main()
