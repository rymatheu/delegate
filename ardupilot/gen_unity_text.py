#!/usr/bin/env python3
"""Writes ardupilot/unity_text.cpp: the unity translation unit of ArduPilot's text formatter
(AP_HAL/utility/print_vprintf.cpp, ftoa_engine.cpp, utoa_invert.cpp, AP_HAL::Util::snprintf and
vsnprintf of AP_HAL/Util.cpp, included unmodified) and the functions the difftest drives: one per
conversion specification found in the format strings of the reference build's sources (the
`snprintf`, `vsnprintf`, `GCS_SEND_TEXT`, `send_text`, `check_failed`, `printf`, `panic`, ... calls of
the files in build/reference/ap/build/sitl/compile_commands.json, AP_HAL_SITL and SITL excluded;
README.md, "Phase 2b"), each formatting random arguments of the conversion's type into a 40-byte
buffer through `hal.util->snprintf` with a random size, and a few whole formats of the vehicle's
messages. `%p` is left out (a pointer's value differs between the two programs).
Usage: python3 ardupilot/gen_unity_text.py [--scan] (with --scan, the specifications are recomputed
from the reference build; without it, the list below, which is that scan's result, is used)."""
import collections
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

# the result of --scan (72 specifications; count of uses in the reference build's sources)
SPECS = ['%s', '%u', '%d', '%.1f', '%f', '%x', '%02x', '%.2f', '%4.2f', '%02u', '%c', '%i', '%lu', '%3.1f',
         '%.0f', '%4.1f', '%ld', '%08x', '%%', '%03u', '%02d', '%04x', '%X', '%4.3f', '%02X', '%.3f', '%0.4f',
         '%0.2f', '%04X', '%p', '%2X', '%0.0f', '%-8s', '%12.7f', '%0.1f', '%0.3f', '%1.1f', '%.5f', '%.4f',
         '%03d', '%05u', '%04u', '%04d', '%.7f', '%4.0f', '%.6f', '%1.2f', '%.32s', '%4u', '%3u', '%07.4f',
         '%08.5f', '%07llx', '%0.5f', '% 0x', '%-7s', '%.17g', '%08u', '%08.1f', '%05.1f', '%05.2f', '%-5s',
         '%2u', '%2d', '%li', '%+d', '%-9s', '%llu', '%08lx', '%.4s', '%lx', '%lld']

# whole formats of the vehicle's messages (each with its arguments' kinds)
WHOLE = ['PreArm: Battery %d low voltage %.2fV', 'Mode %s (%u)', '%s: %u (%5.1f%%)', 'EKF3 IMU%u is using GPS',
         'Throttle (%.1f) > %.1f', 'Param %s %ld', 'Arm: %s %-5s|%3u|%+d', 'V%u.%u.%u %c%x', 'gyro %.3e %E %g %G']

SPEC_RE = re.compile(r'%[-+ #0]*\d*(?:\.\d+)?(?:hh|h|ll|l|z|j|t)?[diouxXeEfgGcsp%]')


def scan():
    cc = json.load(open(os.path.join(HERE, '..', 'build', 'reference', 'ap', 'build', 'sitl', 'compile_commands.json')))
    files = sorted(set(os.path.normpath(os.path.join(e['directory'], e['file'])) for e in cc))
    calls = re.compile(r'(snprintf|vsnprintf|GCS_SEND_TEXT|send_text|check_failed|printf|panic|Write_MessageF|asprintf)\s*\(')
    specs = collections.Counter()
    for f in files:
        if '/AP_HAL_SITL/' in f or '/SITL/' in f:
            continue
        src = open(f, errors='replace').read()
        for m in calls.finditer(src):
            seg = src[m.end():m.end() + 400]
            depth, i = 1, 0
            while i < len(seg) and depth > 0:
                c = seg[i]
                if c == '"':
                    j = i + 1
                    while j < len(seg) and seg[j] != '"':
                        j += 2 if seg[j] == '\\' else 1
                    i = j + 1
                    continue
                depth += c == '('
                depth -= c == ')'
                i += 1
            for s in SPEC_RE.findall(seg[:i]):
                specs[s] += 1
    return [s for s, _ in specs.most_common()]


def arg_kind(spec):
    conv = spec[-1]
    long_ = 'll' if 'll' in spec else 'l' if 'l' in spec[:-1].lstrip('%-+ #0123456789.') else ''
    if conv in 'di':
        return {'': ('int32_t', 'int32_t'), 'l': ('int64_t', 'long'), 'll': ('int64_t', 'long long')}[long_]
    if conv in 'uxXo':
        return {'': ('uint32_t', 'uint32_t'), 'l': ('uint64_t', 'unsigned long'), 'll': ('uint64_t', 'unsigned long long')}[long_]
    if conv == 'c':
        return ('uint8_t', 'int')
    if conv in 'feEgG':
        return ('float', None)
    if conv == 's':
        return ('string', None)
    return None


DOMAINS = {}     # function.param -> [lo, hi]: Text.json's "domains"


def function(k, fmt, out):
    params, args, body = [], [], []
    for j, spec in enumerate(SPEC_RE.findall(fmt)):
        if spec == '%%':
            continue
        kind = arg_kind(spec)
        if kind[0] == 'string':
            params += ['uint32_t seed%d' % j, 'uint8_t len%d' % j]
            body.append('    char s%d[12];' % j)
            body.append('    text_fill(s%d, seed%d, len%d %% 12);' % (j, j, j))
            args.append('s%d' % j)
        elif kind[0] == 'float':
            params.append('float a%d' % j)
            args.append('a%d' % j)
        else:
            params.append('%s a%d' % (kind[0], j))
            args.append('(%s)a%d' % (kind[1], j) if kind[1] != kind[0] else 'a%d' % j)
            if kind[0] == 'int64_t':
                # %ld/%lld negate a negative value (`x = -x`, print_vprintf.cpp:395, :403): for
                # INT64_MIN that overflows, undefined in C++ (clang -O2 then prints "-0"); left out
                DOMAINS['fmt_%d.a%d' % (k, j)] = [-(1 << 63) + 1, (1 << 63) - 1]
    c_fmt = fmt.replace('\\', '\\\\').replace('"', '\\"')
    out.append('// "%s"' % c_fmt)
    out.append('int32_t fmt_%d(uint8_t out[40], uint8_t size%s)' % (k, ''.join(', ' + p for p in params)))
    out.append('{')
    out += body
    out.append('    return hal.util->snprintf((char *)out, size %% 41, "<%s>"%s);' % (c_fmt, ''.join(', ' + a for a in args)))
    out.append('}')
    out.append('')


def main():
    specs = scan() if '--scan' in sys.argv else SPECS
    out = ['// Unity translation unit for cpp2lean: ArduPilot\'s text formatter, generated by',
           '// ardupilot/gen_unity_text.py (do not edit). The ArduPilot sources are included unmodified;',
           '// the C++ side of the difftest compiles them separately (ardupilot/Text.json).',
           '#include <AP_HAL/utility/print_vprintf.cpp>',
           '#include <AP_HAL/utility/ftoa_engine.cpp>',
           '#include <AP_HAL/utility/utoa_invert.cpp>',
           '#include <AP_HAL/Util.cpp>',
           '',
           'extern const AP_HAL::HAL& hal;',
           '',
           '// a string of len characters (len < 12): letters, digits, punctuation, a high byte',
           'static void text_fill(char *s, uint32_t seed, uint8_t len)',
           '{',
           '    const char alphabet[16] = "aZ0 9%_.-,:\\x80xyQ";',
           '    for (uint8_t i = 0; i < len; i++) {',
           '        s[i] = alphabet[seed % 15];',
           '        seed /= 15;',
           '    }',
           '    s[len] = 0;',
           '}',
           '']
    k = 0
    for spec in specs:
        if spec.endswith('p'):
            continue
        function(k, spec, out)
        k += 1
    for fmt in WHOLE:
        function(k, fmt, out)
        k += 1
    with open(os.path.join(HERE, 'unity_text.cpp'), 'w') as f:
        f.write('\n'.join(out))
    cfgp = os.path.join(HERE, 'Text.json')
    cfg = json.load(open(cfgp))
    cfg['free']['domains'] = DOMAINS
    with open(cfgp, 'w') as f:
        json.dump(cfg, f, indent=1)
        f.write('\n')
    protos = [l + ';' for l in out if l.startswith('int32_t fmt_')]
    with open(os.path.join(HERE, 'unity_text.h'), 'w') as f:
        f.write('// The functions of ardupilot/unity_text.cpp (generated by ardupilot/gen_unity_text.py; do not edit).\n'
                '#pragma once\n#include <stdint.h>\n' + '\n'.join(protos) + '\n')
    print('ardupilot/unity_text.cpp: %d functions' % k)


if __name__ == '__main__':
    main()
