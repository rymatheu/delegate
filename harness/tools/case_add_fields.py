#!/usr/bin/env python3
"""Carry a saved (hand-checked) case of a module over fields added to the module's schemas later.

    python3 -I tools/case_add_fields.py MODULE CASE.json PARAM=VALUE...   (from the harness directory)

A parameter or input the case does not have gets the value given on the command line (PARAM=VALUE), else 0 / false.
The module's executable (build/modules/MODULE/MODULE) is run on the case; every output field the case records must
come out bit for bit as recorded (else nothing is written), and an output field the case does not have is recorded
as the executable gives it (a field added later is not hand-checked; the note says which). The case is rewritten in
schema order, with a line appended to its note.
"""
import json
import os
import struct
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
H = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(H, 'py'))
import module_protocol as mp  # noqa: E402


def enc(t, v):
    if t == 'f32':
        return '0x%08x' % struct.unpack('<I', mp.f32_bits(v))[0]
    if t == 'bool':
        return 'true' if v else 'false'
    return str(int(v))


def dec(t, s):
    if t == 'f32':
        return struct.unpack('<f', struct.pack('<I', int(s, 16)))[0]
    if t == 'bool':
        return s == 'true'
    return int(s)


def main():
    name, path = sys.argv[1], sys.argv[2]
    given = dict(a.split('=', 1) for a in sys.argv[3:])
    schema = mp.load_schema(os.path.join(H, 'build', 'gen', name, 'module_schema.json'))
    case = json.load(open(path))
    added = []

    def fill(fields, rec, port):
        out = {}
        for f in fields:
            if f['name'] in rec:
                out[f['name']] = rec[f['name']]
            else:
                v = given.get(f['name'], 'false' if f['type'] == 'bool' else '0')
                out[f['name']] = enc(f['type'], float(v) if f['type'] == 'f32' else v == 'true' if f['type'] == 'bool' else int(v))
                added.append('%s %s = %s' % (port, f['name'], v))
        return out

    params = fill(schema['params'], case['params'], 'parameter')
    n0 = len(added)
    inputs = [fill(schema['input'], r, 'input') for r in case['inputs']]
    added_inputs = sorted(set(a for a in added[n0:]))
    added = added[:n0] + added_inputs
    p = subprocess.Popen([os.path.join(H, 'build', 'modules', name, name)], stdin=subprocess.PIPE,
                         stdout=subprocess.PIPE)

    def req(b, nout=0):
        p.stdin.write(b)
        p.stdin.flush()
        if p.stdout.read(1) != b'K':
            raise SystemExit('module refused')
        return p.stdout.read(nout) if nout else b''

    tp = {f['name']: f['type'] for f in schema['params']}
    ti = {f['name']: f['type'] for f in schema['input']}
    req(b'I' + mp.pack(schema['params'], {k: dec(tp[k], v) for k, v in params.items()}))
    nout = mp.record_bytes(schema['output'])
    outs, new_out = [], set()
    for k, (inp, rec) in enumerate(zip(inputs, case['outputs'])):
        got = mp.unpack(schema['output'], req(b'S' + mp.pack(schema['input'], {n: dec(ti[n], v) for n, v in inp.items()}), nout))
        o = {}
        for f in schema['output']:
            g = enc(f['type'], got[f['name']])
            if f['name'] in rec:
                if rec[f['name']] != g:
                    raise SystemExit('step %d: %s recorded %s, the executable gives %s; nothing written' %
                                     (k, f['name'], rec[f['name']], g))
                o[f['name']] = rec[f['name']]
            else:
                o[f['name']] = g
                new_out.add(f['name'])
        outs.append(o)
    req(b'Q')
    note = case.get('note', '')
    line = ('Fields added to the schemas later (2026-11-19), not hand-checked: %s; the recorded outputs are '
            'unchanged bit for bit.' % '; '.join(added + ['output %s as the executable gives it' % n
                                                          for n in sorted(new_out)]))
    case.update(params=params, inputs=inputs, outputs=outs, note=(note + ' ' + line).strip())
    with open(path, 'w') as fh:
        json.dump(case, fh, indent=1)
        fh.write('\n')
    print('%s: %d steps, every recorded output bit for bit; %s' % (path, len(outs), line))


if __name__ == '__main__':
    main()
