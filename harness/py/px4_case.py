"""px4_case.py: write a hand-checked case of a PX4 harness module from a scripted input sequence.

A PX4 module's outputs carry hundreds of fields; only some of them are worked out by hand. A
hand-checked case script (px4/modules/NAME/hand_checked_case.py) gives the parameters (PX4's
defaults, with overrides), the input records by field name, and the values it derived from the
code for some output fields at some steps. `record` runs the module executable over the module
protocol once, checks every derived value against what the module returned (and stops with the
differences if any does not match), and writes px4/modules/NAME/hand-checked-case.json with the full
records, which `harness replay` then reproduces bit for bit. So the JSON is a recorded run, and
the hand-derived part is the script's list of expectations, checked when the case is written."""
import json
import math
import os
import struct
import subprocess
import sys

HARNESS = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def _schema(name):
    return json.load(open(os.path.join(HARNESS, 'build/gen', name, 'module_schema.json')))


def defaults(name):
    """PX4's default of every parameter of the module (its generated parameter table)."""
    pj = json.load(open(os.path.join(HARNESS, 'build/gen', name, 'parameters/parameters.json')))
    d = {p['name']: p['default'] for p in pj['parameters']}
    return {f['name']: d[f['name']] for f in _schema(name)['params']}


def _f32(x):
    return struct.unpack('<f', struct.pack('<f', x))[0]


def _word(t, v):
    if t == 'bool':
        return 'true' if v else 'false'
    if t == 'f32':
        return '0x%08x' % struct.unpack('<I', struct.pack('<f', v))[0]
    return str(int(v))


def _pack(fields, rec):
    b = b''
    for f in fields:
        v, t = rec.get(f['name'], 0), f['type']
        if t == 'bool':
            b += bytes([1 if v else 0])
        elif t == 'f32':
            b += struct.pack('<f', v)
        elif t == 'u32':
            b += struct.pack('<I', int(v) & 0xffffffff)
        else:
            b += struct.pack('<i', int(v))
    return b


def _unpack(fields, buf):
    out, o = {}, 0
    for f in fields:
        t = f['type']
        if t == 'bool':
            out[f['name']] = bool(buf[o])
            o += 1
        else:
            fmt = {'f32': '<f', 'u32': '<I', 'i32': '<i'}[t]
            out[f['name']] = struct.unpack(fmt, buf[o:o + 4])[0]
            o += 4
    return out


def _same(a, b):
    if isinstance(b, float):
        return (math.isnan(a) and math.isnan(b)) or _f32(b) == a
    return a == b


def record(name, params, inputs, expect, note):
    """Run, check `expect` ({step: {field: value}}), write the case; returns the outputs."""
    sch = _schema(name)
    exe = os.path.join(HARNESS, 'build/modules', name, name)
    p = subprocess.Popen([exe], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    size = sum(1 if f['type'] == 'bool' else 4 for f in sch['output'])

    def req(b, n):
        p.stdin.write(b)
        p.stdin.flush()
        r = p.stdout.read(n)
        if len(r) < n:
            sys.exit(f'{name}: the executable stopped')
        return r
    req(b'I' + _pack(sch['params'], params), 1)
    outs = [_unpack(sch['output'], req(b'S' + _pack(sch['input'], i), 1 + size)[1:]) for i in inputs]
    req(b'Q', 1)
    bad = [(k, f, v, outs[k][f]) for k, fs in sorted(expect.items()) for f, v in fs.items()
           if not _same(outs[k][f], v)]
    for k, f, v, got in bad:
        print(f'step {k}: {f} worked out {v}, module returned {got}')
    if bad:
        sys.exit(f'{name}: {len(bad)} worked-out values differ; case not written')
    case = {'module': name, 'code_hash': '(computed by hand)', 'campaign': 'none',
            'kind': 'hand-checked', 'clause': '', 'case': 0, 'step': len(inputs) - 1,
            'note': note.strip().replace('\n', ' '),
            'expected': {str(k): {f: _word(next(x['type'] for x in sch['output'] if x['name'] == f), v)
                                  for f, v in fs.items()} for k, fs in sorted(expect.items())},
            'params': {f['name']: _word(f['type'], params[f['name']]) for f in sch['params']},
            'inputs': [{f['name']: _word(f['type'], i.get(f['name'], 0)) for f in sch['input']}
                       for i in inputs],
            'outputs': [{f['name']: _word(f['type'], o[f['name']]) for f in sch['output']} for o in outs]}
    path = os.path.join(HARNESS, 'px4', 'modules', name, 'hand-checked-case.json')
    json.dump(case, open(path, 'w'), indent=1)
    print(f'{name}: {sum(len(v) for v in expect.values())} worked-out values match; wrote {path}')
    return outs
