"""Shared by the PX4 modules' hand_checked_case.py scripts: binary32 helpers, the schemas of a
module's Ports.lean, PX4's parameter defaults, and the writer of hand-checked-case.json (the
format `harness replay FILE` reads: every field of every record as a word)."""
import json, os, re, struct

HARNESS = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))


def f(x):
    """x rounded to binary32."""
    return struct.unpack('<f', struct.pack('<f', x))[0]


def hx(x):
    return '0x%08x' % struct.unpack('<I', struct.pack('<f', x))[0]


def schema(name, label):
    txt = open(os.path.join(HARNESS, 'px4', 'modules', name, 'Ports.lean')).read()
    # the schema's rows, in either layout of px4/ports.py (one array, or chunks joined by ++)
    block = re.search(rf'def {label} : Schema :=(.*?)(?:\n(?:def |/--|end |set_option)|\Z)', txt,
                      re.S).group(1)
    return re.findall(r'name := "([^"]+)", type := \.(\w+)', block)


def defaults(name):
    pj = json.load(open(os.path.join(HARNESS, 'build/gen', name, 'parameters/parameters.json')))
    return {p['name']: p['default'] for p in pj['parameters']}


def word(t, v):
    if t == 'f32':
        return hx(v)
    if t == 'bool':
        return 'true' if v else 'false'
    return str(int(v)) if t == 'i32' else str(int(v) & 0xffffffff)


def record(name, label, vals):
    """Every field of the schema, zero unless given."""
    sch = schema(name, label)
    unknown = set(vals) - {n for n, _ in sch}
    if unknown:
        raise SystemExit(f'{name}: no {label} fields {sorted(unknown)}')
    return {n: word(t, vals.get(n, 0.0 if t == 'f32' else (False if t == 'bool' else 0)))
            for n, t in sch}


def write(name, note, params, inputs, outputs, path):
    d = defaults(name)
    d.update(params)
    P = {n: word(t, d[n]) for n, t in schema(name, 'params')}
    case = {"module": name, "code_hash": "(computed by hand)", "campaign": "none",
            "kind": "hand-checked", "clause": "", "case": 0, "step": len(inputs) - 1,
            "note": ' '.join(note.split()), "params": P,
            "inputs": [record(name, 'input', i) for i in inputs],
            "outputs": [record(name, 'output', o) for o in outputs]}
    json.dump(case, open(path, 'w'), indent=2)
