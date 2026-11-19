#!/usr/bin/env python3
"""regime_case.py SYSTEM REGIME OUT.json --steps N [--set NAME=VALUE ...]

A replayable case of a composite (system) node built from one of its regimes, for `harness replay`
and py/replay_csv.py (which then needs no --steps: the file holds every input record). Every
parameter and input field gets the value the regime pins (`X = v`, NaN as `¬X = X`), the midpoint
of a range the regime states (`lo ≤ X`, `X ≤ hi`; `|X| ≤ b` gives 0), false for `¬X`, and for a
hint `X starts at A and increases by B` the value A + B * step; anything else is 0 / false and is
listed on stderr. --set overrides a parameter (or `in:NAME` an input field) last. The input records
after the first are written in the delta form (`inputs_delta`): only the fields that changed.

It reads the regime from `harness contract SYSTEM` and the field types from the children's
build/gen/*/module_schema.json. The case is not a campaign's case (a campaign draws the free values
from its seed); `harness replay` checks the composite's assumption on it like any other case."""
import glob, json, os, re, struct, subprocess, sys

HARNESS = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
NUM = r'(-?[0-9][0-9.e+-]*|inf|-inf)'


def field_types():
    types = {}
    for p in glob.glob(os.path.join(HARNESS, 'build/gen/*/module_schema.json')):
        s = json.load(open(p))
        for k in ('params', 'input', 'output'):
            for f in s.get(k, []):
                types[f['name']] = f['type']
    return types


class RegimeCase:
    """The values of one regime of a system: `params`, `first` (the first input record, words),
    `at(k)` (the input fields that change at step k: the hinted timestamps), `word(name, v)`."""

    def __init__(self, system, regime, sets=(), px4_defaults=False):
        """With `px4_defaults`, a parameter the regime does not pin to a value gets PX4's default
        (build/gen/*/parameters/parameters.json) rather than a range's midpoint or 0."""
        self.types = field_types()
        defaults = {}
        if px4_defaults:
            for p in glob.glob(os.path.join(HARNESS, 'build/gen/*/parameters/parameters.json')):
                for q in json.load(open(p))['parameters']:
                    defaults.setdefault(q['name'], q['default'])
        H = os.path.join(HARNESS, '.lake/build/bin/harness')
        tree = subprocess.run([H, 'tree', system, '--depth', '1'], cwd=HARNESS,
                              capture_output=True, text=True).stdout
        contract = subprocess.run([H, 'contract', system], cwd=HARNESS, capture_output=True,
                                  text=True).stdout
        line = next((l for l in contract.splitlines() if l.startswith(f'regime {regime}:')), None)
        if line is None:
            sys.exit(f'regime_case: {system} has no regime {regime}')
        # the composite's own parameters and inputs: the children's fields marked "← param/input"
        pnames, inames = [], []
        for l in tree.splitlines():
            m = re.match(r'\s+(param|input) (\S+) ← (param|input) (\S+)$', l)
            if m:
                (pnames if m.group(3) == 'param' else inames).append(m.group(4))
        pnames, inames = list(dict.fromkeys(pnames)), list(dict.fromkeys(inames))
        if not pnames or not inames:
            sys.exit('regime_case: cannot read the composite fields from `harness tree`')
        val, lo, hi, self.hints = {}, {}, {}, {}
        for item in line.split(':', 1)[1].split(';'):
            item = item.strip()
            m = re.match(rf'(\S+) starts at {NUM} and increases by {NUM}', item)
            if m:
                self.hints[m.group(1)] = (float(m.group(2)), float(m.group(3)))
                continue
            expr = item.split(': ', 1)[1] if ': ' in item else item
            for c in expr.split(' ∧ '):
                c = c.strip().lstrip('(').rstrip(')').strip()
                if m := re.fullmatch(rf'(\w+) = {NUM}', c):
                    val[m.group(1)] = float(m.group(2))
                elif m := re.fullmatch(r'(\w+) = (true|false)', c):
                    val[m.group(1)] = m.group(2) == 'true'
                elif m := re.fullmatch(r'¬(\w+) = (\w+)', c):
                    if m.group(1) == m.group(2):
                        val[m.group(1)] = float('nan')
                elif m := re.fullmatch(r'¬(\w+)', c):
                    val[m.group(1)] = False
                elif m := re.fullmatch(r'(\w+)', c):
                    if m.group(1) not in ('true', 'false'):
                        val[m.group(1)] = True
                elif m := re.fullmatch(rf'{NUM} ≤ (\w+)', c):
                    lo[m.group(2)] = float(m.group(1))
                elif m := re.fullmatch(rf'(\w+) ≤ {NUM}', c):
                    hi[m.group(1)] = float(m.group(2))
                elif m := re.fullmatch(rf'\|(\w+)\| ≤ {NUM}', c):
                    lo[m.group(1)], hi[m.group(1)] = 0.0, 0.0
                elif m := re.fullmatch(rf'(\w+) < {NUM}', c):
                    hi[m.group(1)] = float(m.group(2)) - 1
        self.unset = []

        def value(name):
            if name in val: return val[name]
            if name in defaults and name in pnames: return defaults[name]
            if name in lo and name in hi: return (lo[name] + hi[name]) / 2
            if name in lo: return lo[name]
            if name in hi: return min(hi[name], 0.0)
            if name in self.hints: return self.hints[name][0]
            self.unset.append(name)
            return False if self.types[name] == 'bool' else 0
        self.params = {n: self.word(n, value(n)) for n in pnames}
        self.first = {n: self.word(n, value(n)) for n in inames}
        for s in sets:
            n, v = s.split('=', 1)
            tgt = self.params
            if n.startswith('in:'):
                n, tgt = n[3:], self.first
            tgt[n] = self.word(n, v == 'true' if self.types[n] == 'bool' else float(v))

    def word(self, name, v):
        t = self.types[name]
        if t == 'bool': return 'true' if v else 'false'
        if t == 'f32': return '0x%08x' % struct.unpack('<I', struct.pack('<f', float(v)))[0]
        return str(int(v))

    def at(self, k):
        return {n: self.word(n, a + b * k) for n, (a, b) in self.hints.items() if n in self.first}


def main():
    args = sys.argv[1:]
    system, regime, out = args[0], args[1], args[2]
    steps, sets = None, []
    i = 3
    while i < len(args):
        if args[i] == '--steps': steps = int(args[i + 1]); i += 2
        elif args[i] == '--set': sets.append(args[i + 1]); i += 2
        else: sys.exit(f'regime_case: unknown argument {args[i]}')
    if steps is None: sys.exit('regime_case: --steps N is required')
    rc = RegimeCase(system, regime, sets)
    inputs = [rc.first] + [rc.at(k) for k in range(1, steps)]
    case = {'system': system, 'code_hash': '-', 'kind': 'regime case', 'campaign': 'none',
            'clause': '', 'case': 0, 'step': steps - 1,
            'note': f'built by py/regime_case.py from regime {regime}',
            'params': rc.params, 'inputs': inputs, 'inputs_delta': True, 'outputs': []}
    json.dump(case, open(out, 'w'))
    print(f'{out}: {len(rc.params)} params, {len(rc.first)} input fields, {steps} steps; '
          f'{len(rc.unset)} fields not stated by the regime (0 / false)', file=sys.stderr)
    if rc.unset: print('  ' + ' '.join(rc.unset), file=sys.stderr)


if __name__ == '__main__':
    main()
