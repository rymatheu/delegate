#!/usr/bin/env python3
"""replay_csv.py CASE.json OUT.csv [--steps N] [--set NAME=VALUE ...] [--cols PREFIX,...]

Per-tick CSV of a node's run, through `harness replay` (nothing recorded). CASE.json is any saved
case (a campaign's counterexample or smallest-margin file). With --steps N the case's first input
record is held for N ticks (the right thing for a composite whose inputs are constant in its regime,
e.g. with a scripted test driver); --set changes a parameter (or `in:NAME` an input field) first.
Columns: the step, every input and output field (or those starting with one of --cols)."""
import csv, json, os, struct, subprocess, sys, tempfile

HARNESS = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
args = sys.argv[1:]
src, out = args[0], args[1]
steps, sets, cols = None, [], None
i = 2
while i < len(args):
    if args[i] == '--steps': steps = int(args[i + 1]); i += 2
    elif args[i] == '--set': sets.append(args[i + 1]); i += 2
    elif args[i] == '--cols': cols = args[i + 1].split(','); i += 2
    else: sys.exit(f'replay_csv: unknown argument {args[i]}')
if not sets and steps is None:
    # the saved case as it is (no rewrite: a long case's file can be large)
    tmp, made = src, False
else:
    j = json.load(open(src))
    if 'inputs_file' in j:
        sys.exit('replay_csv: a long case with its inputs in a shared inputs file; --set and '
                 '--steps need a case with its own inputs (replay it as it is)')
    key = 'system' if 'system' in j else 'module'
    case = {key: j[key], 'params': dict(j['params']), 'code_hash': j.get('code_hash', '-')}
    inp = dict(j['inputs'][0])
    for s in sets:
        n, v = s.split('=', 1)
        tgt = case['params']
        if n.startswith('in:'): n, tgt = n[3:], inp
        old = tgt[n]
        tgt[n] = ('0x%08x' % struct.unpack('<I', struct.pack('<f', float(v)))[0]) if old.startswith('0x') else v
    if steps is None:
        case['inputs'] = j['inputs']
        if j.get('inputs_delta'):
            case['inputs_delta'] = True
    else:
        case['inputs'] = [inp] * steps
    case['outputs'] = j['outputs'][-1:]          # compared at the last step only (none: not compared)
    del j
    with tempfile.NamedTemporaryFile('w', suffix='.json', delete=False) as f:
        json.dump(case, f)
        tmp, made = f.name, True
# the replay's output, read line by line (a long case prints gigabytes), only the kept columns
p = subprocess.Popen([os.path.join(HARNESS, '.lake/build/bin/harness'), 'replay', tmp], cwd=HARNESS,
                     stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, errors='replace')
keep = (lambda n: True) if cols is None else (lambda n: any(n.startswith(c) for c in cols))
rows, cur, names, tail = [], None, None, []
verdict = ''
for line in p.stdout:
    if line.startswith('  step '):
        k, rest = line[7:].split(':', 1)
        cur = {'step': int(k)}
        cur.update(kv.split('=', 1) for kv in rest.split() if '=' in kv and keep(kv.split('=', 1)[0]))
    elif cur is not None and (line.startswith('       ≠ ') or line.startswith('       = ')):
        cur.update(kv.split('=', 1) for kv in line[9:].split()
                   if '=' in kv and not kv.startswith('violates') and keep(kv.split('=', 1)[0]))
        rows.append(cur)
        cur = None
    else:
        tail = (tail + [line])[-20:]
        if line.startswith('outputs '):
            verdict = line.strip()
err = p.stderr.read()
p.wait()
if made:
    os.unlink(tmp)
if not rows:
    sys.exit('replay_csv: no steps parsed\n' + ''.join(tail)[-2000:] + err[-2000:])
names = list(rows[0].keys())
if cols:
    names = ['step'] + [n for n in names if n != 'step']
with open(out, 'w', newline='') as f:
    w = csv.writer(f)
    w.writerow(names)
    for row in rows:
        w.writerow([row.get(n, '') for n in names])
print(f'{out}: {len(rows)} steps, {len(names)} columns; replay: {verdict}')
sys.stderr.write(err)
