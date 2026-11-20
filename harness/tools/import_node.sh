#!/usr/bin/env bash
# Bring one node from an old-layout copy of this project into this layout:
#
#   tools/import_node.sh SRC KIND NAME STACK
#     SRC    an old-layout copy (modules/ and harnesses/ side by side at its root); read only
#     KIND   modules | harnesses
#     NAME   the node's folder name (SRC/KIND/NAME)
#     STACK  ardupilot | px4 | sim
#
# What it does:
#   1. Copies SRC/KIND/NAME to STACK/KIND/NAME here, without its evidence/ folder (evidence
#      stays with the copy it was made in; the code hashes change with the paths anyway).
#   2. Rewrites, in the copied files only:
#      - Lean imports `modules.X.` / `harnesses.X.` to `STACK(X).modules.X.` / `...harnesses.X.`
#      - namespaces and references `Modules.Foo` / `Harnesses.Foo` to `Ardupilot.Modules.Foo`,
#        `Px4.Modules.Foo`, `Sim.Modules.Foo`, ... (by where Foo lives here, or is being put), in
#        Lean files and in any other file that writes Lean (contains `namespace Modules.` or
#        `namespace Harnesses.`, e.g. a generator of a Lean file)
#      - paths: modules/build.sh -> ardupilot/build.sh, modules/gen_mavlink.sh ->
#        ardupilot/gen_mavlink.sh, modules/px4_gen.sh -> px4/gen.sh, modules/px4_build.sh ->
#        px4/build.sh, py/px4_ports.py -> px4/ports.py, cpp/px4_shim -> px4/shim, and
#        modules/X, harnesses/X, $HARNESS/modules/X to the stack's folder, for every X that is
#        a node (here, in SRC, or this one); other paths (build/modules/X, src/modules/...,
#        ArduPilot's modules/mavlink) are left alone
#      - a script or program of the node that finds the project root by going up from its own
#        folder goes up one folder more: `$(dirname "$0")/../..`, `$HERE/../..`,
#        `HERE.parent.parent`, `os.path.dirname(os.path.dirname(HERE))`, `os.path.join(HERE,
#        '..', '..')`, and the `__file__` forms; only chains that reached exactly the old root
#        (two folders up from the node's folder) are changed, and each change is printed
#      - Module.lean: `stack := .STACK` after the `exe :=` line of the declaration
#   3. Prints the lines to add to Main.lean (imports and registry entries), the generic files of
#      SRC (Harness/, cpp/, py/, the build scripts) changed in that copy since the layout moved
#      (by tools/old_layout_generic.sha256), which have to be merged by hand, and any line of
#      the copy that still looks like an old-layout path.
#   With BACKUP=DIR in the environment, a node that is already here (same stack and kind) is
#   replaced: its files other than evidence/ are moved to DIR/STACK/KIND/NAME first, and its
#   evidence stays (the ledger then shows its old records as stale until they are re-backed).
# Nothing is written outside STACK/KIND/NAME (and BACKUP), and nothing in SRC.
set -euo pipefail

usage="usage: tools/import_node.sh SRC modules|harnesses NAME ardupilot|px4|sim"
[ $# -eq 4 ] || { echo "$usage" >&2; exit 2; }
SRC="$(cd "$1" && pwd -P)"
KIND="$2"
NAME="$3"
STACK="$4"
HARNESS="$(cd "$(dirname "$0")/.." && pwd -P)"
case "$KIND" in modules|harnesses) ;; *) echo "$usage" >&2; exit 2 ;; esac
case "$STACK" in ardupilot|px4|sim) ;; *) echo "$usage" >&2; exit 2 ;; esac
[[ "$NAME" =~ ^[a-z_][a-z0-9_]*$ ]] || { echo "import_node.sh: '$NAME' is not a node name" >&2; exit 2; }
[ "$SRC" != "$HARNESS" ] || { echo "import_node.sh: SRC is this project" >&2; exit 2; }
FROM="$SRC/$KIND/$NAME"
DEST="$HARNESS/$STACK/$KIND/$NAME"
[ -d "$FROM" ] || { echo "import_node.sh: no $FROM (is SRC an old-layout copy?)" >&2; exit 1; }
for k in modules harnesses; do
  for s in ardupilot px4 sim; do
    [ -e "$HARNESS/$s/$k/$NAME" ] || continue
    if [ -n "${BACKUP:-}" ] && [ "$s/$k" = "$STACK/$KIND" ]; then
      # replace it: everything but its evidence/ is moved to $BACKUP/STACK/KIND/NAME first
      [ ! -e "$BACKUP/$s/$k/$NAME" ] ||
        { echo "import_node.sh: $BACKUP/$s/$k/$NAME exists; nothing done" >&2; exit 1; }
      mkdir -p "$BACKUP/$s/$k/$NAME"
      for f in "$HARNESS/$s/$k/$NAME"/* "$HARNESS/$s/$k/$NAME"/.[!.]*; do
        [ -e "$f" ] || continue
        [ "$(basename "$f")" = evidence ] || mv "$f" "$BACKUP/$s/$k/$NAME/"
      done
      echo "moved $s/$k/$NAME (all but evidence/) to $BACKUP/$s/$k/$NAME"
    else
      echo "import_node.sh: $s/$k/$NAME exists here already; nothing done" \
           "(BACKUP=DIR replaces it, keeping its evidence)" >&2
      exit 1
    fi
  done
done

# 1. copy, without the evidence and without build or editor droppings
mkdir -p "$(dirname "$DEST")"
rsync -a --exclude '/evidence/' --exclude '__pycache__/' --exclude '.DS_Store' "$FROM/" "$DEST/"
echo "copied $FROM"
echo "    -> $STACK/$KIND/$NAME (without evidence/)"

# 2 and 3
"$HARNESS/../sim/.venv/bin/python" -I - "$SRC" "$HARNESS" "$KIND" "$NAME" "$STACK" <<'PY'
import os, re, sys

SRC, HARNESS, KIND, NAME, STACK = sys.argv[1:]
DEST = os.path.join(HARNESS, STACK, KIND, NAME)
STACKS = ['ardupilot', 'px4', 'sim']
NS = {'ardupilot': 'Ardupilot', 'px4': 'Px4', 'sim': 'Sim'}
KNS = {'modules': 'Modules', 'harnesses': 'Harnesses'}
warnings = []

def guess(name):
    """The stack of a node that is neither here nor being imported (a warning is printed)."""
    if name == 'plant_sim':
        return 'sim'
    return 'px4' if name.startswith('px4') else 'ardupilot'

def camel(name):
    return ''.join(w.capitalize() for w in name.split('_'))

# where every node folder is here: (kind, name) -> stack
here = {}
for s in STACKS:
    for k in KNS:
        d = os.path.join(HARNESS, s, k)
        if os.path.isdir(d):
            for n in os.listdir(d):
                if os.path.isdir(os.path.join(d, n)):
                    here[(k, n)] = s
here[(KIND, NAME)] = STACK
old_nodes = set()
for k in KNS:
    d = os.path.join(SRC, k)
    if os.path.isdir(d):
        old_nodes |= {(k, n) for n in os.listdir(d) if os.path.isdir(os.path.join(d, n))}

def stack_of(kind, name, what):
    if (kind, name) in here:
        return here[(kind, name)]
    g = guess(name)
    warnings.append(f'{what}: {kind}/{name} is not in this project yet; assumed stack {g} '
                    f'(import it with tools/import_node.sh ... {kind} {name} {g})')
    return g

# namespaces: (Modules|Harnesses, Leaf) -> Lean stack prefix, from the Lean files here and the
# namespaces the copied node declares
ns_here = {}
for s in STACKS:
    for root, _, files in os.walk(os.path.join(HARNESS, s)):
        if '/evidence' in root:
            continue
        for f in files:
            if f.endswith('.lean'):
                for m in re.finditer(r'^namespace (Ardupilot|Px4|Sim)\.(Modules|Harnesses)\.(\w+)',
                                     open(os.path.join(root, f)).read(), re.M):
                    ns_here[(m.group(2), m.group(3))] = m.group(1)
own_ns = set()
for root, _, files in os.walk(DEST):
    for f in files:
        if f.endswith('.lean'):
            for m in re.finditer(r'^namespace (Modules|Harnesses)\.(\w+)',
                                 open(os.path.join(root, f)).read(), re.M):
                ns_here[(m.group(1), m.group(2))] = NS[STACK]
                own_ns.add((m.group(1), m.group(2)))

def ns_of(k, leaf, what):
    if (k, leaf) in ns_here:
        return ns_here[(k, leaf)]
    # a namespace is the CamelCase of a folder name: find the folder
    for (kind, n), s in here.items():
        if KNS[kind] == k and camel(n) == leaf:
            return NS[s]
    snake = re.sub(r'(?<!^)(?=[A-Z])', '_', leaf).lower()
    g = guess(snake)
    warnings.append(f'{what}: namespace {k}.{leaf} is not in this project yet; assumed {NS[g]}')
    return NS[g]

FIXED = [('modules/build.sh', 'ardupilot/build.sh'),
         ('modules/gen_mavlink.sh', 'ardupilot/gen_mavlink.sh'),
         ('modules/px4_gen.sh', 'px4/gen.sh'), ('modules/px4_build.sh', 'px4/build.sh'),
         ('py/px4_ports.py', 'px4/ports.py'), ('cpp/px4_shim', 'px4/shim'),
         ('modules/plain_build.sh', 'px4/plain_build.sh'),
         ('cpp/px4_test_drive.h', 'px4/px4_test_drive.h')]
PRE = r'(?<![\w/.$-])'
nodes = {n for (_, n) in here} | {n for (_, n) in old_nodes}

def rewrite(text, lean, what, own):
    """The text with old-layout paths, imports and namespaces rewritten; `own`: for a file of
    the imported node, how many folders below the node's folder it is (the depth fixes apply);
    None otherwise."""
    for a, b in FIXED:
        text = re.sub(PRE + re.escape(a), b, text)
        text = re.sub(r'(?<=HARNESS/)' + re.escape(a), b, text)
        text = re.sub(r'(?<=HARNESS\}/)' + re.escape(a), b, text)
    def path(m):
        pre, k, n = m.group(1), m.group(2), m.group(3)
        if n not in nodes and (k, n) not in old_nodes:
            return m.group(0)
        return f'{pre}{stack_of(k, n, what)}/{k}/{n}'
    text = re.sub(r'(\$HARNESS/|\$\{HARNESS\}/)(modules|harnesses)/(\w+)', path, text)
    text = re.sub(r'(\$HARNESS/|\$\{HARNESS\}/)(modules|harnesses)/\$', lambda m:
                  f'{m.group(1)}{STACK}/{m.group(2)}/$', text)
    text = re.sub(PRE + r'()(modules|harnesses)/([a-z_][a-z0-9_]*)\b', path, text)
    # Python joins from the root: os.path.join(HARNESS, 'modules', 'x') by x's stack, and
    # os.path.join(HARNESS, 'modules', name) (a variable) by this node's stack
    def pyjoin(m):
        k, rest = m.group(2), m.group(3)
        lit = re.match(r"'([a-z_][a-z0-9_]*)'", rest)
        s = stack_of(k, lit.group(1), what) if lit and (lit.group(1) in nodes or (k, lit.group(1))
                                                         in old_nodes) else STACK
        return f"{m.group(1)}'{s}', '{k}', {rest}"
    text = re.sub(r"(os\.path\.join\(HARNESS, )'(modules|harnesses)', ([^)]*)", pyjoin, text)
    if lean:
        text = re.sub(r'^import (modules|harnesses)\.(\w+)\.', lambda m:
                      f'import {stack_of(m.group(1), m.group(2), what)}.{m.group(1)}.{m.group(2)}.',
                      text, flags=re.M)
        text = re.sub(r'(?<![\w.])(Modules|Harnesses)\.([A-Z]\w*)', lambda m:
                      f'{ns_of(m.group(1), m.group(2), what)}.{m.group(1)}.{m.group(2)}', text)
    if own is not None:
        text = deeper(text, own, what)
    return text

def deeper(text, d, what):
    """A file `d` folders below the node's folder reached the project root `d + 2` folders up
    from its own folder; now it is `d + 3`. Only chains of exactly that length are changed."""
    up = d + 2
    def fix(m, n, more):
        if n != up:
            return m.group(0)
        depth_fixes.append(f'{what}: {m.group(0)} -> {more}')
        return more
    # shell: $(dirname "$0")/../.., $HERE/../.. (HERE the script's folder)
    text = re.sub(r'(\$\(dirname "\$0"\)|\$HERE\b|\$\{HERE\})((?:/\.\.)+)(?![\w.])',
                  lambda m: fix(m, m.group(2).count('..'), m.group(0) + '/..'), text)
    # Python: HERE.parent..., os.path.dirname(...(HERE)), os.path.join(HERE, '..', ...)
    text = re.sub(r'\bHERE((?:\.parent)+)\b(?!\.parent)',
                  lambda m: fix(m, m.group(1).count('parent'), m.group(0) + '.parent'), text)
    text = re.sub(r'((?:os\.path\.dirname\()+)HERE(\)+)', lambda m: fix(
        m, m.group(1).count('dirname'), 'os.path.dirname(' + m.group(0) + ')'), text)
    text = re.sub(r"os\.path\.join\(HERE((?:, '\.\.')+)", lambda m: fix(
        m, m.group(1).count('..'), m.group(0) + ", '..'"), text)
    text = re.sub(r"os\.path\.join\(os\.path\.dirname\(os\.path\.abspath\(__file__\)\)((?:, '\.\.')+)",
                  lambda m: fix(m, m.group(1).count('..'), m.group(0) + ", '..'"), text)
    # Python from __file__: one more level (the file itself)
    text = re.sub(r'((?:os\.path\.dirname\()+)os\.path\.abspath\(__file__\)(\)+)', lambda m: fix(
        m, m.group(1).count('dirname') - 1, 'os.path.dirname(' + m.group(0) + ')'), text)
    text = re.sub(r'(Path\(__file__\)\.resolve\(\))((?:\.parent)+)\b(?!\.parent)', lambda m: fix(
        m, m.group(2).count('parent') - 1, m.group(0) + '.parent'), text)
    text = re.sub(r'(Path\(__file__\)\.resolve\(\)\.parents)\[(\d+)\]', lambda m: fix(
        m, int(m.group(2)), f'{m.group(1)}[{int(m.group(2)) + 1}]'), text)
    return text

changed = []
depth_fixes = []
for root, _, files in os.walk(DEST):
    for f in sorted(files):
        p = os.path.join(root, f)
        rel = os.path.relpath(p, HARNESS)
        try:
            text = open(p, encoding='utf-8').read()
        except (UnicodeDecodeError, IsADirectoryError):
            continue
        d = len(os.path.relpath(root, DEST).split(os.sep)) if root != DEST else 0
        # a program that writes Lean (a generator) carries Lean namespaces in its strings
        lean_text = f.endswith('.lean') or re.search(r'namespace (Modules|Harnesses)\.', text)
        new = rewrite(text, bool(lean_text), rel, d)
        if f == 'Module.lean' and KIND == 'modules':
            m = re.search(r'^def module : Module where\n((?:[ \t]+.*\n?)*)', new, re.M)
            if m and not re.search(r'^\s+stack :=', m.group(1), re.M):
                e = re.search(r'^([ \t]+)exe := .*$', m.group(1), re.M)
                if e:
                    at = m.start(1) + e.end()
                    new = new[:at] + f'\n{e.group(1)}stack := .{STACK}' + new[at:]
                else:
                    warnings.append(f'{rel}: no `exe :=` line in `def module : Module where`; '
                                    f'add `stack := .{STACK}` by hand')
            elif not m:
                warnings.append(f'{rel}: no `def module : Module where`; add `stack := .{STACK}` '
                                f'to the declaration by hand')
        if new != text:
            open(p, 'w', encoding='utf-8').write(new)
            changed.append(rel)
print('rewrote:' if changed else 'rewrote: nothing')
for c in changed:
    print(f'    {c}')
if depth_fixes:
    print('one more folder up to the project root:')
    for x in depth_fixes:
        print(f'    {x}')

# 3. the lines for Main.lean
entries = [f for f in ['Module.lean'] if KIND == 'modules'] or \
          [f for f in ['Harness.lean', 'Composed.lean'] if os.path.exists(os.path.join(DEST, f))]
imports = [f'import {STACK}.{KIND}.{NAME}.{f[:-5]}' for f in entries
           if os.path.exists(os.path.join(DEST, f))]
reg = []
old_main = os.path.join(SRC, 'Main.lean')
if os.path.exists(old_main):
    mt = open(old_main).read()
    pat = (r'entry \(\.(?:module|system) (?:Modules|Harnesses)\.\w+\.\w+\)'
           r'|composed "[^"]+" (?:Modules|Harnesses)\.\w+\.\w+')
    for m in re.finditer(pat, mt):
        k, leaf = re.search(r'(Modules|Harnesses)\.(\w+)\.', m.group(0)).groups()
        if (k, leaf) in own_ns:
            reg.append(rewrite(m.group(0), True, 'Main.lean', None))
if not reg:
    for k, leaf in sorted(own_ns):
        if k == 'Modules' and KIND == 'modules' and re.search(r'^def module : Module\b',
                open(os.path.join(DEST, 'Module.lean')).read() if os.path.exists(
                    os.path.join(DEST, 'Module.lean')) else '', re.M):
            reg.append(f'entry (.module {NS[STACK]}.Modules.{leaf}.module)')
        elif k == 'Harnesses':
            f = [g for g in entries if f'namespace Harnesses.{leaf}' in
                 open(os.path.join(SRC, KIND, NAME, g)).read()]
            src = open(os.path.join(SRC, KIND, NAME, f[0])).read() if f else ''
            if re.search(r'^def system : Sys\b', src, re.M):
                reg.append(f'entry (.system {NS[STACK]}.Harnesses.{leaf}.system)')
            else:
                m = re.search(r'compose(?:All)? "([^"]+)"', src)
                reg.append(f'composed "{m.group(1) if m else NAME}" '
                           f'{NS[STACK]}.Harnesses.{leaf}.system')
print()
if imports or reg:
    print('add to Main.lean, with the other imports of this stack:')
    for i in imports:
        print(f'  {i}')
    print('and to `registry`, in the block of this stack:')
    for r in reg:
        print(f'  {r},')
else:
    print('not a node (no Module.lean, Harness.lean or Composed.lean): nothing to add to Main.lean;')
    print('the nodes that import it find it at its new path')

# generic files of SRC changed since the layout moved (tools/old_layout_generic.sha256): the
# tool does not bring them in; they are listed with their place here, to merge by hand
import hashlib
HERE_OF = {'modules/build.sh': 'ardupilot/build.sh', 'modules/gen_mavlink.sh': 'ardupilot/gen_mavlink.sh',
           'modules/px4_build.sh': 'px4/build.sh', 'modules/px4_gen.sh': 'px4/gen.sh',
           'py/px4_ports.py': 'px4/ports.py', 'modules/plain_build.sh': 'px4/plain_build.sh',
           'cpp/px4_test_drive.h': 'px4/px4_test_drive.h'}
def here_of(rel):
    if rel.startswith('cpp/px4_shim/'):
        return 'px4/shim/' + rel[len('cpp/px4_shim/'):]
    if rel.startswith('modules/') and rel not in HERE_OF:
        return 'ardupilot/ or px4/, by the stack it serves'
    return HERE_OF.get(rel, rel)
base = {}
for l in open(os.path.join(HARNESS, 'tools', 'old_layout_generic.sha256')):
    if l.strip() and not l.startswith('#'):
        h, rel = l.split(None, 1)
        base[rel.strip()] = h
cands = set(base)
for d in ['Harness', 'cpp', 'py']:
    for root, _, files in os.walk(os.path.join(SRC, d)):
        cands |= {os.path.relpath(os.path.join(root, f), SRC) for f in files
                  if not f.startswith('.') and '__pycache__' not in root}
cands.add('Harness.lean')
d = os.path.join(SRC, 'modules')
cands |= {f'modules/{f}' for f in os.listdir(d) if os.path.isfile(os.path.join(d, f))}
differ = []
for rel in sorted(cands):
    p = os.path.join(SRC, rel)
    if not os.path.isfile(p):
        continue
    h = hashlib.sha256(open(p, 'rb').read()).hexdigest()
    if rel not in base:
        differ.append(f'{rel}: new in that copy (here it would be {here_of(rel)})')
    elif h != base[rel]:
        differ.append(f'{rel}: differs (here: {here_of(rel)})')
odd = sorted(n for (k, n) in old_nodes if (k, n) not in here and k == 'modules'
             and not os.path.exists(os.path.join(SRC, k, n, 'Module.lean')))
if differ or odd:
    print()
    print('generic files of the copy that differ from their version at the move (older there, or changed there;\n'
          'not brought in, compare and merge by hand):')
    for x in differ:
        print(f'  {x}')
    for n in odd:
        print(f'  modules/{n}/: a folder with no Module.lean (shared files?); if a node imports it, '
              f'bring it in the same way (tools/import_node.sh SRC modules {n} STACK)')

# what still looks like an old-layout path in the copy
left = []
for root, _, files in os.walk(DEST):
    for f in sorted(files):
        p = os.path.join(root, f)
        try:
            lines = open(p, encoding='utf-8').read().split('\n')
        except UnicodeDecodeError:
            continue
        for i, l in enumerate(lines):
            if re.search(PRE + r'(modules|harnesses)/[\w<$]', l) or \
               re.search(r'^import (modules|harnesses)\.', l):
                left.append(f'{os.path.relpath(p, HARNESS)}:{i + 1}: {l.strip()[:90]}')
if left:
    print()
    print('lines that still look like old-layout paths (intentional ones are fine):')
    for l in left:
        print(f'  {l}')
if warnings:
    print()
    print('warnings:')
    for w in dict.fromkeys(warnings):
        print(f'  {w}')
print()
if KIND == 'modules':
    build = {'ardupilot': f'ardupilot/build.sh {NAME}', 'px4': f'px4/build.sh {NAME}',
             'sim': f'sim/modules/{NAME}/build.sh'}[STACK]
    print(f'then: LEAN_NUM_THREADS=1 lake build; {build}; .lake/build/bin/harness describe {NAME}')
else:
    print(f'then: LEAN_NUM_THREADS=1 lake build; .lake/build/bin/harness tree {NAME} --depth 1 '
          f'(its stack is inferred from its children unless it declares one)')
PY
