#!/usr/bin/env python3
"""px4/ports.py NAME: the ports of a PX4 harness module, generated from PX4's own definitions.

Reads px4/modules/NAME/px4.txt (the module's entry point, its sources, the directories PX4's parameter
tool scans, the uORB topics it subscribes to and publishes, and PX4 generators to run (pygen)), PX4's .msg files and PX4's
parameter definitions, and writes:

  px4/modules/NAME/Ports.lean      the parameter, input and output schemas (Lean), the documented
                                   parameter ranges and the integer-width assumptions as clauses
  build/gen/NAME/px4_ports.cpp     the C++ between the harness records and PX4's uORB structs and
                                   parameter store, and the call of the module's entry point
  build/gen/NAME/parameters/       px4_parameters.hpp and parameters.json, made by PX4's tools
                                   (src/lib/parameters/px_process_params.py, px_generate_params.py)

Naming (so that modules compose by name, with no renaming):
  parameter     its PX4 name                         MC_ROLLRATE_P
  topic field   <topic>_<field>, arrays _<index>,    vehicle_torque_setpoint_xyz_0
                nested messages <topic>_<field>_<sub>
  instance i>0  <topic><i>_...                       sensor_gyro1_x
  fresh flag    <topic>_updated (bool)               input: a message was published on the topic this
                                                     tick; output: the module published one this tick
  clock         t_us (u32)                           what hrt_absolute_time() returns this tick
  errors        <module>_errors (u32, output)        PX4_ERR/PX4_PANIC messages since init
  queued topic  a topic whose .msg sets ORB_QUEUE_LENGTH > 1 (vehicle_command) has N slots per
                tick (N = the queue length, or `slots N` in px4.txt, at most the queue length):
                slot 0 <topic>_<field>, slot k <topic>_q<k>_<field>, and
                <topic>_count (u32)                  input: the first count slots are published, in
                                                     order; output: messages the module published
                                                     this tick, oldest first, at most N
                <topic>_lost (u32, output)           messages published this tick beyond the N
                                                     newest (dropped, as uORB drops them for a
                                                     subscriber with an N-message queue)
                <topic>_updated (output only)        count > 0

Field types: float32 -> f32; bool -> bool; int8/16/32 -> i32 and uint8/16/32 -> u32 (with an
assumption clause for the narrower ranges); uint64/int64 -> u32/i32 carrying the low 32 bits
(the harness has no 64-bit fields; timestamps in us wrap after 71.6 min); float64 -> two f32
fields, <name> (the value rounded) and <name>_lo (the rest), whose sum carries 48 significant bits
(latitude in degrees to about 1e-12 deg), except in a queued topic's slots, where it is one f32
(rounded); char -> u32.
"""
import json
import os
import re
import subprocess
import sys

HARNESS = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PX4_ROOT = os.path.realpath(os.environ.get('PX4_ROOT', os.path.join(HARNESS, 'deps', 'px4')))
PY = os.path.join(HARNESS, 'build', 'px4venv', 'bin', 'python')
MSG_DIRS = [os.path.join(PX4_ROOT, 'msg'), os.path.join(PX4_ROOT, 'msg', 'versioned')]

BASIC = {
    'bool': ('bool', 'bool', None),
    'float32': ('f32', 'float', None),
    'float64': ('f32', 'double', None),
    'int8': ('i32', 'int8_t', (-128, 127)),
    'int16': ('i32', 'int16_t', (-32768, 32767)),
    'int32': ('i32', 'int32_t', None),
    'int64': ('i32', 'int64_t', None),
    'uint8': ('u32', 'uint8_t', (0, 255)),
    'uint16': ('u32', 'uint16_t', (0, 65535)),
    'uint32': ('u32', 'uint32_t', None),
    'uint64': ('u32', 'uint64_t', None),
    'char': ('u32', 'char', (0, 255)),
}


# bytes of each basic type in a uORB struct (the generated struct orders fields by size)
MSG_SIZE = {'bool': 1, 'float32': 4, 'float64': 8, 'int8': 1, 'int16': 2, 'int32': 4, 'int64': 8,
            'uint8': 1, 'uint16': 2, 'uint32': 4, 'uint64': 8, 'char': 1}


def snake(name):
    return re.sub(r'(?<!^)(?=[A-Z])', '_', name).lower()


def msg_index():
    """msg type (PascalCase) -> path; topic name -> msg type."""
    paths, topics = {}, {}
    for d in MSG_DIRS:
        for f in sorted(os.listdir(d)):
            if f.endswith('.msg'):
                t = f[:-4]
                paths[t] = os.path.join(d, f)
    for t, p in paths.items():
        named = []
        for line in open(p):
            m = re.match(r'\s*#\s*TOPICS\s+(.*)', line)
            if m:
                named += m.group(1).split()
        for tp in (named or [snake(t)]):
            topics[tp] = t
    return paths, topics


def queue_length(paths, t):
    """ORB_QUEUE_LENGTH of message type t (1 when the .msg does not set it)."""
    for line in open(paths[t]):
        m = re.match(r'\s*uint\d+\s+ORB_QUEUE_LENGTH\s*=\s*(\d+)', line)
        if m:
            return int(m.group(1))
    return 1


def parse_msg(paths, t):
    """The fields of message type t: [(name, type, array_len or None)], constants skipped."""
    fields = []
    for line in open(paths[t]):
        line = line.split('#', 1)[0].strip()
        if not line or '=' in line:
            continue
        typ, name = line.split()[:2]
        m = re.match(r'(.+)\[(\d+)\]$', typ)
        n = None
        if m:
            typ, n = m.group(1), int(m.group(2))
        typ = typ.split('/')[-1]
        fields.append((name, typ, n))
    return fields


def flatten(paths, t, prefix, cpath):
    """Leaves of message type t: (record field name, C++ lvalue path, msg basic type)."""
    out = []
    for name, typ, n in parse_msg(paths, t):
        idxs = [None] if n is None else list(range(n))
        for i in idxs:
            rec = f'{prefix}_{name}' + ('' if i is None else f'_{i}')
            cp = f'{cpath}.{name}' + ('' if i is None else f'[{i}]')
            if typ in BASIC:
                out.append((rec, cp, typ))
            else:
                out += flatten(paths, typ, rec, cp)
    return out


def read_config(name):
    cfg = {'main': None, 'args': [], 'sources': [], 'includes': [], 'params': [], 'sub': [], 'pub': [],
           'start': [], 'process': 'reuse', 'run': [], 'stream': [], 'pygen': [], 'gensources': [],
           'mirror': {}, 'params_readonly': False, 'by': set(), 'merge': None}
    for line in open(os.path.join(HARNESS, 'px4', 'modules', name, 'px4.txt')):
        line = line.split('#', 1)[0].strip()
        if not line:
            continue
        key, *rest = line.split()
        if key == 'main':
            cfg['main'] = rest[0]
        elif key == 'args':
            cfg['args'] = rest
        elif key == 'source':
            cfg['sources'] += rest
        elif key == 'include':
            cfg['includes'] += rest
        elif key == 'params':
            # params DIR: every parameter defined there (*.c, *.h, module.yaml);
            # params FILE NAME...: only the named parameters of that file (.c or module.yaml; a
            # name ending in '*' names every parameter with that prefix)
            if rest[0] == 'readonly':
                # the module's writes to the parameter store fail (param_set returns an error,
                # the value stays): px4_mavlink serves the stack's parameters read-only
                cfg['params_readonly'] = True
            else:
                # a file named twice is one entry (gen_params: the union of the lists)
                cfg['params'].append((rest[0], rest[1:]))
        elif key == 'params-of':
            # every parameter source of other harness modules (their px4.txt `params` lines)
            for other in rest:
                cfg['params'] += read_config(other)['params']
        elif key == 'pygen':
            # pygen DIR SCRIPT ARG...: one of PX4's own Python generators, run as its CMakeLists.txt
            # runs it (working directory $PX4_ROOT/DIR); {GEN} in an argument is build/gen/NAME
            cfg['pygen'].append((rest[0], rest[1:]))
        elif key == 'gensource':
            # gensource FILE...: generated sources (relative to build/gen/NAME), compiled by
            # px4_build.sh like the module's own
            cfg['gensources'] += rest
        elif key in ('sub', 'pub'):
            # TOPIC [INSTANCE] [slots N | mirror N [from MODULE]] [by]
            inst, slots, words = 0, None, rest[1:]
            if words[-1:] == ['by']:
                # one of several publishers of the topic: its ports are <topic>_by_<module>_...,
                # and a merge node (`merge` below) makes the one queue subscribers read
                cfg['by'].add((key, rest[0]))
                words = words[:-1]
            if words and words[0].isdigit():
                inst, words = int(words[0]), words[1:]
            if words[:1] == ['slots'] and len(words) == 2:
                slots, words = int(words[1]), []
            elif words[:1] == ['mirror'] and len(words) == 2:
                cfg['mirror'][(key, rest[0], inst)] = int(words[1])
                words = []
            elif words[:1] == ['mirror'] and len(words) == 4 and words[2] == 'from' and key == 'sub':
                # the subscriber names the module whose mirror it expects: an input
                # <topic>_mirror_by_<MODULE> (bool), fed by that module's output of the same name
                cfg['mirror'][(key, rest[0], inst)] = int(words[1])
                cfg.setdefault('mirror_from', {})[(rest[0], inst)] = words[3]
                words = []
            if words:
                sys.exit(f'px4_ports: {name}/px4.txt: {line}: expected TOPIC [INSTANCE] [slots N | mirror N]')
            cfg[key].append((rest[0], inst, slots))
        elif key == 'merge':
            # a merge node, not a PX4 module: TOPIC PUBLISHER... (see merge_main)
            cfg['merge'] = (rest[0], rest[1:])
        elif key == 'start':
            # another PX4 module run in the same process, started before the module: NAME ARGS...
            cfg['start'].append(rest)
        elif key == 'define':
            pass    # compile definitions, read by px4/build.sh
        elif key == 'run':
            # a command of a PX4 module run after the module started: NAME ARGS...
            cfg['run'].append(rest)
        elif key == 'stream':
            # a byte-stream device: NAME DEVICE WORDS (WORDS u32 words per step each way)
            cfg['stream'].append((rest[0], rest[1], int(rest[2])))
        elif key == 'process':
            if rest != ['fresh'] and rest != ['reuse']:
                sys.exit(f'px4_ports: {name}/px4.txt: process fresh|reuse')
            cfg['process'] = rest[0]
        else:
            sys.exit(f'px4_ports: {name}/px4.txt: unknown key {key}')
    return cfg


def named(param, names):
    """A parameter is named by its name or by a pattern ending in '*' (a prefix)."""
    return any(param == n or (n.endswith('*') and param.startswith(n[:-1])) for n in names)


def gen_params(name, cfg, gen):
    """PX4's parameter tools over the module's parameter sources: module.yaml through
    Tools/module_config/generate_params.py, then src/lib/parameters/px_process_params.py (which
    scans directories) and px_generate_params.py, as src/lib/parameters/CMakeLists.txt does. A file
    named with a list of parameters contributes only those."""
    import shutil
    import xml.etree.ElementTree as ET
    pdir = os.path.join(gen, 'parameters')
    shutil.rmtree(pdir, ignore_errors=True)
    os.makedirs(pdir)
    scan, keep_only = [], {}
    # one entry per source: a directory once, a file once with the union of its names (all of
    # them if any entry names none), and no file of a directory that is scanned whole
    dirs = {p for p, _ in cfg['params'] if os.path.isdir(os.path.join(PX4_ROOT, p))}
    files = {}
    for p, ns in cfg['params']:
        if p in dirs or os.path.dirname(p) in dirs:
            continue
        if p in files:
            files[p] = None if (files[p] is None or not ns) else sorted(set(files[p]) | set(ns))
        else:
            files[p] = list(ns) if ns else None
    entries = [(p, []) for p in sorted(dirs)] + [(p, ns or []) for p, ns in files.items()]
    for k, (path, names) in enumerate(entries):
        full = os.path.join(PX4_ROOT, path)
        d = os.path.join(pdir, f'src{k}')
        os.makedirs(d)
        if os.path.isdir(full):
            scan.append(full)
            yml = os.path.join(full, 'module.yaml')
            if os.path.exists(yml):
                # module.yaml and the module's other parameter yaml files (ekf2: params_*.yaml, which its
                # CMakeLists.txt adds to MODULE_CONFIG when the matching CONFIG_ option is on, as all are in
                # the px4_sitl default build)
                ymls = [yml] + sorted(os.path.join(full, f) for f in os.listdir(full)
                                      if f.startswith('params_') and f.endswith('.yaml'))
                subprocess.run([PY, os.path.join(PX4_ROOT, 'Tools/module_config/generate_params.py'),
                                '--params-file', os.path.join(d, 'module_params.c'),
                                '--config-files', *ymls, '--board', 'px4_sitl'],
                               check=True, stdout=subprocess.DEVNULL)
                scan.append(d)
        elif full.endswith('.yaml'):
            # a module.yaml file: its parameters through PX4's generator (only the named ones)
            subprocess.run([PY, os.path.join(PX4_ROOT, 'Tools/module_config/generate_params.py'),
                            '--params-file', os.path.join(d, 'module_params.c'),
                            '--config-files', full, '--board', 'px4_sitl'],
                           check=True, stdout=subprocess.DEVNULL)
            scan.append(d)
            if names:
                keep_only[os.path.join(d, 'module_params.c')] = set(names)
        else:
            shutil.copy(full, d)
            scan.append(d)
            if names:
                keep_only[os.path.join(d, os.path.basename(full))] = set(names)
    xml, js = os.path.join(pdir, 'parameters.xml'), os.path.join(pdir, 'parameters.json')
    subprocess.run([PY, os.path.join(PX4_ROOT, 'src/lib/parameters/px_process_params.py'),
                    '--src-path', *scan, '--xml', xml, '--json', js, '--board', 'px4_sitl'],
                   check=True, stdout=subprocess.DEVNULL)
    if keep_only:
        # drop the parameters of filtered files that were not named
        wanted = set().union(*keep_only.values())
        tree = ET.parse(xml)
        defined_in = {}
        for src, names in keep_only.items():
            txt = open(src).read()
            for m in re.finditer(r'PARAM_DEFINE_\w+\(\s*(\w+)', txt):
                defined_in.setdefault(m.group(1), []).append(set(names))
        for group in tree.getroot().iter('group'):
            for prm in list(group.findall('parameter')):
                n = prm.get('name')
                if n in defined_in and not any(named(n, ns) for ns in defined_in[n]):
                    group.remove(prm)
        tree.write(xml)
        have = [p.get('name') for p in tree.getroot().iter('parameter')]
        missing = {w for w in wanted if not any(named(h, {w}) for h in have)}
        if missing:
            sys.exit(f'px4_ports: {name}: parameters not found: {sorted(missing)}')
    subprocess.run([PY, os.path.join(PX4_ROOT, 'src/lib/parameters/px_generate_params.py'),
                    '--xml', xml, '--dest', pdir], check=True, stdout=subprocess.DEVNULL)
    # the parameters as the generated table has them (enum px4::params, sorted by name)
    ps = []
    for prm in ET.parse(xml).getroot().iter('parameter'):
        p = {'name': prm.get('name'), 'type': {'FLOAT': 'Float', 'INT32': 'Int32'}[prm.get('type')],
             'default': float(prm.get('default'))}
        for tag, key in (('short_desc', 'shortDesc'), ('min', 'min'), ('max', 'max')):
            e = prm.find(tag)
            if e is not None and e.text is not None:
                p[key] = e.text.strip() if key == 'shortDesc' else float(e.text)
        vals = [int(float(v.get('code'))) for v in prm.iter('value')]
        if prm.get('boolean') == 'true':
            vals = [0, 1]
        if vals and 'min' not in p and 'max' not in p:
            p['values'] = vals
        ps.append(p)
    return sorted(ps, key=lambda p: p['name'])


def lean_str(s):
    return s.replace('\\', '\\\\').replace('"', '\\"').replace('\n', ' ')


def fmt_float(x):
    r = repr(float(x))
    return r if ('e' in r or '.' in r) else r + '.0'


def merge_main(name, cfg, gen, paths, topic_msg):
    """A merge node (px4.txt `merge TOPIC PUBLISHER...`): not PX4 code, generic word copying. Its
    inputs are each publisher's slots of a queued topic (<topic>_by_<publisher>_..., the ports of
    `pub TOPIC by`), its output the one queue subscribers read (<topic>_...): every message of the
    step, publishers in the order listed, each publisher's in its own order, up to the topic's
    ORB_QUEUE_LENGTH; the rest are counted in <topic>_lost, as the uORB queue of a subscriber that
    reads once per step would drop them. Writes Ports.lean and build/gen/NAME/merge.cpp."""
    t, pubs = cfg['merge']
    mt = topic_msg[t]
    q = queue_length(paths, mt)
    leaves = flatten(paths, mt, t, 'm')
    sfx = [rec[len(t):] for rec, _, _ in leaves]
    ht = [BASIC[typ][0] for _, _, typ in leaves]
    def slot(prefix, k):
        return prefix if k == 0 else f'{prefix}_q{k}'
    ins = [('t_us', 'u32', 'hrt_absolute_time() this tick, us (low 32 bits)')]
    for p in pubs:
        pp = f'{t}_by_{p}'
        ins.append((f'{pp}_count', 'u32', f'messages {p} published on {t} this tick'))
        for k in range(q):
            ins += [(slot(pp, k) + x, y, f'{t} from {p}, slot {k}') for x, y in zip(sfx, ht)]
    outs = [(f'{t}_updated', 'bool', f'a message on {t} this tick'),
            (f'{t}_count', 'u32', f'messages on {t} this tick, all publishers ({q} slots)'),
            (f'{t}_lost', 'u32', f'messages on {t} this tick beyond the {q} slots')]
    for k in range(q):
        outs += [(slot(t, k) + x, y, f'{t}, slot {k}') for x, y in zip(sfx, ht)]
    ns = ''.join(w.capitalize() for w in name.split('_'))
    def schema(label, fields):
        rows = [f'  {{ name := "{n}", type := .{ty}, doc := "{lean_str(d)}" }}' for n, ty, d in fields]
        return f'def {label} : Schema := #[\n' + ',\n'.join(rows) + ']\n'
    L = [f'import Harness.Module\n\n/-! Ports of `{name}`, generated by `px4/ports.py {name}` from '
         f'px4/modules/{name}/px4.txt\nand PX4\'s .msg files. Do not edit. -/\n',
         f'namespace Px4.Modules.{ns}.Ports\n\nopen Harness Harness.Contract.Lang\n',
         'def params : Schema := #[]\n', schema('input', ins), schema('output', outs),
         '/-- The counts within the slots. -/',
         'def widths : List Clause := [\n' + ',\n'.join(
             f'  ⟨"slots_{t}_by_{p}_count", "{t}_by_{p}_count" ≤. ({q}.0 : Expr)⟩' for p in pubs) + ']\n',
         f'end Px4.Modules.{ns}.Ports\n']
    open(os.path.join(HARNESS, 'px4', 'modules', name, 'Ports.lean'), 'w').write('\n'.join(L))
    C = [f'// merge.cpp for {name}: generated by px4/ports.py from px4/modules/{name}/px4.txt. Do not edit.',
         '#include "module_protocol.h"\n', 'void module_init(const Params &) {}\n',
         'static void put(Output &out, unsigned k, const Input &in, unsigned p, unsigned j)\n{']
    for k in range(q):
        for pi, p in enumerate(pubs):
            for j in range(q):
                src = slot(f'{t}_by_{p}', j)
                C.append(f'    if (k == {k} && p == {pi} && j == {j}) {{ ' +
                         ' '.join(f'out.{slot(t, k)}{x} = in.{src}{x};' for x in sfx) + ' }')
    C.append('}\n')
    C.append('void module_step(const Input &in, Output &out)\n{\n    unsigned n = 0, total = 0;')
    for pi, p in enumerate(pubs):
        C.append(f'    for (unsigned j = 0; j < in.{t}_by_{p}_count && j < {q}; j++, total++) {{\n'
                 f'        if (n < {q}) {{ put(out, n++, in, {pi}, j); }}\n    }}')
    C.append(f'    out.{t}_updated = n > 0;\n    out.{t}_count = n;\n    out.{t}_lost = total - n;\n}}')
    open(os.path.join(gen, 'merge.cpp'), 'w').write('\n'.join(C) + '\n')
    print(f'px4_ports {name}: merge of {t} from {", ".join(pubs)}, {len(ins)} input fields, '
          f'{len(outs)} output fields')


def main():
    name = sys.argv[1]
    cfg = read_config(name)
    gen = os.path.join(HARNESS, 'build', 'gen', name)
    os.makedirs(gen, exist_ok=True)
    paths, topic_msg = msg_index()
    if cfg['merge']:
        return merge_main(name, cfg, gen, paths, topic_msg)

    for wd, cmd in cfg['pygen']:
        subprocess.run([PY] + [a.replace('{GEN}', gen) for a in cmd], cwd=os.path.join(PX4_ROOT, wd),
                       check=True, stdout=subprocess.DEVNULL)
    subs = {t for t, _, _ in cfg['sub']}
    both = subs & {t for t, _, _ in cfg['pub']}
    if both:
        sys.exit(f'px4_ports: {name}: topics both subscribed and published as ports: {sorted(both)} '
                 '(list each once; a module\'s own publications stay on its bus)')

    params = gen_params(name, cfg, gen)

    def topic_ports(t, inst, by=False):
        if t not in topic_msg:
            sys.exit(f'px4_ports: {name}: no .msg defines topic {t}')
        prefix = t if inst == 0 else f'{t}{inst}'
        if by:
            prefix = f'{prefix}_by_{name}'
        return prefix, topic_msg[t], flatten(paths, topic_msg[t], prefix, 'm')

    def note_of(typ):
        return {'uint64': ' (uint64 on the bus, low 32 bits)',
                'int64': ' (int64 on the bus, low 32 bits)',
                'float64': ' (float64 on the bus, as binary32)'}.get(typ, '')

    ins = [('t_us', 'u32', 'hrt_absolute_time() this tick, us (low 32 bits)')]
    outs = []
    ranges = []
    cpp_in, cpp_out, includes = [], [], set()
    queued_ranges = []
    # what the glue guarantees of the outputs: a field narrower in its C struct than its record
    # field carries a value of the C type (`out.F = (int32_t)m.f` with f an int8_t etc.), and a
    # queued topic's count is at most the slots copied (collect_queue / collect_tap stop there)
    out_ranges = []
    out_slots = []
    pairs = []      # float64 input fields carried as <rec>, <rec>_lo
    taps, cpp_in_last = [], []
    for kind, lst in (('sub', cfg['sub']), ('pub', cfg['pub'])):
        for t, inst, slots in lst:
            prefix, mt, leaves = topic_ports(t, inst, (kind, t) in cfg['by'])
            sname = snake(mt)
            includes.add(sname)
            fl = ins if kind == 'sub' else outs
            qlen = queue_length(paths, mt)
            if (kind, t, inst) in cfg['mirror']:
                # a mirror port: every message written in a step, whole, as the bytes of its uORB
                # struct packed in u32 words (msg_words per message): <p>_mirror_count messages
                # in <p>_mirror_0.., and on an output <p>_mirror_lost beyond the slots. Output:
                # a tap on the bus. Input: published one at a time, the module run to rest after
                # each, so a consumer with a queue of one sees every message.
                n = cfg['mirror'][(kind, t, inst)]
                size = sum(MSG_SIZE[typ] for _, _, typ in leaves)
                size = (size + 7) // 8 * 8
                w = size // 4
                fl.append((f'{prefix}_mirror_count', 'u32',
                           f'messages on {t} mirrored this tick (at most {n}, {w} words each)'))
                if kind == 'pub':
                    fl.append((f'{prefix}_mirror_lost', 'u32',
                               f'messages written on {t} this tick beyond the {n} mirrored'))
                    # the mark of the port's source: true at every tick (set below), so that a
                    # subscriber can tell this module's mirror from generated words
                    fl.append((f'{prefix}_mirror_by_{name}', 'bool',
                               f'the mirrored {t} messages are every message written on {t} in '
                               f'{name}, whole and in order (always true)'))
                    taps.append((t, inst, n))
                else:
                    queued_ranges.append((f'{prefix}_mirror_count', (0, n)))
                    src = cfg.get('mirror_from', {}).get((t, inst))
                    if src:
                        fl.append((f'{prefix}_mirror_by_{src}', 'bool',
                                   f'the mirrored {t} messages are {src}\'s mirror (its mark)'))
                fl += [(f'{prefix}_mirror_{i}', 'u32', f'{t} message {i // w}, word {i % w}')
                       for i in range(n * w)]
                words_ = ', '.join(f'in.{prefix}_mirror_{i}' for i in range(n * w)) if kind == 'sub' else ''
                if kind == 'sub':
                    cpp_in_last.append(
                        f'    {{\n        static_assert(sizeof({sname}_s) <= {4 * w}, "mirror words");\n'
                        f'        const uint32_t buf[{n * w}] = {{{words_}}};\n'
                        f'        for (uint32_t k = 0; k < in.{prefix}_mirror_count && k < {n}; k++) {{\n'
                        f'            {sname}_s m{{}};\n            memcpy(&m, buf + k * {w}, sizeof m);\n'
                        f'            px4_shim::inject(ORB_ID({t}), {inst}, &m);\n'
                        f'            px4_shim::run_all();\n        }}\n    }}')
                else:
                    cpp_out.append(
                        f'    {{\n    static_assert(sizeof({sname}_s) <= {4 * w}, "mirror words");\n'
                        f'    static {sname}_s m[{n}];\n    static uint32_t buf[{n * w}];\n'
                        f'    unsigned n = 0, lost = 0;\n'
                        f'    px4_shim::collect_tap(ORB_ID({t}), {inst}, m, sizeof m[0], {n}, &n, &lost);\n'
                        f'    memset(buf, 0, sizeof buf);\n'
                        f'    for (unsigned k = 0; k < n; k++) {{ memcpy(buf + k * {w}, &m[k], sizeof m[k]); }}\n'
                        f'    out.{prefix}_mirror_count = n;\n    out.{prefix}_mirror_lost = lost;\n'
                        f'    out.{prefix}_mirror_by_{name} = true;\n' +
                        '\n'.join(f'    out.{prefix}_mirror_{i} = buf[{i}];' for i in range(n * w)) + '\n    }')
                continue
            if qlen > 1 or (slots is not None and slots > 1):
                n = qlen if slots is None else slots
                if n < 1:
                    sys.exit(f'px4_ports: {name}: {t}: slots {n} < 1')
                # more slots than the topic's queue: a mirror. Output: every message written this
                # step (a tap, bus.cpp), not only the queue's newest. Input: the slots are
                # published one at a time, the module running to rest after each, so that a
                # consumer with a queue of qlen sees every one.
                mirror = n > qlen
                if mirror and kind == 'pub':
                    taps.append((t, inst, n))
                # a queued topic: n slots, a count, and (output) the messages lost
                if kind == 'pub':
                    fl.append((f'{prefix}_updated', 'bool', f'the module published on {t} this tick'))
                fl.append((f'{prefix}_count', 'u32',
                           f'messages on {t} (instance {inst}) this tick, in slots 0..count-1 '
                           f'({n} slots, ORB_QUEUE_LENGTH {qlen})'))
                if kind == 'pub':
                    fl.append((f'{prefix}_lost', 'u32',
                               f'messages published on {t} this tick beyond the {n} newest'))
                    out_slots.append((f'{prefix}_count', n))
                else:
                    queued_ranges.append((f'{prefix}_count', (0, n)))
                inj, col = [], []
                for k in range(n):
                    sp = prefix if k == 0 else f'{prefix}_q{k}'
                    body = []
                    for rec, cp, typ in leaves:
                        r = sp + rec[len(prefix):]
                        ht, ct, rng = BASIC[typ]
                        fl.append((r, ht, f'{t}.{cp[2:]} (slot {k}): {typ}{note_of(typ)}'))
                        if kind == 'sub':
                            if rng is not None:
                                ranges.append((r, rng))
                            body.append(f'        {cp} = ({ct})in.{r};')
                        else:
                            if rng is not None:
                                out_ranges.append((r, rng))
                            cast = {'f32': 'float', 'i32': 'int32_t', 'u32': 'uint32_t', 'bool': 'bool'}[ht]
                            col.append(f'    out.{r} = ({cast})m[{k}]{cp[1:]};')
                    if kind == 'sub':
                        inj.append(f'    if (in.{prefix}_count > {k}) {{\n        {sname}_s m{{}};\n' +
                                   '\n'.join(body) +
                                   f'\n        px4_shim::inject(ORB_ID({t}), {inst}, &m);\n    }}')
                if kind == 'sub':
                    if mirror:
                        cpp_in_last.extend(i.replace('&m);\n    }', '&m);\n        px4_shim::run_all();\n    }')
                                           for i in inj)
                    else:
                        cpp_in += inj
                else:
                    fn = 'collect_tap' if mirror else 'collect_queue'
                    cpp_out.append(f'    {{\n    static {sname}_s m[{n}];\n    unsigned n = 0, lost = 0;\n'
                                   f'    px4_shim::{fn}(ORB_ID({t}), {inst}, m, sizeof m[0], {n}, '
                                   f'&n, &lost);\n    out.{prefix}_updated = n > 0;\n'
                                   f'    out.{prefix}_count = n;\n    out.{prefix}_lost = lost;\n' +
                                   '\n'.join(col) + '\n    }')
                continue
            if slots is not None:
                sys.exit(f'px4_ports: {name}: {t} is not a queued topic; `slots` does not apply')
            what = 'a message was published on' if kind == 'sub' else 'the module published on'
            fl.append((f'{prefix}_updated', 'bool', f'{what} {t} (instance {inst}) this tick'))
            body = []
            for rec, cp, typ in leaves:
                ht, ct, rng = BASIC[typ]
                if typ == 'float64':
                    # two binary32 fields: the value rounded, and the rest (hi + lo carries 48 bits)
                    fl.append((rec, 'f32', f'{t}.{cp[2:]}: float64 on the bus, rounded to binary32'))
                    fl.append((f'{rec}_lo', 'f32', f'{t}.{cp[2:]}: float64 on the bus, minus {rec}'))
                    if kind == 'sub':
                        pairs.append(rec)
                        body.append(f'        {cp} = (double)in.{rec} + (double)in.{rec}_lo;')
                    else:
                        body.append(f'    out.{rec} = (float){cp};')
                        # the rest of a non-finite value is 0 (NaN - NaN would be NaN)
                        body.append(f'    out.{rec}_lo = __builtin_isfinite(out.{rec}) ? '
                                    f'(float)({cp} - (double)out.{rec}) : 0.f;')
                    continue
                fl.append((rec, ht, f'{t}.{cp[2:]}: {typ}{note_of(typ)}'))
                if kind == 'sub':
                    if rng is not None:
                        ranges.append((rec, rng))
                    body.append(f'        {cp} = ({ct})in.{rec};')
                else:
                    if rng is not None:
                        out_ranges.append((rec, rng))
                    cast = {'f32': 'float', 'i32': 'int32_t', 'u32': 'uint32_t', 'bool': 'bool'}[ht]
                    body.append(f'    out.{rec} = ({cast}){cp};')
            if kind == 'sub':
                cpp_in.append(f'    if (in.{prefix}_updated) {{\n        {sname}_s m{{}};\n' +
                              '\n'.join(body) +
                              f'\n        px4_shim::inject(ORB_ID({t}), {inst}, &m);\n    }}')
            else:
                cpp_out.append(f'    {{\n    {sname}_s m{{}};\n    out.{prefix}_updated = '
                               f'px4_shim::collect(ORB_ID({t}), {inst}, &m, sizeof m);\n' +
                               '\n'.join(body) + '\n    }')
    for sname_, dev, words in cfg['stream']:
        p_ = sname_
        ins.append((f'{p_}_rx_len', 'u32', f'bytes received on {dev} this tick, packed in {p_}_rx_* (at most {4 * words})'))
        ins += [(f'{p_}_rx_{i}', 'u32', f'received bytes {4 * i}-{4 * i + 3}, little-endian') for i in range(words)]
        queued_ranges.append((f'{p_}_rx_len', (0, 4 * words)))
        outs.append((f'{p_}_tx_len', 'u32', f'bytes the module wrote to {dev}, sent this tick in {p_}_tx_*'))
        outs += [(f'{p_}_tx_{i}', 'u32', f'sent bytes {4 * i}-{4 * i + 3}, little-endian') for i in range(words)]
        outs.append((f'{p_}_tx_pending', 'u32', f'bytes left in the transmit buffer of {dev} after this tick'))
        outs.append((f'{p_}_rx_dropped', 'u32', f'bytes dropped on a full receive buffer of {dev} since init'))
        cpp_in.append(f'    {{\n        const uint32_t w[{words}] = {{' + ', '.join(f'in.{p_}_rx_{i}' for i in range(words)) +
                      f'}};\n        px4_shim::stream_inject("{dev}", w, in.{p_}_rx_len, {words});\n    }}')
        cpp_out.append(f'    {{\n    uint32_t w[{words}], n, pending, dropped;\n    px4_shim::stream_collect("{dev}", w, {words}, '
                       f'&n, &pending, &dropped);\n    out.{p_}_tx_len = n;\n    out.{p_}_tx_pending = pending;\n'
                       f'    out.{p_}_rx_dropped = dropped;\n' +
                       '\n'.join(f'    out.{p_}_tx_{i} = w[{i}];' for i in range(words)) + '\n    }')
    cpp_in += cpp_in_last    # mirrored inputs last: each slot runs the module to rest
    # named after the module, so that composed modules do not clash on it
    outs.append((f'{name}_errors', 'u32', 'PX4_ERR / PX4_PANIC messages logged since init (shim count)'))

    # ---- Lean
    ns = ''.join(w.capitalize() for w in name.split('_'))
    L = []
    L.append(f'import Harness.Module\n\n/-! Ports of `{name}`, generated by `px4/ports.py {name}` from '
             f'px4/modules/{name}/px4.txt,\nPX4\'s .msg files and its parameter definitions. Do not edit. -/\n')
    L.append(f'namespace Px4.Modules.{ns}.Ports\n\nopen Harness Harness.Contract.Lang\n')

    def schema(label, fields):
        rows = [f'  {{ name := "{n}", type := .{t}, doc := "{lean_str(d)}" }}' for n, t, d in fields]
        # chunks of 300: one long array literal exceeds Lean's elaboration depth
        chunks = [',\n'.join(rows[i:i + 300]) for i in range(0, len(rows), 300)] or ['']
        opt = 'set_option maxRecDepth 100000 in\n' if len(rows) > 1000 else ''
        return f'{opt}def {label} : Schema :=\n  #[\n' + ']\n  ++ #[\n'.join(chunks) + ']\n'

    pf = []
    for p in params:
        t = 'f32' if p['type'] == 'Float' else 'i32'
        d = f"{p.get('shortDesc', '')} (default {p['default']}"
        if 'min' in p or 'max' in p:
            d += f", range [{p.get('min', '')}, {p.get('max', '')}]"
        if 'values' in p:
            d += f", values {p['values']}"
        d += ')'
        pf.append((p['name'], t, d))
    L.append(schema('params', pf))
    L.append(schema('input', ins))
    L.append(schema('output', outs))

    def lit(x):
        x = float(x)
        return f'({fmt_float(x)} : Expr)' if x >= 0 else f'(-{fmt_float(-x)} : Expr)'

    L.append('/-- The domains PX4 documents for the parameters: `min` and `max`, or the listed values of an\n'
             'enumeration or a Boolean. -/')
    cl = []
    for p in params:
        if 'values' in p:
            alts = ' ∨. '.join(f'"{p["name"]}" =. {lit(v)}' for v in p['values'])
            cl.append(f'  ⟨"range_{p["name"]}", {alts}⟩')
            continue
        parts = []
        if 'min' in p:
            parts.append(f'{lit(p["min"])} ≤. "{p["name"]}"')
        if 'max' in p:
            parts.append(f'"{p["name"]}" ≤. {lit(p["max"])}')
        if parts:
            cl.append(f'  ⟨"range_{p["name"]}", ' + ' ∧. '.join(parts) + '⟩')
    L.append('def paramRanges : List Clause := [\n' + ',\n'.join(cl) + ']\n')
    L.append('/-- The default value of every parameter, as clauses (the stock configuration). -/')
    dl = [f'  ⟨"default_{p["name"]}", "{p["name"]}" =. {lit(p["default"])}⟩' for p in params]
    L.append('def paramDefaults : List Clause := [\n' + ',\n'.join(dl) + ']\n')
    L.append('/-- Input fields narrower on the bus than their record field carry values in range, and the\n'
             'second field of a float64 pair is the rest of the first. -/')
    rl = [f'  ⟨"width_{r}", {lit(lo)} ≤. "{r}" ∧. "{r}" ≤. {lit(hi)}⟩' for r, (lo, hi) in ranges]
    rl += [f'  ⟨"slots_{r}", "{r}" ≤. {lit(hi)}⟩' for r, (lo, hi) in queued_ranges]
    # a float64 pair: the rest is small. Exactly it is at most half an ulp of the rounded value
    # (2^-24 relative); stated as the single-field bound |rest| <= 1e-3, which every rounding of a
    # value below 1.6e4 satisfies (half an ulp of 16384 is 9.8e-4) and which a campaign's sampler
    # meets field by field (a two-field relation it meets only by rejection). A non-finite value is
    # published as (value, 0), so every generated publisher meets it.
    rl += [f'  ⟨"pair_{r}", abs "{r}_lo" ≤. (0.001 : Expr)⟩' for r in pairs]
    L.append('def widths : List Clause := [\n' + ',\n'.join(rl) + ']\n')
    L.append('/-- Output fields narrower in the C struct than their record field carry values of the C\n'
             'type (the glue copies them with a cast), and a queued topic\'s count is at most its slots\n'
             '(the glue copies at most that many): facts of the generated px4_ports.cpp. -/')
    ol = [f'  ⟨"width_{r}", {lit(lo)} ≤. "{r}" ∧. "{r}" ≤. {lit(hi)}⟩' for r, (lo, hi) in out_ranges]
    ol += [f'  ⟨"slots_{r}", "{r}" ≤. {lit(n)}⟩' for r, n in out_slots]
    L.append('def outWidths : List Clause := [\n' + ',\n'.join(ol) + ']\n')
    L.append(f'end Px4.Modules.{ns}.Ports\n')
    with open(os.path.join(HARNESS, 'px4', 'modules', name, 'Ports.lean'), 'w') as f:
        f.write('\n'.join(L))

    # ---- C++
    argv = [cfg['main'], 'start'] + cfg['args']
    C = []
    C.append(f'// px4_ports.cpp for module {name}: generated by px4/ports.py from px4/modules/{name}/px4.txt,\n'
             '// PX4\'s .msg files and parameter definitions. Do not edit.\n')
    C.append('#include "px4_shim.h"\n#include "module_records.h"')
    for s in sorted(includes):
        C.append(f'#include <uORB/topics/{s}.h>')
    C.append(f'\nextern "C" int {cfg["main"]}_main(int argc, char *argv[]);\n')
    C.append('int px4_ports_main(int argc, char *argv[])\n{\n'
             f'    return {cfg["main"]}_main(argc, argv);\n}}\n')
    C.append('extern const char *const px4_ports_start_argv[] = {' +
             ', '.join(f'"{a}"' for a in argv) + ', nullptr};')
    C.append(f'extern const int px4_ports_start_argc = {len(argv)};')
    C.append(f'extern const bool px4_ports_fresh_process = {"true" if cfg["process"] == "fresh" else "false"};\n')
    others = cfg['start']
    for o in sorted(({o[0] for o in others} | {r[0] for r in cfg['run']}) - {cfg['main']}):
        C.append(f'extern "C" int {o}_main(int argc, char *argv[]);')
    C.append('void px4_ports_start_others()\n{')
    for sname_, dev, words in cfg['stream']:
        C.append(f'    px4_shim::stream_register("{dev}");')
    for t, inst, n in taps:
        C.append(f'    px4_shim::tap(ORB_ID({t}), {inst}, {n});')
    for o in others:
        av = [o[0], 'start'] + o[1:]
        C.append(f'    {{ const char *a[] = {{' + ', '.join(f'"{x}"' for x in av) +
                 f', nullptr}}; {o[0]}_main({len(av)}, const_cast<char **>(a)); }}')
    C.append('}\n')
    C.append('void px4_ports_after_start()\n{')
    for o in cfg['run']:
        av = list(o)
        C.append(f'    {{ const char *a[] = {{' + ', '.join(f'"{x}"' for x in av) +
                 f', nullptr}}; {o[0]}_main({len(av)}, const_cast<char **>(a)); }}')
    C.append('}\n')
    C.append('void px4_ports_stop_others()\n{')
    for o in reversed(others):
        C.append(f'    {{ const char *a[] = {{"{o[0]}", "stop", nullptr}}; {o[0]}_main(2, const_cast<char **>(a)); }}')
    C.append('}\n')
    C.append('void px4_ports_params(const Params &p)\n{')
    for p in params:
        v = 'float' if p['type'] == 'Float' else 'int32_t'
        C.append(f'    {{ const {v} v = p.{p["name"]}; px4_shim::param_store(px4::params::{p["name"]}, &v); }}')
    if cfg['params_readonly']:
        C.append('    px4_shim::params_readonly();')
    C.append('}\n')
    C.append('void px4_ports_inject(const Input &in)\n{\n' + '\n'.join(cpp_in) + '\n}\n')
    C.append('void px4_ports_collect(Output &out)\n{\n' + '\n'.join(cpp_out) +
             f'\n    out.{name}_errors = px4_shim::error_count();\n}}\n')
    with open(os.path.join(gen, 'px4_ports.cpp'), 'w') as f:
        f.write('\n'.join(C))

    print(f'px4_ports {name}: {len(params)} parameters, {len(ins)} input fields '
          f'({len(cfg["sub"])} topics), {len(outs)} output fields ({len(cfg["pub"])} topics)')


if __name__ == '__main__':
    main()
