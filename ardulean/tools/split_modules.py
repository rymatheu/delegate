#!/usr/bin/env python3
"""Split one generated Lean file (Vehicle_lib.lean or Estimator_lib.lean) into modules laid out after ArduPilot's tree.

    split_modules.py SOURCE.lean --namespace NS --ardupilot AP_TREE --root REPO --out-dir ArduLean/Vehicle
                     --module-prefix ArduLean.Vehicle (--deps DEPS.tsv | --deps-index INDEX.json) [options]

SOURCE is the monolithic file as generated (`namespace NS ... end NS` after a header of imports, a module doc comment
and `open`/`set_option` lines). Its body is cut into top-level items: a declaration with the doc comments, `--`
comments and `set_option ... in` lines before it and the blank lines after it; a `mutual ... end` block and a nested
`namespace X ... end X` block are one item each. Every item's text is kept byte for byte, items keep their relative
order inside a module, and every module repeats the source's `open` and `set_option` lines and its namespace.

Dependencies between items: the constants each constant uses, as Lean records them (`DEPS.tsv`, written by
tools/dump_deps.lean from the .olean of SOURCE before the split; or the item graph recorded in a previous INDEX.json),
united with a scan of the item's identifiers. A dependency on a shared auxiliary matcher (`f.match_1` that Lean reuses
for an identical `match` elsewhere) is not one: Lean creates the matcher anew where the first is absent.

Placement:
 1. Each item gets an ArduPilot folder (`ArduCopter`, `libraries/<Lib>`, `mavlink`) from the source file its doc
    comment cites, from its C++ class (the folder most of the class's cited functions are in; a citation of a header
    outside that folder is clang's macro or template location and loses to the class), from its base function
    (`f.pure'`, `f.body`, `f'rec` go with `f`), from a definition of the same name in the ArduPilot tree, or from its
    first user. Generated items without a C++ origin go to plainly named modules: Layout (addresses, the image, the
    memory's initial state), Dispatch (function-pointer calls), World (the boundary's text outputs), Startup (static
    construction).
 2. ArduPilot's libraries call each other in cycles, so a folder cannot be one module. The folders are put in a linear
    order (a local search that minimizes the number of modules) and placed in passes: an item goes to the first pass
    in which all its dependencies are placed, in the module (pass, folder). Small modules are then emptied into
    another module of the same folder where all their dependencies and users allow it.
 3. The top of the call graph (the passes from --top-pass on) is merged into a few cross-library modules, cut at the
    passes of the anchor declarations (--anchor NAME=DECL): mode switching, arming, GCS message handling, the
    scheduler loop.
 4. A module of more than --max-lines lines is split by ArduPilot source file.
Every inter-module dependency goes from a later module to an earlier one in the linear order, so the import graph is
acyclic; each module imports exactly the modules (and runtime modules) its items use.

Outputs: the modules under OUT_DIR, the umbrella module OUT_DIR.lean (imports them all), OUT_DIR/INDEX.json (for each
item in source order its module and line count, the item graph, the source's SHA-256 and header; tools/check_split.py
rebuilds the source from it) and OUT_DIR/INDEX.md (ArduPilot source file to Lean modules). Deterministic.
"""
import argparse, collections, hashlib, json, os, re, sys
from pathlib import Path

# ----------------------------------------------------------------------------------------------------------------------
# parsing

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"
                  r"(def|abbrev|theorem|structure|inductive|class|instance|opaque|axiom|mutual|namespace)\b")
TRIVIA = re.compile(r"^(/-|--|set_option\s.*\sin\s*$|@\[)")


def comment_depth_after(line, depth):
    """The block-comment depth after `line`, starting at `depth` (block comments nest; strings and `--` respected)."""
    i, n, instr = 0, len(line), False
    while i < n:
        if depth > 0:
            if line.startswith("/-", i): depth += 1; i += 2; continue
            if line.startswith("-/", i): depth -= 1; i += 2; continue
            i += 1; continue
        c = line[i]
        if instr:
            if c == "\\": i += 2; continue
            if c == '"': instr = False
            i += 1; continue
        if c == '"': instr = True; i += 1; continue
        if line.startswith("--", i): break
        if line.startswith("/-", i): depth += 1; i += 2; continue
        i += 1
    return depth


def parse(text, ns):
    """Cut the body of `namespace ns` into items. Returns (lines, items, first, endl); item = dict(a, b, decl, kind)
    with lines[a:b] its text; lines[first:endl] is the body."""
    lines = text.split("\n")
    nsl = [i for i, l in enumerate(lines) if l == f"namespace {ns}"]
    assert len(nsl) == 1, "exactly one `namespace NS` line"
    nsl = nsl[0]
    endl = max(i for i, l in enumerate(lines) if l == f"end {ns}")
    depth, d0 = 0, []
    for l in lines:
        d0.append(depth); depth = comment_depth_after(l, depth)
    items, pending, i = [], None, nsl + 1
    while i < endl:
        l = lines[i]
        if not l or l[0] in " \t" or d0[i] > 0:
            i += 1; continue
        m = DECL.match(l)
        if m:
            kind = m.group(1)
            if kind == "mutual":
                e = next(k for k in range(i + 1, endl) if lines[k] == "end") + 1
            elif kind == "namespace":
                e = next(k for k in range(i + 1, endl) if lines[k] == f"end {l.split()[1]}") + 1
            else:
                e = i + 1
            items.append(dict(a=pending if pending is not None else i, decl=i, kind=kind))
            pending = None; i = e; continue
        if TRIVIA.match(l):
            if pending is None: pending = i
            if l.startswith("/-"):
                k = i
                while comment_depth_after(lines[k], d0[k]) > 0: k += 1
                i = k + 1; continue
            i += 1; continue
        assert pending is None, f"line {i + 1}: a continuation line after a comment: {l!r}"
        i += 1
    assert pending is None
    for k, it in enumerate(items):
        it["b"] = items[k + 1]["a"] if k + 1 < len(items) else endl
    first = items[0]["a"]
    assert all(not lines[j] for j in range(nsl + 1, first)), "only blank lines between `namespace` and the first item"
    return lines, items, first, endl


DEFNAME = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
                     r"(?:def|abbrev|theorem|structure|inductive|class|opaque)\s+([^\s:(\[{]+)")


def decl_name(lines, it):
    """The item's (first) declared name, relative to the file's namespace."""
    if it["kind"] == "namespace":
        base = lines[it["decl"]].split()[1]
        for j in range(it["decl"] + 1, it["b"]):
            m = DEFNAME.match(lines[j])
            if m: return base + "." + m.group(1)
        return base
    if it["kind"] == "mutual":
        for j in range(it["decl"] + 1, it["b"]):
            m = DEFNAME.match(lines[j])
            if m: return m.group(1)
    m = DEFNAME.match(lines[it["decl"]])
    return m.group(1) if m else None

# ----------------------------------------------------------------------------------------------------------------------
# dependencies

AUX_SHARED = re.compile(r"\.(match_\d+|_sparseCasesOn_\d+|proof_\d+|_proof_\d+)$")


def read_deps_tsv(path, items, ns):
    """Item graph from tools/dump_deps.lean's output. Returns (deps, other_modules, names, clients, foreign) where
    names[k] are the constants declared in item k (with a declaration range), other_modules[k] the other project
    modules item k uses, clients[c] the constants of this file that client module c uses, foreign[k] the constants
    of other project modules that item k uses (by name)."""
    import bisect
    starts = [it["a"] for it in items]
    rows, clients = [], {}
    for l in open(path):
        l = l.rstrip("\n")
        if l.startswith("@client "):
            c, _, us = l[len("@client "):].partition("\t")
            clients[c] = us.split() if us else []
            continue
        r = l.split("\t")
        while len(r) < 5: r.append("")
        rows.append(r)
    line = {r[0]: int(r[1]) for r in rows if r[1] != "-"}
    def owner(n):
        p = n
        while p not in line and "." in p: p = p.rsplit(".", 1)[0]
        return bisect.bisect_right(starts, line[p] - 1) - 1 if p in line else None
    own = {r[0]: owner(r[0]) for r in rows}
    missing = sorted(n for n, o in own.items() if o is None)
    assert not missing, f"constants without an item: {missing[:5]}"
    deps = [set() for _ in items]; other = [set() for _ in items]; names = [set() for _ in items]
    foreign = [set() for _ in items]
    for r in rows:
        o = own[r[0]]
        if r[1] != "-": names[o].add(r[0][len(ns) + 1:])
        for u in r[2].split():
            ou = own.get(u)
            if ou is not None and ou != o and not AUX_SHARED.search(u): deps[o].add(ou)
        for m in r[3].split(): other[o].add(m)
        for u in r[4].split(): foreign[o].add(u)
    return deps, other, names, clients, foreign


TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*")


def strip_comments_strings(t):
    t = re.sub(r"/-.*?-/", " ", t, flags=re.S)
    t = re.sub(r"--[^\n]*", " ", t)
    return re.sub(r'"(?:\\.|[^"\\])*"', " ", t)


def token_deps(lines, items, names, ns):
    """Earlier items named by an identifier of the item (the longest prefix of a dotted identifier that is a name)."""
    name2item = {}
    for k, ns_ in enumerate(names):
        for n in sorted(ns_): name2item.setdefault(n, k)
    deps = [set() for _ in items]
    for k, it in enumerate(items):
        for t in set(TOKEN.findall(strip_comments_strings("\n".join(lines[it["a"]:it["b"]])))):
            if t.startswith("_root_."): t = t[7:]
            if t.startswith(ns + "."): t = t[len(ns) + 1:]
            parts = t.split(".")
            for m in range(len(parts), 0, -1):
                j = name2item.get(".".join(parts[:m]))
                if j is not None:
                    if j < k: deps[k].add(j)
                    break
    return deps

# ----------------------------------------------------------------------------------------------------------------------
# classification: the ArduPilot folder and source file of each item

CITE = re.compile(r"`((?:[A-Za-z0-9_]+/)*)([A-Za-z0-9_]+\.(?:cpp|h|hpp|c|inc)):(?:\d+|\?)(?:-(?:\d+|\?))?`")
HAL_FILES = {"Storage.cpp", "Semaphores.h", "Util.cpp", "Scheduler.cpp", "system.cpp"}
VARIANT = re.compile(r"(\.pure'|\.body'rec|\.body|'rec)+$")
MAVLINK_NAME = re.compile(r"^(mavlink_|_mav_|_mavlink_|crc_|__mavlink_|MAVLINK_|MAV_)")


def base_name(n): return VARIANT.sub("", n)


def class_of(n):
    if not n or "." not in n: return None
    return n.split(".")[0].split("'")[0]


def ap_index(ap):
    idx = collections.defaultdict(list)
    for top in ("ArduCopter", "libraries", "modules/mavlink"):
        for dp, dn, fn in os.walk(Path(ap) / top):
            dn[:] = sorted(d for d in dn if d not in (".git", "examples", "tests", "benchmarks"))
            for f in sorted(fn):
                if f.endswith((".cpp", ".h", ".hpp", ".c", ".inc")):
                    idx[f].append(os.path.relpath(os.path.join(dp, f), ap))
    return idx


def folder_of_path(rel):
    p = rel.split("/")
    return "libraries/" + p[1] if p[0] == "libraries" else ("ArduCopter" if p[0] == "ArduCopter" else "mavlink")


def free_definitions(ap, wanted):
    """For each wanted free-function name, the ArduPilot files with a line that defines it."""
    if not wanted: return {}
    rx = re.compile(r"^[A-Za-z_][\w:<>,\*&\s]*?[\s\*&](" + "|".join(sorted(map(re.escape, wanted), key=len, reverse=True))
                    + r")\s*\([^;]*$")
    hits = collections.defaultdict(list)
    for top in ("libraries", "ArduCopter"):
        for dp, dn, fn in os.walk(Path(ap) / top):
            dn[:] = sorted(d for d in dn if d not in (".git", "examples", "tests")
                           and (not d.startswith("AP_HAL_") or d == "AP_HAL_SITL"))
            for f in sorted(fn):
                if not f.endswith((".cpp", ".h", ".c")): continue
                p = os.path.join(dp, f)
                for line in open(p, errors="replace").read().split("\n"):
                    if "(" in line:
                        m = rx.match(line)
                        if m: hits[m.group(1)].append(os.path.relpath(p, ap))
    return hits


def type_definitions(ap, wanted):
    """For each wanted type name, the ArduPilot files that define it (`enum`, `enum class`, `struct`, `class`, `union`,
    with or without `typedef`), declarations without a body (`class X;`) apart."""
    if not wanted: return {}
    rx = re.compile(r"^\s*(?:typedef\s+)?(?:enum|struct|class|union)\s+(?:class\s+|struct\s+)?("
                    + "|".join(sorted(map(re.escape, wanted), key=len, reverse=True))
                    + r")\s*(?::\s*(?:public\s+)?[\w:<>, ]+)?\s*(?:\{.*)?$")
    hits = collections.defaultdict(list)
    for top in ("libraries", "ArduCopter"):
        for dp, dn, fn in os.walk(Path(ap) / top):
            dn[:] = sorted(d for d in dn if d not in (".git", "examples", "tests")
                           and (not d.startswith("AP_HAL_") or d == "AP_HAL_SITL"))
            for f in sorted(fn):
                if not f.endswith((".cpp", ".h")): continue
                p = os.path.join(dp, f)
                for line in open(p, errors="replace").read().split("\n"):
                    m = rx.match(line)
                    if m: hits[m.group(1)].append(os.path.relpath(p, ap))
    return hits


def classify(lines, items, nm, deps, ap, generated):
    """(folder, ArduPilot path or source basename or None, rule) for each item."""
    idx = ap_index(ap)
    n = len(items)
    cites = []
    for it in items:
        end = it["b"] if it["kind"] == "namespace" else it["decl"] + 1
        m = CITE.search("\n".join(lines[it["a"]:end]))
        cites.append((m.group(1), m.group(2)) if m else None)
    def cite_paths(c):
        d, b = c
        if b.startswith("mavlink") or b in ("checksum.h", "protocol.h"): return ["mavlink"], [b]
        ps = [x for x in idx.get(b, []) if x.endswith("/" + d + b)]
        return sorted(set(map(folder_of_path, ps))), ps
    votes = collections.defaultdict(collections.Counter); fvotes = collections.defaultdict(collections.Counter)
    for k, c in enumerate(cites):
        cl = class_of(nm[k])
        if c and cl:
            fs, ps = cite_paths(c)
            if len(fs) == 1:
                votes[cl][fs[0]] += 2 if c[1].endswith((".cpp", ".c")) else 1
                fvotes[(cl, fs[0])][ps[0] if ps else c[1]] += 1
    def class_home(cl):
        if not cl: return None
        if cl in votes:
            f = sorted(votes[cl].items(), key=lambda x: (-x[1], x[0]))[0][0]
            return f, sorted(fvotes[(cl, f)].items(), key=lambda x: (-x[1], x[0]))[0][0]
        for ext in (".h", ".cpp"):
            ps = idx.get(cl + ext)
            if ps and len(set(map(folder_of_path, ps))) == 1: return folder_of_path(ps[0]), ps[0]
        if MAVLINK_NAME.match(cl): return "mavlink", None
        return None
    home = [None] * n
    for k in range(n):
        c = cites[k]
        if not c: continue
        ch = class_home(class_of(base_name(nm[k] or "")))
        fs, ps = cite_paths(c)
        path = ps[0] if len(fs) == 1 and ps else c[1]
        if len(fs) == 1:
            if ch and ch[0] != fs[0] and not c[1].endswith((".cpp", ".c")): home[k] = (ch[0], ch[1], "class")
            else: home[k] = (fs[0], path, "cite")
        elif ch and ch[0] in fs: home[k] = (ch[0], [p for p in ps if folder_of_path(p) == ch[0]][0], "cite+class")
        elif c[1] in HAL_FILES and "libraries/AP_HAL" in fs:
            home[k] = ("libraries/AP_HAL", [p for p in ps if folder_of_path(p) == "libraries/AP_HAL"][0], "cite")
        elif ch: home[k] = (ch[0], ch[1], "class")
    # the variants of a function (f, f.body, f.pure', f'rec, ...) share the home of the cited one
    fam = collections.defaultdict(list)
    for k in range(n):
        if nm[k]: fam[base_name(nm[k])].append(k)
    for b in sorted(fam):
        ks = fam[b]
        h = next((home[k] for k in ks if home[k] and home[k][2] != "class"), None) or next((home[k] for k in ks if home[k]), None)
        for k in ks:
            if not home[k] and h: home[k] = (h[0], h[1], "variant")
    for k in range(n):
        if home[k]: continue
        name = nm[k] or ""
        g = next((folder for rx, folder in generated if re.match(rx, name)), None)
        if g: home[k] = (g, None, "generated"); continue
        if MAVLINK_NAME.match(name): home[k] = ("mavlink", None, "name"); continue
        ch = class_home(class_of(base_name(name)))
        if ch: home[k] = (ch[0], ch[1], "class")
    free = sorted({re.split(r"['.]", nm[k] or "")[0] for k in range(n) if not home[k]} - {""})
    fd = free_definitions(ap, free)
    for k in range(n):
        if home[k]: continue
        ps = fd.get(re.split(r"['.]", nm[k] or "")[0])
        if ps and len(set(map(folder_of_path, ps))) == 1: home[k] = (folder_of_path(ps[0]), ps[0], "definition")
    # a type (enum, struct, class) of ArduPilot named by the item (`Rotation`, `Rotation.toInt`): where it is defined
    want = {}
    for k in range(n):
        if not home[k] and nm[k]:
            t = nm[k].split(".")[0].split("'")[0]
            if re.fullmatch(r"[A-Za-z_]\w*", t): want[k] = t
    td = type_definitions(ap, sorted(set(want.values())))
    for k, t in sorted(want.items()):
        ps = td.get(t)
        if ps and len(set(map(folder_of_path, ps))) == 1: home[k] = (folder_of_path(ps[0]), ps[0], "type definition")
    users = collections.defaultdict(list)
    for k in range(n):
        for d in deps[k]: users[d].append(k)
    for k in range(n - 1, -1, -1):
        if not home[k] and users[k]:
            h = home[min(users[k])]
            if h: home[k] = (h[0], h[1], "first user")
    for k in range(n):
        if not home[k]:
            ds = sorted(deps[k])
            h = home[ds[-1]] if ds else None
            home[k] = (h[0], h[1], "last dependency") if h else ("Other", None, "none")
    return home

# ----------------------------------------------------------------------------------------------------------------------
# placement

def place_passes(folder, deps, order):
    pos = {f: i for i, f in enumerate(order)}
    p = [0] * len(folder)
    for k in range(len(folder)):
        r = 0
        for d in deps[k]:
            r = max(r, p[d] if (folder[d] == folder[k] or pos[folder[d]] < pos[folder[k]]) else p[d] + 1)
        p[k] = r
    return p


def module_count(folder, deps, order, size=None, small=0):
    """The number of modules of the passes for this order, a module of fewer than `small` lines counting twice."""
    p = place_passes(folder, deps, order)
    lines = collections.Counter()
    for k in range(len(folder)): lines[(p[k], folder[k])] += size[k] if size else 1
    return len(lines) + sum(1 for v in lines.values() if v < small), p


def folder_order(folder, deps, size, small):
    """A linear order of the folders with few modules: start from the order that puts first the folders that depend
    least on the others, then move single folders while that lowers the count."""
    fs = sorted(set(folder))
    size = collections.Counter(folder)
    w = collections.Counter()
    for k in range(len(folder)):
        for d in deps[k]:
            if folder[d] != folder[k]: w[(folder[k], folder[d])] += 1
    rem, order = set(fs), []
    while rem:
        f = min(sorted(rem), key=lambda f: sum(w[(f, g)] for g in rem if g != f) / size[f])
        order.append(f); rem.remove(f)
    best, _ = module_count(folder, deps, order, size, small)
    improved = True
    while improved:
        improved = False
        for i in range(len(order)):
            for j in range(len(order)):
                if i == j: continue
                o = order[:]; f = o.pop(i); o.insert(j, f)
                c, _ = module_count(folder, deps, o, size, small)
                if c < best: best, order, improved = c, o, True
    return order


def consolidate(mod, keyfolder, size, deps, small):
    """Empty modules of fewer than `small` lines into another module of the same folder, where every dependency of
    the moved items is at or before the target and every user at or after it (positions in the linear order)."""
    n = len(mod)
    users = [[] for _ in range(n)]
    for k in range(n):
        for d in deps[k]: users[d].append(k)
    while True:
        mm = collections.defaultdict(list)
        for k in range(n): mm[mod[k]].append(k)
        moved = False
        for M in sorted(mm, key=lambda M: (sum(size[k] for k in mm[M]), M)):
            ks = mm[M]
            if sum(size[k] for k in ks) >= small: continue
            S = set(ks)
            lo = max([mod[d] for k in ks for d in deps[k] if d not in S], default=-1)
            hi = min([mod[u] for k in ks for u in users[k] if u not in S], default=10 ** 9)
            cands = [T for T in sorted(mm) if T != M and keyfolder[T] == keyfolder[M] and lo <= T <= hi]
            if cands:
                T = min(cands, key=lambda T: (abs(T - M), T))
                for k in ks: mod[k] = T
                moved = True; break
        if not moved: return mod


def convex(S, E, R):
    """No path leaves the module set S and comes back (E: module -> modules it depends on, R: reachability)."""
    for m in S:
        for d in E[m]:
            if d not in S and any(s in R[d] for s in S): return False
    return True


def split_by_source(ks, file_of, deps, max_lines, size):
    """Cut a module's items (in source order) into chunks of whole ArduPilot source files (a header and its .cpp
    count as one), each of at most max_lines lines where the files allow, preserving dependency order."""
    stem = lambda k: (Path(file_of[k]).stem if file_of[k] else "_")
    stems = sorted({stem(k) for k in ks})
    S = set(ks)
    E = collections.defaultdict(set)
    for k in ks:
        for d in deps[k]:
            if d in S and stem(d) != stem(k): E[stem(k)].add(stem(d))
    # strongly connected components of the source-file graph (Tarjan), in dependency order
    index, low, st, on, comps, c = {}, {}, [], set(), [], [0]
    sys.setrecursionlimit(100000)
    def sc(v):
        index[v] = low[v] = c[0]; c[0] += 1; st.append(v); on.add(v)
        for w in sorted(E[v]):
            if w not in index: sc(w); low[v] = min(low[v], low[w])
            elif w in on: low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = st.pop(); on.discard(w); comp.append(w)
                if w == v: break
            comps.append(sorted(comp))
    for v in stems:
        if v not in index: sc(v)
    lines_of = collections.Counter()
    for k in ks: lines_of[stem(k)] += size[k]
    chunks, cur, cur_lines = [], [], 0
    for comp in comps:   # Tarjan emits components after the ones they depend on
        cl = sum(lines_of[s] for s in comp)
        if cur and cur_lines + cl > max_lines:
            chunks.append(cur); cur, cur_lines = [], 0
        cur += comp; cur_lines += cl
    if cur: chunks.append(cur)
    where = {s: i for i, ch in enumerate(chunks) for s in ch}
    return [[k for k in ks if where[stem(k)] == i] for i in range(len(chunks))], chunks

# ----------------------------------------------------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("source"); ap.add_argument("--namespace", required=True)
    ap.add_argument("--ardupilot", required=True); ap.add_argument("--root", required=True)
    ap.add_argument("--out-dir", required=True); ap.add_argument("--module-prefix", required=True)
    ap.add_argument("--deps"); ap.add_argument("--deps-index")
    ap.add_argument("--import-map", action="append", default=[], help="OLD=NEW module renaming for runtime imports")
    ap.add_argument("--foreign-index", action="append", default=[], help="NS=INDEX.json of an already split file")
    ap.add_argument("--always-import", action="append", default=[], help="a module every module imports")
    ap.add_argument("--generated", action="append", default=[], help="REGEX=MODULE for items without a C++ origin")
    ap.add_argument("--anchor", action="append", default=[], help="NAME=DECL: a cross-library module from DECL's pass on")
    ap.add_argument("--anchor-doc", action="append", default=[], help="NAME=TEXT: what the cross-library module holds")
    ap.add_argument("--top-pass", type=int, default=None, help="the first pass of the cross-library modules")
    ap.add_argument("--small", type=int, default=300); ap.add_argument("--max-lines", type=int, default=8000)
    ap.add_argument("--source-name", required=True, help="the source's path as recorded in the index")
    ap.add_argument("--title", required=True)
    ap.add_argument("--verbose", action="store_true")
    a = ap.parse_args()
    NS = a.namespace; root = Path(a.root); out = root / a.out_dir
    text = Path(a.source).read_text()
    lines, items, first, endl = parse(text, NS)
    n = len(items)
    size = [it["b"] - it["a"] for it in items]
    nm = [decl_name(lines, it) for it in items]
    imap_exact = dict(x.split("=", 1) for x in a.import_map if not x.split("=", 1)[0].endswith("."))
    imap_prefix = [tuple(x.split("=", 1)) for x in a.import_map if x.split("=", 1)[0].endswith(".")]
    class IMap:
        def get(self, m, default=None):
            if m in imap_exact: return imap_exact[m]
            for o, n_ in imap_prefix:
                if m.startswith(o): return n_ + m[len(o):]
            return default
    imap = IMap()

    if a.deps:
        deps, other, names, clients, foreign = read_deps_tsv(a.deps, items, NS)
        tdeps = token_deps(lines, items, names, NS)
        for k in range(n): deps[k] |= tdeps[k]
        other = [sorted(imap.get(m, m) for m in o) for o in other]
        foreign = [sorted(f) for f in foreign]
        names = [sorted(x) for x in names]
    else:
        old = json.load(open(a.deps_index))
        assert [it["lines"] for it in old["items"]] == size
        deps = [set(it["deps"]) for it in old["items"]]; other = [it["runtime"] for it in old["items"]]
        names = [it["names"] for it in old["items"]]; foreign = [it.get("foreign", []) for it in old["items"]]
        clients = old.get("clients", {})
    assert all(d < k for k in range(n) for d in deps[k]), "a dependency on a later item"

    # foreign constants (of files split before this one) -> their modules
    fmods = [set() for _ in range(n)]
    for spec in a.foreign_index:
        fns, path = spec.split("=", 1)
        fi = json.load(open(path))
        owner = {}
        for it in fi["items"]:
            for c in it["names"]: owner[fns + "." + c] = it["module"]
        for k in range(n):
            for c in foreign[k]:
                p = c
                while p not in owner and "." in p: p = p.rsplit(".", 1)[0]
                if p in owner: fmods[k].add(owner[p])
        for k in range(n):
            other[k] = [m for m in other[k] if m != fns and m != imap.get(fns)]

    generated = [tuple(g.split("=", 1)) for g in a.generated]
    home = classify(lines, items, nm, deps, a.ardupilot, generated)
    folder = [h[0] for h in home]; srcfile = [h[1] for h in home]

    order = folder_order(folder, deps, size, a.small)
    _, p = module_count(folder, deps, order)
    pos = {f: i for i, f in enumerate(order)}
    keys = sorted(set(zip(p, folder)), key=lambda x: (x[0], pos[x[1]]))
    kidx = {key: i for i, key in enumerate(keys)}
    mod = [kidx[(p[k], folder[k])] for k in range(n)]
    mod = consolidate(mod, [key[1] for key in keys], size, deps, a.small)

    # cross-library modules for the top: bands of passes starting at the anchors' passes
    group = {}   # key index -> cross module name
    if a.anchor:
        anchors = []
        for spec in a.anchor:
            name, decl = spec.split("=", 1)
            k = nm.index(decl) if decl in nm else None
            assert k is not None, f"anchor {decl} not found"
            anchors.append((keys[mod[k]][0], name))
        anchors.sort()
        top = a.top_pass if a.top_pass is not None else anchors[0][0]
        for K in sorted(set(mod)):
            pk = keys[K][0]
            if pk < top: continue
            name = [nm_ for ap_, nm_ in anchors if ap_ <= pk]
            group[K] = name[-1] if name else anchors[0][1]
    # modules: (name hint, items) in linear order
    mm = collections.defaultdict(list)
    for k in range(n): mm[mod[k]].append(k)
    units = []   # (kind, folder or cross name, items)
    seen_group = {}
    for K in sorted(mm):
        if K in group:
            g = group[K]
            if g in seen_group: units[seen_group[g]][2].extend(mm[K])
            else: seen_group[g] = len(units); units.append(("cross", g, list(mm[K])))
        else:
            units.append(("folder", keys[K][1], list(mm[K])))
    for u in units: u[2].sort()
    # size split
    final = []
    for kind, f, ks in units:
        if sum(size[k] for k in ks) > a.max_lines:
            parts, stems = split_by_source(ks, srcfile, deps, a.max_lines, size)
            for part, st in zip(parts, stems): final.append((kind, f, part, st))
        else:
            final.append((kind, f, ks, None))
    # verify the order: every dependency is in the same or an earlier unit
    unit_of = [None] * n
    for i, (_, _, ks, _) in enumerate(final):
        for k in ks: unit_of[k] = i
    bad = [(k, d) for k in range(n) for d in deps[k] if unit_of[d] > unit_of[k]]
    assert not bad, f"{len(bad)} dependencies on a later module, e.g. {nm[bad[0][0]]} -> {nm[bad[0][1]]}"

    # names
    SPECIAL = {f for f in set(folder) if "/" not in f and f not in ("ArduCopter", "mavlink")}
    count_in_folder = collections.Counter(f for kind, f, _, _ in final if kind == "folder")
    numbering = collections.Counter()
    modnames = []
    used = set()
    stem_units = collections.defaultdict(set)
    for i, (kind, f, ks, st) in enumerate(final):
        for k in ks:
            if srcfile[k]: stem_units[(folder[k], Path(srcfile[k]).stem)].add(i)
    for i, (kind, f, ks, st) in enumerate(final):
        if kind == "cross" or f in SPECIAL:
            base = [f]
        else:
            lib = f.split("/")[-1]
            base = f.split("/")
            numbering[f] += 1
            stems = sorted({Path(srcfile[k]).stem for k in ks if srcfile[k]})
            if st and len(st) <= 2:
                leaf = "_".join(st)
            elif numbering[f] > 1 and len(stems) == 1 and stem_units[(f, stems[0])] == {i} and stems[0] != lib:
                leaf = stems[0]
            else:
                leaf = lib if numbering[f] == 1 else f"{lib}_{numbering[f]}"
            base = base + [leaf]
        if kind == "cross" or f in SPECIAL:
            nmod = sum(1 for x in final[:i + 1] if x[1] == f)
            if nmod > 1: base = [f"{f}_{nmod}"]
        path = "/".join(base)
        assert path.lower() not in used, path
        used.add(path.lower())
        modnames.append(path)
    modules = [a.module_prefix + "." + p.replace("/", ".") for p in modnames]

    # imports
    runtime_closure = {}
    def imports_of_file(m):
        f = root / (m.replace(".", "/") + ".lean")
        if not f.exists(): return []
        return [l.split()[1] for l in f.read_text().split("\n") if l.startswith("import ")]
    def closure(m):
        if m not in runtime_closure:
            runtime_closure[m] = set()
            for i in imports_of_file(m): runtime_closure[m] |= {i} | closure(i)
        return runtime_closure[m]
    mod_imports = []
    for i, (kind, f, ks, st) in enumerate(final):
        sib = sorted({unit_of[d] for k in ks for d in deps[k]} - {i})
        rt = set(a.always_import)
        for k in ks: rt |= set(other[k]); rt |= fmods[k]
        # drop runtime imports that another runtime import already brings
        rt = {m for m in rt if not any(m in closure(x) for x in rt if x != m)}
        mod_imports.append((sorted(rt), [modules[j] for j in sib]))

    # header pieces
    doc_end = None
    depth = 0
    for j in range(first):
        if lines[j].startswith("/-!"):
            k = j
            while comment_depth_after(lines[k], 0 if k == j else 1) > 0 and not lines[k].rstrip().endswith("-/"): k += 1
            doc_end = k
            break
    assert doc_end is not None
    header_tail = "\n".join(lines[doc_end + 1:first]) + "\n"
    prefix = "\n".join(lines[:first]) + "\n"
    suffix = "\n".join(lines[endl:])
    body = "\n".join(lines[first:endl]) + "\n"
    assert prefix + body + suffix == text

    def sources_of(ks):
        c = collections.Counter()
        for k in ks: c[srcfile[k] or "(generated)"] += size[k]
        return [s for s, _ in sorted(c.items(), key=lambda x: (-x[1], x[0]))]
    anchor_doc = dict(x.split("=", 1) for x in a.anchor_doc)
    # write
    if out.exists():
        for f in sorted(out.rglob("*.lean")): f.unlink()
    for i, (kind, f, ks, st) in enumerate(final):
        rt, sib = mod_imports[i]
        srcs = sources_of(ks)
        shown = ", ".join(f"`{s}`" for s in srcs[:8]) + (f" and {len(srcs) - 8} more" if len(srcs) > 8 else "")
        if kind == "cross":
            fam = collections.Counter()
            for k in ks: fam[base_name(nm[k] or "")] += size[k]
            main_fns = [x for x, _ in sorted(fam.items(), key=lambda x: (-x[1], x[0]))[:10]]
            what = (f"Cross-library module `{f}`: {anchor_doc.get(f, 'part of the top of the call graph')}. It belongs to "
                    f"the top of the call graph, where ArduPilot's libraries call each other in a cycle, so it cannot be "
                    f"cut by library. Largest functions: " + ", ".join(f"`{x}`" for x in main_fns) + f". Sources: {shown}.")
        elif f in SPECIAL:
            what = f"`{f}`: generated items without a C++ function of their own."
        else:
            nf = sum(1 for x in final if x[0] == "folder" and x[1] == f)
            nth = sum(1 for x in final[:i + 1] if x[0] == "folder" and x[1] == f)
            what = f"ArduPilot `{f}`" + (f", part {nth} of {nf}" if nf > 1 else "") + f". Sources: {shown}."
        doc = (f"/-!\n{what}\n\nItems of `{a.source_name}` ({a.title}), unchanged; placed by `tools/split_modules.py` "
               f"(`{a.out_dir}/INDEX.md`).\n-/\n")
        body_text = "".join("\n".join(lines[items[k]["a"]:items[k]["b"]]) + "\n" for k in ks)
        if not body_text.endswith("\n\n"): body_text += "\n"
        content = "".join(f"import {m}\n" for m in rt + sib) + "\n" + doc + header_tail + body_text + suffix
        path = out / (modnames[i] + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
    # umbrella
    hdr_doc = "\n".join(lines[0:doc_end + 1])
    hdr_doc = hdr_doc[hdr_doc.index("/-!"):]
    umbrella = "".join(f"import {m}\n" for m in modules) + "\n" + hdr_doc + "\n\n" + \
        f"/-! The modules above are `{a.source_name}` split by `tools/split_modules.py` ({len(modules)} modules; " + \
        f"`{a.out_dir}/INDEX.md`). -/\n"
    (root / (a.out_dir + ".lean")).write_text(umbrella)

    # index
    index = dict(
        source=dict(path=a.source_name, namespace=NS, sha256=hashlib.sha256(text.encode()).hexdigest(),
                    body_sha256=hashlib.sha256(body.encode()).hexdigest(), prefix=prefix, header_tail=header_tail,
                    suffix=suffix),
        modules=[dict(module=modules[i], path=f"{a.out_dir}/{modnames[i]}.lean", kind=final[i][0],
                      folder=final[i][1], items=len(final[i][2]), lines=sum(size[k] for k in final[i][2]),
                      imports=mod_imports[i][0] + mod_imports[i][1]) for i in range(len(final))],
        items=[dict(module=modules[unit_of[k]], lines=size[k], name=nm[k], folder=folder[k], source=srcfile[k],
                    rule=home[k][2], deps=sorted(deps[k]), runtime=other[k], foreign=foreign[k], names=names[k])
               for k in range(n)],
        clients=clients)
    (out / "INDEX.json").write_text(json.dumps(index, indent=0, sort_keys=False) + "\n")

    # INDEX.md
    md = [f"# {a.title}: ArduPilot source file to Lean module", "",
          f"`{a.source_name}` ({n} items, {len(text.splitlines())} lines) split into {len(modules)} modules by `tools/split_modules.py`; "
          f"`tools/check_split.py` rebuilds it byte for byte from `INDEX.json`. A function is in the folder of the "
          f"ArduPilot source file its doc comment cites (or of its C++ class). Modules of one folder are numbered in "
          f"dependency order (`AC_PID.lean` before `AC_PID_2.lean`); the cross-library modules hold the top of the "
          f"call graph, where the libraries call each other in a cycle.", "",
          "## Modules", "", "| module | lines | items | ArduPilot sources (by size) |", "|---|---:|---:|---|"]
    for i in range(len(final)):
        srcs = sources_of(final[i][2])
        md.append(f"| `{modnames[i]}` | {sum(size[k] for k in final[i][2])} | {len(final[i][2])} | "
                  + ", ".join(f"`{s}`" for s in srcs[:6]) + (f" (+{len(srcs) - 6})" if len(srcs) > 6 else "") + " |")
    md += ["", "## ArduPilot source files", "", "| source file | modules (items) |", "|---|---|"]
    bysrc = collections.defaultdict(collections.Counter)
    for k in range(n): bysrc[srcfile[k] or f"({folder[k]}: generated)"][modnames[unit_of[k]]] += 1
    for s in sorted(bysrc):
        md.append(f"| `{s}` | " + ", ".join(f"`{m}` ({c})" for m, c in sorted(bysrc[s].items(), key=lambda x: (modnames.index(x[0])))) + " |")
    (out / "INDEX.md").write_text("\n".join(md) + "\n")

    # report
    if a.verbose:
        for i, (kind, f, ks, st) in enumerate(final):
            ps = sorted({keys[mod[k]][0] for k in ks})
            print(f"  {modnames[i]:55s} passes {ps} lines {sum(size[k] for k in ks):6d} items {len(ks)}")
    ls = sorted(sum(size[k] for k in ks) for _, _, ks, _ in final)
    print(f"{a.source_name}: {n} items -> {len(final)} modules; lines per module min {ls[0]} median {ls[len(ls)//2]} max {ls[-1]}")
    print("folder order:", " ".join(order))
    print("rules:", dict(sorted(collections.Counter(h[2] for h in home).items())))


if __name__ == "__main__":
    main()
