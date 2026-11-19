#!/usr/bin/env python3
"""Static check of the project's imports (no Lean needed): every import of a project module names a file that exists
with exactly that letter case (macOS's file system ignores case; a Linux clone does not), every module under ArduLean/
is covered by the globs of the library `ArduLean` (lakefile.toml), and the project's module graph has no cycle.

    python3 tools/check_imports.py            (from the repository root; exit status 1 on a problem)
"""
import os, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXT = ("Mathlib", "FloatLib", "DynamicalSystems", "Lean", "Std", "Init", "Batteries", "Aesop", "Qq", "Plausible")
IMP = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z_][\w.']*)\s*$")
files = sorted([f for d in ("ArduLean", "Corpus", "Plant", "tests") for f in (ROOT / d).rglob("*.lean")]
               + [ROOT / n for n in ("Main.lean", "Corpus.lean", "Plant.lean")])

def exact(rel):
    q = ROOT
    for part in rel.parts:
        if part not in os.listdir(q): return False
        q = q / part
    return True

bad = n = 0
graph = {}
for f in files:
    mod = ".".join(f.relative_to(ROOT).with_suffix("").parts)
    graph[mod] = []
    for i, line in enumerate(f.read_text().split("\n"), 1):
        if not re.match(r"^(public\s+)?(meta\s+)?import\b", line): continue
        m = IMP.match(line)
        if not m: print("UNPARSED", f.relative_to(ROOT), i, line); bad += 1; continue
        imp = m.group(1); n += 1
        if imp.split(".")[0] in EXT: continue
        rel = Path(imp.replace(".", "/") + ".lean")
        if not (ROOT / rel).is_file(): print("UNRESOLVED", f.relative_to(ROOT), i, imp); bad += 1
        elif not exact(rel): print("CASE MISMATCH", f.relative_to(ROOT), i, imp); bad += 1
        else: graph[mod].append(imp)

toml = (ROOT / "lakefile.toml").read_text()
sect = toml[toml.index('name = "ArduLean"'):].split("[[")[0]
globs = re.findall(r'"([\w.+]+)"', sect[sect.index("globs"):])
def covered(mod):
    for g in globs:
        if g.endswith(".+"):
            if mod.startswith(g[:-2] + "."): return True
        elif mod == g: return True
    return False
for f in (ROOT / "ArduLean").rglob("*.lean"):
    mod = ".".join(f.relative_to(ROOT).with_suffix("").parts)
    if not covered(mod): print("NOT IN GLOBS", mod); bad += 1

state = {}
def visit(m, stack):
    state[m] = 1
    for d in graph.get(m, []):
        if state.get(d) == 1: print("CYCLE", " -> ".join(stack + [m, d])); return False
        if d not in state and not visit(d, stack + [m]): return False
    state[m] = 2
    return True
sys.setrecursionlimit(100000)
for m in sorted(graph):
    if m not in state and not visit(m, []): bad += 1; break

print(f"{len(files)} files, {n} imports checked, {len(globs)} globs, {bad} problems")
sys.exit(1 if bad else 0)
