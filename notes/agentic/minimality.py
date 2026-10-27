#!/usr/bin/env python3
"""Conjunct-minimality of accepted families: for each top-level conjunct of each guarantee, drop it and re-run
(V1), (V2), (K by alternation).  A conjunct whose removal keeps the family accepted is unnecessary for the query.
    .venv/bin/python notes/agentic/minimality.py notes/agentic/runs/governor-run1.jsonl"""
import json, sys, importlib.util, pathlib
spec = importlib.util.spec_from_file_location("pl", pathlib.Path(__file__).parent / "proposal_loop.py"); pl = importlib.util.module_from_spec(spec); spec.loader.exec_module(pl)
from z3 import And, is_and, BoolVal
for path in sys.argv[1:]:
    rows = [json.loads(l) for l in open(path)]
    inst = pl.INSTANCES[pathlib.Path(path).name.split("-")[0]]()
    last = {}
    for r in rows:
        if "component" in r: last[r["component"]] = r
    class P:
        def __init__(s, r): s.assumption, s.guarantee, s.strategy = r["assumption"], r["guarantee"], {}
    fam, errs = pl.parse_family(inst, {c: P(last[c]) for c in inst.comps})
    ok, rep, S = pl.verify(inst, fam); print(f"{pathlib.Path(path).name}: accepted as logged: {ok}")
    total = removable = 0
    for c in inst.comps:
        G = fam[c]["G"]; conj = list(G.children()) if is_and(G) else [G]
        unneeded = []
        for i, cj in enumerate(conj):
            fam2 = {k: dict(v) for k, v in fam.items()}
            rest = [x for j, x in enumerate(conj) if j != i]
            fam2[c]["G"] = And(rest) if len(rest) > 1 else (rest[0] if rest else BoolVal(True))
            if pl.verify(inst, fam2)[0]: unneeded.append(str(cj).replace("\n", " "))
        total += len(conj); removable += len(unneeded)
        print(f"  {c}: {len(conj)} conjuncts, {len(unneeded)} individually removable: {unneeded}")
    print(f"  total conjuncts {total}, individually removable {removable}")
