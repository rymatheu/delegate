#!/usr/bin/env python3
"""The proposal experiment: a language model proposes port-local contracts, a deterministic Z3 verifier accepts or
returns counterexamples, and we count the rounds until a family passes.

    .venv/bin/python notes/agentic/proposal_loop.py --instance governor --runs 3 --rounds 8
    .venv/bin/python notes/agentic/proposal_loop.py --instance stack --runs 3 --rounds 8
    .venv/bin/python notes/agentic/proposal_loop.py --instance governor --dry      # verifier only, no model

Checks per round (all quantifier-free except (K) without a certificate, which quantifies over one component's
ports only): (Ports) by parsing with only the component's ports declared; (V1) A_P & all S_i |= G_P;
(V2) A_P & all S_i |= A_j for each j; (K) by certificate (strategy terms over inputs at times <= t, substituted
into S_i: one validity check) or by alternation forall in(0) exists out(0) ... over ports(i).
S_i := not A_i or G_i (saturation).  Every proposal, verdict and counterexample is logged to notes/agentic/runs/.
The model is claude-opus-5-5 with adaptive thinking; the API has no seed, so runs are logged, not re-runnable."""
import argparse, json, os, sys, time, pathlib, functools, concurrent.futures as cf
print = functools.partial(print, flush=True)
from fractions import Fraction as Fr
from z3 import *

# ---------------------------------------------------------------- instances
class Instance:
    def __init__(self, name, comps, env, H, AP, GP, words):
        self.name, self.comps, self.env, self.H, self.AP, self.GP, self.words = name, comps, env, H, AP, GP, words
        self.AP_text, self.GP_text = AP.sexpr(), GP.sexpr()   # computed once: Z3 is not thread-safe, prompts are built in threads
    def ports(self, c): i, o = self.comps[c]; return sorted(set(i) | set(o))
    def timed(self, c): return [f"{v}_{t}" for v in self.ports(c) for t in range(self.H + 1)]

SYM = {}
def X(v, t):
    k = f"{v}_{t}"
    if k not in SYM: SYM[k] = Real(k)
    return SYM[k]
def alw(a, b, f): return And([f(t) for t in range(a, b + 1)])

def governor(H=2):
    o, v = (lambda t: X("o", t)), (lambda t: X("v", t))
    AP = alw(0, H, lambda t: And(o(t) >= 0, o(t) <= 5))
    GP = And(alw(0, H, lambda t: And(v(t) >= 0, v(t) <= 2)),
             alw(0, H - 1, lambda t: Implies(o(t) <= 1, Or(v(t) <= Fr(1, 4), v(t + 1) <= Fr(1, 4)))),
             alw(0, H - 1, lambda t: Implies(o(t) >= 3, Or(v(t) >= 1, v(t + 1) >= 1))))
    words = ("A speed governor. Perception reads the environment variable o (distance to an obstacle, 0..5) and writes an "
             "estimate e. Controller reads e and writes a command u. Actuator reads u and writes the speed v. "
             "Query assumption A_P: o stays in [0,5] at every time. Query guarantee G_P: v stays in [0,2] at every time; "
             "whenever o <= 1 at time t (t = 0,1), v <= 1/4 at time t or t+1; whenever o >= 3 at time t (t = 0,1), "
             "v >= 1 at time t or t+1.")
    return Instance("governor", {"Perception": (["o"], ["e"]), "Controller": (["e"], ["u"]), "Actuator": (["u"], ["v"])},
                    ["o"], H, AP, GP, words)

def stack(H=2):
    """A stand-in for the author's longitudinal stack (that instance is not in this directory): three components in a
    chain, two environment inputs, one internal channel per edge."""
    d, w, v = (lambda t: X("d", t)), (lambda t: X("w", t)), (lambda t: X("v", t))
    AP = alw(0, H, lambda t: And(d(t) >= 0, d(t) <= 50, w(t) >= 0, w(t) <= 30))
    GP = And(alw(0, H, lambda t: And(v(t) >= 0, v(t) <= 30)),
             alw(0, H - 1, lambda t: Implies(d(t) <= 10, Or(v(t) <= 5, v(t + 1) <= 5))),
             alw(0, H - 1, lambda t: Implies(And(d(t) >= 30, w(t) >= 20), Or(v(t) >= 10, v(t + 1) >= 10))))
    words = ("A longitudinal driving stack. Sensor reads two environment variables, d (gap to the vehicle ahead, 0..50) "
             "and w (measured own speed, 0..30), and writes two estimates dh and wh. Planner reads dh and wh and writes "
             "one acceleration command a. Vehicle reads a and writes the speed v. "
             "Query assumption A_P: d in [0,50] and w in [0,30] at every time. Query guarantee G_P: v in [0,30] at every "
             "time; whenever d <= 10 at time t (t = 0,1), v <= 5 at time t or t+1; whenever d >= 30 and w >= 20 at time t "
             "(t = 0,1), v >= 10 at time t or t+1.")
    return Instance("stack", {"Sensor": (["d", "w"], ["dh", "wh"]), "Planner": (["dh", "wh"], ["a"]), "Vehicle": (["a"], ["v"])},
                    ["d", "w"], H, AP, GP, words)

INSTANCES = {"governor": governor, "stack": stack}

# ---------------------------------------------------------------- verifier
def smt(inst, c, text):
    """Parse an SMT-LIB 2 Bool term with ONLY the timed ports of c declared.  Returns (expr, error)."""
    decls = {k: X(*k.rsplit("_", 1)) for k in inst.timed(c)}
    try:
        v = parse_smt2_string(f"(assert {text})", decls=decls)
    except Z3Exception as e:
        msg = str(e).splitlines()[0][:300]
        return None, f"not accepted: {msg}. Only these variables exist for {c}: {', '.join(inst.timed(c))}."
    if len(v) != 1: return None, "exactly one Bool term is required"
    return v[0], None
def smt_term(inst, c, t, text):
    """Parse an SMT-LIB 2 Real term for a strategy value at time t: inputs of c at times <= t only."""
    ins = inst.comps[c][0]
    decls = {f"{x}_{s}": X(x, s) for x in ins for s in range(t + 1)}
    try:
        v = parse_smt2_string(f"(declare-fun __r () Real)(assert (= __r {text}))", decls=decls)
    except Z3Exception as e:
        return None, f"strategy term not accepted: {str(e).splitlines()[0][:200]}. Allowed variables at time {t}: {', '.join(sorted(decls))}."
    return v[0].children()[1], None

def valid(f, timeout_ms=60000):
    s = Solver(); s.set("random_seed", 0); s.set("timeout", timeout_ms); s.add(Not(f)); r = s.check()
    return (True, None) if r == unsat else (False, s.model()) if r == sat else (None, None)
def show(inst, m, keep):
    out = []
    for v in sorted(keep):
        out.append(f"{v} = ({', '.join(str(m.eval(X(v, t), model_completion=True)) for t in range(inst.H + 1))})")
    return "; ".join(out)
def K_alt(inst, c, Sc, timeout_ms=60000):
    ins, outs = inst.comps[c]; q = Sc
    for t in reversed(range(inst.H + 1)):
        q = Exists([X(y, t) for y in outs], q)
        if ins: q = ForAll([X(x, t) for x in ins], q)
    return valid(q, timeout_ms)[0]

def verify(inst, fam):
    """fam[c] = dict(A=expr, G=expr, strat={(y,t): term} or None).  Returns (accepted, report dict per component)."""
    S = {c: simplify(Or(Not(fam[c]["A"]), fam[c]["G"])) for c in inst.comps}
    rep = {c: [] for c in inst.comps}; ok = True
    # (K) first: a contract nobody can meet makes the other checks meaningless
    for c in inst.comps:
        ins, outs = inst.comps[c]
        if fam[c]["strat"] is not None:
            sub = [(X(y, t), term) for (y, t), term in fam[c]["strat"].items()]
            r, m = valid(substitute(S[c], *sub))
            if r is not True:
                ok = False
                rep[c].append("(K) your strategy does not meet your own contract" +
                              (f" on the input history {show(inst, m, ins)}." if m is not None else " (solver gave up)."))
        else:
            r = K_alt(inst, c, S[c])
            if r is not True:
                ok = False
                rep[c].append("(K) no causal strategy over your ports meets your contract for every input history "
                              "(checked by quantifier alternation; give a strategy to get a concrete failing history)."
                              if r is False else "(K) the alternation check timed out; give a strategy instead.")
    if not ok: return False, rep, S
    # (V2) before (V1): a (V1) counterexample off some A_j is really a (V2) failure
    for j in inst.comps:
        r, m = valid(Implies(And(inst.AP, *S.values()), fam[j]["A"]))
        if r is not True:
            ok = False
            for c in inst.comps:
                who = "your" if c == j else f"{j}'s"
                rep[c].append(f"(V2) the composition does not establish {who} assumption; on your ports the failing trace is "
                              f"{show(inst, m, inst.ports(c))}." if m is not None else f"(V2) solver gave up on {j}'s assumption.")
    if not ok: return False, rep, S
    r, m = valid(Implies(And(inst.AP, *S.values()), inst.GP))
    if r is not True:
        ok = False
        for c in inst.comps:
            rep[c].append("(V1) the composed contracts do not imply the query guarantee; on your ports the failing trace is "
                          f"{show(inst, m, inst.ports(c))}." if m is not None else "(V1) solver gave up.")
    return ok, rep, S

# ---------------------------------------------------------------- proposer (language model)
SYSTEM = """You are the contract proposer for ONE component of a system. The system is a chain of components with named
input and output variables, a finite time horizon, and a top-level query contract (A_P, G_P) over environment variables
and final outputs. Your job: write an assume-guarantee contract (A, G) for your component ONLY over its own ports, such
that the composition of all components' contracts refines the query. A verifier (Z3) decides acceptance; you never do.

Language: SMT-LIB 2 Bool terms over Real variables named <var>_<time>, e.g. o_0, e_2. Rationals as (/ 1 4).
Connectives: and, or, not, =>, <=, >=, <, >, =. Only variables of your own ports may appear; anything else is rejected.
The composition is accepted iff:
 (V1) A_P and all saturated contracts (not A_i or G_i) imply G_P;
 (V2) A_P and all saturated contracts imply each component's assumption A_j (so assumptions must be established by
      the upstream guarantees, or be true);
 (K) your contract is causally realizable: for every history of your inputs there must be a way to choose your outputs,
      time by time, using only inputs at times <= t, that satisfies (not A or G). Give a strategy to make this check
      concrete: for each output variable y and each time t, a Real term over your inputs at times <= t, e.g.
      (ite (>= o_1 3) 1 0). Constants are allowed. The strategy must satisfy your own contract for every input history.
Guidance: assumptions true are always safe; a guarantee should say only what the query needs from you and what your
downstream neighbour's assumption needs. Keep formulas short and readable, as an engineer would write them: boxes,
threshold implications, 'at time t or t+1' disjunctions. Do not restate the query over variables you do not own.
Do not pin your inputs (an assumption on inputs that upstream cannot establish fails (V2))."""

def proposal_schema():
    from pydantic import BaseModel
    class Proposal(BaseModel):
        assumption: str        # SMT-LIB Bool term over own ports, "true" if none
        guarantee: str         # SMT-LIB Bool term over own ports
        strategy: dict         # {"y_t": "Real term over inputs at times <= t"}; may be empty
        rationale: str         # one or two sentences
    return Proposal

def describe(inst, c, fam_text, feedback, rnd):
    ins, outs = inst.comps[c]
    lines = [inst.words, "",
             f"Horizon: times 0..{inst.H}. Components and ports: " +
             "; ".join(f"{k}: inputs {list(i)}, outputs {list(o)}" for k, (i, o) in inst.comps.items()) + ".",
             f"Environment variables (written by nobody): {inst.env}.",
             f"A_P (SMT-LIB): {inst.AP_text}", f"G_P (SMT-LIB): {inst.GP_text}", "",
             f"You are the proposer for: {c}. Your inputs: {ins}. Your outputs: {outs}. "
             f"Your variables: {', '.join(inst.timed(c))}.", ""]
    if fam_text:
        lines.append("Current proposals of all components (round %d):" % rnd)
        for k, txt in fam_text.items(): lines.append(f"  {k}: assumption {txt[0]} ; guarantee {txt[1]}")
        lines.append("")
    if feedback:
        lines.append("Verifier feedback on the current family (what failed, traces projected onto your ports):")
        for f in feedback: lines.append("  - " + f)
        lines.append("")
        lines.append("Revise your contract (you may also keep it unchanged if you believe another component must change; "
                     "say so in the rationale).")
    else:
        lines.append("Propose your contract.")
    return "\n".join(lines)

def ask(client, inst, c, fam_text, feedback, rnd, log):
    Proposal = proposal_schema()
    prompt = describe(inst, c, fam_text, feedback, rnd)
    t0 = time.perf_counter()
    r = client.messages.parse(model="claude-opus-5-5", max_tokens=16000, system=SYSTEM,
                              output_config={"effort": "high"},
                              messages=[{"role": "user", "content": prompt}], output_format=Proposal)
    dt = time.perf_counter() - t0
    p = r.parsed_output
    log.append({"component": c, "round": rnd, "prompt": prompt, "assumption": p.assumption, "guarantee": p.guarantee,
                "strategy": p.strategy, "rationale": p.rationale, "seconds": round(dt, 1),
                "usage": {"in": r.usage.input_tokens, "out": r.usage.output_tokens}})
    return p

def parse_family(inst, props):
    """props[c] = Proposal-like with .assumption .guarantee .strategy.  Returns fam, per-component syntax errors."""
    fam, errs = {}, {c: [] for c in inst.comps}
    for c, p in props.items():
        A, ea = smt(inst, c, p.assumption); G, eg = smt(inst, c, p.guarantee)
        if ea: errs[c].append("(Ports) assumption " + ea)
        if eg: errs[c].append("(Ports) guarantee " + eg)
        strat = None
        if p.strategy:
            strat = {}
            ins, outs = inst.comps[c]
            for key, txt in p.strategy.items():
                y, t = key.rsplit("_", 1)
                if y not in outs or not t.isdigit() or int(t) > inst.H:
                    errs[c].append(f"(K) strategy key {key} is not an output of {c} at a time <= {inst.H}"); continue
                term, et = smt_term(inst, c, int(t), txt)
                if et: errs[c].append(f"(K) {key}: {et}")
                else: strat[(y, int(t))] = term
            missing = [f"{y}_{t}" for y in outs for t in range(inst.H + 1) if (y, t) not in strat]
            if missing and not errs[c]: errs[c].append(f"(K) strategy misses {missing}")
            if errs[c]: strat = None
        fam[c] = {"A": A if A is not None else BoolVal(True), "G": G if G is not None else BoolVal(True), "strat": strat}
    return fam, errs

def run_loop(inst, client, rounds, run_id, outdir):
    log = []; props = {}; feedback = {c: [] for c in inst.comps}; fam_text = {}
    accepted = False; calls = 0
    for rnd in range(1, rounds + 1):
        with cf.ThreadPoolExecutor(max_workers=len(inst.comps)) as ex:
            futs = {c: ex.submit(ask, client, inst, c, fam_text, feedback[c], rnd, log) for c in inst.comps}
            for c, f in futs.items(): props[c] = f.result(); calls += 1
        fam_text = {c: (props[c].assumption, props[c].guarantee) for c in inst.comps}
        fam, errs = parse_family(inst, props)
        if any(errs.values()):
            feedback = {c: errs[c] or ["(no syntax problem in your proposal; another component's was rejected)"] for c in inst.comps}
            verdict = {"round": rnd, "accepted": False, "errors": errs}
        else:
            t0 = time.perf_counter(); ok, rep, S = verify(inst, fam); tv = time.perf_counter() - t0
            feedback = {c: rep[c] or ["(all checks pass for your contract; another component's fails)"] for c in inst.comps}
            verdict = {"round": rnd, "accepted": ok, "report": rep, "verify_seconds": round(tv, 3)}
            accepted = ok
        log.append({"verdict": verdict})
        print(f"  run {run_id} round {rnd}: {'ACCEPTED' if accepted else 'rejected'}" +
              ("" if accepted else "  " + "; ".join(f"{c}: {len(feedback[c])} note(s)" for c in inst.comps)))
        for c in inst.comps:
            print(f"      {c}: A = {props[c].assumption} | G = {props[c].guarantee}" + (f" | strategy {props[c].strategy}" if props[c].strategy else ""))
            if not accepted:
                for f in feedback[c]: print(f"         {f}")
        if accepted: break
    path = outdir / f"{inst.name}-run{run_id}.jsonl"
    with open(path, "w") as fh:
        for e in log: fh.write(json.dumps(e, default=str) + "\n")
    return accepted, rnd, calls, props, fam if accepted else None

# ---------------------------------------------------------------- comparison on the governor: the known families
def governor_reference(inst):
    """Saturated sets of the swept (maximal) family of docs/example.tex and of D_lazy, for inclusion tests."""
    H = inst.H; o, e, u, v = (lambda t: X("o", t)), (lambda t: X("e", t)), (lambda t: X("u", t)), (lambda t: X("v", t))
    rng = lambda w, lo, hi: alw(0, H, lambda t: And(X(w, t) >= lo, X(w, t) <= hi))
    G_sw = {"Perception": Implies(And(inst.AP, o(1) >= 3), And(rng("e", 0, 5), e(1) >= 3)),
            "Controller": Implies(And(rng("e", 0, 5), e(1) >= 3), And(rng("u", 0, 5), u(1) >= 3)),
            "Actuator": And(rng("v", 0, 2), Or(v(0) >= 1, v(1) >= 1), Or(v(0) <= Fr(1, 4), v(1) <= Fr(1, 4)),
                            Or(v(1) <= Fr(1, 4), v(2) <= Fr(1, 4)), Implies(And(rng("u", 0, 5), u(1) >= 3), Or(v(1) >= 1, v(2) >= 1)))}
    A_sw = {"Perception": inst.AP, "Controller": BoolVal(True), "Actuator": BoolVal(True)}
    return {c: simplify(Or(Not(A_sw[c]), G_sw[c])) for c in inst.comps}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--instance", default="governor", choices=INSTANCES)
    ap.add_argument("--runs", type=int, default=3); ap.add_argument("--rounds", type=int, default=8)
    ap.add_argument("--dry", action="store_true", help="verifier smoke test with hand-written proposals, no model")
    a = ap.parse_args()
    inst = INSTANCES[a.instance]()
    outdir = pathlib.Path(__file__).parent / "runs"; outdir.mkdir(exist_ok=True)
    print(f"instance {inst.name}, H = {inst.H}, z3 {get_version_string()}")
    if a.dry:
        class P:  # hand-written stand-ins: forwarding plus a threshold actuator
            def __init__(s, A, G, st): s.assumption, s.guarantee, s.strategy = A, G, st
        if inst.name == "governor":
            props = {"Perception": P("true", "(and (= e_0 o_0) (= e_1 o_1) (= e_2 o_2))", {f"e_{t}": f"o_{t}" for t in range(3)}),
                     "Controller": P("true", "(and (= u_0 e_0) (= u_1 e_1) (= u_2 e_2))", {f"u_{t}": f"e_{t}" for t in range(3)}),
                     "Actuator": P("true", "(and " + " ".join(f"(>= v_{t} 0) (<= v_{t} 2) (=> (>= u_{t} 3) (>= v_{t} 1)) (=> (<= u_{t} 1) (<= v_{t} (/ 1 4)))" for t in range(3)) + ")",
                                   {f"v_{t}": f"(ite (>= u_{t} 3) 1 0)" for t in range(3)})}
        else:
            props = {"Sensor": P("true", "(and " + " ".join(f"(= dh_{t} d_{t}) (= wh_{t} w_{t})" for t in range(3)) + ")",
                                 {**{f"dh_{t}": f"d_{t}" for t in range(3)}, **{f"wh_{t}": f"w_{t}" for t in range(3)}}),
                     "Planner": P("true", "(and " + " ".join(f"(=> (<= dh_{t} 10) (<= a_{t} 0)) (=> (and (>= dh_{t} 30) (>= wh_{t} 20)) (>= a_{t} 2))" for t in range(3)) + ")",
                                  {f"a_{t}": f"(ite (<= dh_{t} 10) 0 (ite (and (>= dh_{t} 30) (>= wh_{t} 20)) 2 1))" for t in range(3)}),
                     "Vehicle": P("true", "(and " + " ".join(f"(>= v_{t} 0) (<= v_{t} 30) (=> (<= a_{t} 0) (<= v_{t} 5)) (=> (>= a_{t} 2) (>= v_{t} 10))" for t in range(3)) + ")",
                                  {f"v_{t}": f"(ite (<= a_{t} 0) 0 (ite (>= a_{t} 2) 10 7))" for t in range(3)})}
        fam, errs = parse_family(inst, props); print("syntax errors:", {c: e for c, e in errs.items() if e})
        t0 = time.perf_counter(); ok, rep, S = verify(inst, fam); print(f"dry family accepted: {ok} in {time.perf_counter()-t0:.3f} s"); print(rep)
        # a wrong family: actuator ignores the command
        props["Actuator" if inst.name == "governor" else "Vehicle"].guarantee = "(and (>= v_0 0) (<= v_0 2) (>= v_1 0) (<= v_1 2) (>= v_2 0) (<= v_2 2))" if inst.name == "governor" else "(and (>= v_0 0) (<= v_0 30))"
        props["Actuator" if inst.name == "governor" else "Vehicle"].strategy = {}
        fam, errs = parse_family(inst, props); ok, rep, S = verify(inst, fam); print("wrong family accepted:", ok); print(rep)
        return 0
    import anthropic
    client = anthropic.Anthropic()
    ref = governor_reference(inst) if inst.name == "governor" else None
    summary = []
    for run_id in range(1, a.runs + 1):
        print(f"--- run {run_id}")
        acc, rnd, calls, props, fam = run_loop(inst, client, a.rounds, run_id, outdir)
        row = {"run": run_id, "accepted": acc, "rounds": rnd, "model_calls": calls}
        if acc and ref is not None:
            S = {c: simplify(Or(Not(fam[c]["A"]), fam[c]["G"])) for c in inst.comps}
            row["inside_maximal"] = {c: valid(Implies(S[c], ref[c]))[0] for c in inst.comps}
            row["contains_maximal"] = {c: valid(Implies(ref[c], S[c]))[0] for c in inst.comps}
        summary.append(row); print("  summary:", row)
    with open(outdir / f"{inst.name}-summary.json", "w") as fh: json.dump(summary, fh, indent=1, default=str)
    print("=" * 78)
    for r in summary: print(r)
    return 0

if __name__ == "__main__":
    sys.exit(main())
