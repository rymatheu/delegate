# Proposal experiment, 2026-10-21

Question: can a language model propose port-local contracts that the Z3 verifier accepts, in few rounds, and are
they readable?  Script: `proposal_loop.py` (model claude-opus-5-5, adaptive thinking, effort high, structured output;
one proposer per component, all propose each round, counterexamples projected onto each proposer's ports).
Logs: `runs/*.jsonl` (every prompt, proposal, verdict, trace).  Minimality: `minimality.py`.

## Instances
- governor (docs/example.tex): chain Perception -> Controller -> Actuator, H = 2.  The sweep finishes here (0.5 s).
- stack (stand-in; the author's longitudinal stack is not in this directory): Sensor(d, w -> dh, wh) -> Planner(dh, wh
  -> a) -> Vehicle(a -> v), H = 2, two environment inputs.  scripts/delegate.py reports "no nested topological
  ordering: the procedure does not apply" (the Planner has one output to carry two inputs), so the algorithmic route
  gives nothing here.

## Results (3 runs each, budget 8 rounds)
| instance | run | rounds to accept | model calls | model s per call | verify s per round | conjuncts / removable |
|---|---|---|---|---|---|---|
| governor | 1 | 1 | 3 | 11-15 | 0.03 | 27 / 11 |
| governor | 2 | 1 | 3 | 6-13 | 0.03 | 27 / 11 |
| governor | 3 | 1 | 3 | 7-19 | 0.03 | 27 / 11 |
| stack | 1 | 1 | 3 | 8-14 | 0.04 | 30 / 12 |
| stack | 2 | 3 | 9 | 6-14 | 0.02-0.05 | 24 / 6 |
| stack | 3 | 2 | 6 | 9-13 | 0.05 | 30 / 12 |

No proposer gave a strategy; (K) was decided by alternation over the component's ports (milliseconds).
Governor acceptance vs the swept (maximal) family: Perception inside it (exact copy e = o), Controller and Actuator
neither inside nor containing it (different interface conventions: threshold at e = 2, command box [0,2]).

## Observations
1. Acceptance is quick: 1 round on the governor every time; 1-3 rounds on the stack.  Every rejection was an
   interface mismatch between neighbours (Planner says "slow" with a <= 5, Vehicle expects a <= 0), repaired from the
   projected counterexample in the next round.
2. Shape: boxes plus same-time threshold implications at every time, assumptions always true.  Readable, and the
   same shape every run.  The first component always proposes an exact copy of its inputs.
3. Over-delivery: 6-12 of 24-30 conjuncts are individually unnecessary (time-2 obligations the query never looks
   at, boxes on internal variables).  The agents never use "at t or t+1"; they strengthen to "at t".  A weakening
   pass (drop conjuncts while (V1), (V2) hold) would remove these mechanically.
4. The proposers coordinate without talking: in round 1 nobody sees anybody, and the governor still passes
   because all three pick the query's own thresholds (1/4, 1).  On the stack, where the planner must invent the
   command's encoding, that fails 2 of 3 times and the counterexample fixes it.
5. Cost: about 10 s and 1-2k output tokens per proposal; the verifier is negligible.  Non-reproducible (no seed),
   but every run is logged and re-verifiable.

## Not shown by this experiment
- Existence when proposals fail (no run failed).  Non-existence still needs the symbolic sentence.
- Longer horizons (the "at t or t+1" structure matters more at H = 10) and systems with feedback.
- Whether the over-strong first-component copy survives a weakening pass (it should shrink to the one feature
  the query needs, as the sweep's Perception set shows).
