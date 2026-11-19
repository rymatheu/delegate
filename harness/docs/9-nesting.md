# 9. Nested harnesses

**Status (2026-11-18):** built and run for the nodes in "The first nested harnesses" and for the full ArduCopter stack (`ap_ctl`, `ap_flight`, `ap_full`, `ap_full_ekf`): declaration, checks, runtime, monitors at every level, system code hash, campaigns and ledgers for systems, saved cases (long ones capped: all inputs as deltas, the last outputs, shared by the clauses whose evidence they are), replay of any child alone, regimes and coverage counts, loops closed around the plant, ledger records of served sessions (`monitored`, with `undischarged` for a session with a discharge failure), and stated discharges of obligations (`Discharge`, `withAssume`, `harness obligations NAME --status`). Served flights of `ap_full_ekf` with noise (GUIDED, AUTO, RTL, ALT_HOLD, LOITER, and a QGroundControl-style session through `ardupilot/fly_qgc.sh`) are ledger records with 0 violations and 0 discharge failures. The PX4 stack is built and run the same way (README, "PX4"): ten compositions from `px4_inner` to `px4_full`, a served `px4_full` flown over UDP from a scripted ground station and from QGroundControl (`px4/fly_qgc.sh`), with 0 discharge failures in the headless flights; its discharge table is `px4/harnesses/px4_chain/Discharges.lean`. A served session's log names the failing assumption clauses of an instance with their values (first 50 failing steps per instance). The formal link from a system to a Lean proof is built (doc 10, `harness link NAME`). Not built: the glue check against the monolithic C++.

## The idea in one paragraph

A harness is written in Lean. A harness can call external C++ code (an ArduPilot module, compiled as its own executable) and it can call other harnesses. So the vehicle is one outermost harness that contains modules and harnesses, which contain modules and harnesses, down to the C++. Every level has the same shape: parameters, inputs, outputs, a contract, evidence. Every level is stepped the same way: `init` once, then `step` once per tick.

## Two kinds of node

| Node | What it is | Its `step` |
|---|---|---|
| **module** | one C++ executable behind the module protocol (docs 3 and 8) | one message exchange with its process |
| **system** | a harness written in Lean: an interface, an ordered list of children, and wires | runs each child's `step` once, in order, moving values along the wires |

A child of a system is a module or a system. A node does not know whether it is the outermost one, and its parent does not know which kind it is.

## A system's declaration

A system is a plain Lean value:

- `name`, `doc`
- `params`, `input`, `output` : schemas, as for a module
- `children` : a list, in the order they run within a tick. Each child has an instance name (so the same module can appear several times), the node it instantiates, and one source for every one of its parameter and input fields
- `outputs` : one source for every output field of the system
- `contract` : assumption over (params, input), guarantee over (params, input, output), as for a module

A **source** says where a value comes from:

| Source | Meaning | Allowed for |
|---|---|---|
| `input f` | the system's own input field `f`, this tick | child inputs, system outputs |
| `param f` | the system's own parameter `f` | child parameters, child inputs |
| `out c f` | output field `f` of child `c`, this tick | inputs of children that run **after** `c`, system outputs |
| `prev c f init` | output field `f` of child `c` at the previous tick; `init` at the first tick | inputs of any child |
| `const v` | a constant | child parameters, child inputs |

Wires carry values unchanged. A wire joins two fields of the same type. Arithmetic is not done in wiring: glue that only routes values becomes wires, glue that computes stays in C++ inside a module.

## What is checked before anything runs

1. Names: child instance names are unique; field names follow the module rules.
2. Completeness: every parameter and input field of every child, and every output field of the system, has exactly one source.
3. Types: the two ends of each wire have the same type; a constant has the type of the field it feeds.
4. **No instantaneous loop:** an `out c f` source is used only by children scheduled after `c`. Feedback must use `prev`. This is the side condition of the loop rule (doc 4, `Harness/Algebra.lean`, theorem `loop`): an assumption may rest on guarantees of earlier children at this tick and of all children at earlier ticks.
5. The contract's clauses resolve against the system's own interface. An inner signal a contract needs is wired to an output of the system.

## How a tick runs

1. `init` with the system's parameter record: each child's parameter record is assembled from its sources and the child is initialized. Every `prev` wire is set to its `init` value.
2. `step` with the system's input record: for each child in order, assemble its input record from the sources, call its `step`, keep its output record. Then assemble the system's output record. Then the kept outputs become "previous".
3. A module child's `step` is one exchange with its process. A system child's `step` is this procedure again.

One process per module instance, started when the outermost harness starts. Records cross every boundary as bit patterns, so a value is never rounded or reformatted on its way through a wire.

## Monitors

During every `step`, each node checks its own contract on its own (params, input, output), at every level of the nesting:

- **assumption:** did it hold at this tick? Inside a system, a child's assumption that fails means the system did not discharge it: the system's assumption and the earlier children's guarantees were not enough. That is reported as a discharge failure of the parent, at the child's path.
- **guarantee:** each clause, while the node's assumption has held at every tick so far in the case (the history form, the reading of `Step.always` in the algebra): checks, violations, smallest margin. After the first tick at which a node's assumption fails, its guarantee checks stop for the rest of the case; a stateful module may already be corrupted, so later ticks say nothing.

Paths name instances from the outermost harness down: `inner_loop/rate/roll`.

## Evidence

- A module's evidence is where it was (doc 3): `<stack>/modules/<name>/evidence/`, `<stack>` being the module's declared stack (`ardupilot`, `px4` or `sim`).
- A system's evidence is in `<stack>/harnesses/<name>/evidence/`, with the same ledger format. A system's stack is declared, or else the one flight stack its children other than `sim` share (`closed_inner` is ArduPilot's); children from both flight stacks need a declared stack.
- A campaign on a system generates inputs that satisfy the **system's** assumption, steps it, and checks the system's guarantee. That gives `tested` records for the system's own clauses.
- The same campaign monitored every inner clause. Those are `monitored` records in the system's ledger, one per (path, clause), because they are facts about the children as wired and excited in this system, not about the children alone.
- A system's **code hash** is the hash of its wiring text and of its children's code hashes, in order. Changing one line of one module's C++ changes the hash of every system that contains it, so their records go stale; changing a wire changes only that system and its ancestors.
- A monitored record's contract hash includes the system's assumption, so changing the assumption makes the inner records stale too. A campaign in which no step ran has the verdict `empty` and backs nothing.
- A node may declare **regimes**: named extra clauses over (params, input), with hints for clocks, that narrow what a campaign generates (`harness test NAME --regime R`). A regime only steers sampling: the contract and its hashes are unchanged, and the records are evidence for the same clauses. A node may also declare **coverage** observations, whose true-steps a campaign counts.
- Every exchange of every instance is logged in a saved case, so **any child can be re-run alone from the log** and compared bit for bit. That is the check that a system does nothing to its children except route values.

Status of a system then has three parts: its own clauses (tested as a unit), the inner clauses (monitored in it), and its children's own status (their evidence alone). The formal link, a Lean proof that the children's contracts as wired imply the system's contract, is doc 10: `harness status` reports how many of its hypotheses remain (leaf claims, stated discharges, open obligations), and `harness link NAME` prints them.

## The first nested harnesses

| Harness | Kind | Children | Notes |
|---|---|---|---|
| `rate_pid` | module (built) | | one `AC_PID` |
| `rate` | system | `roll`, `pitch`, `yaw` : `rate_pid` | the three calls of `AC_AttitudeControl_Multi::rate_controller_run_dt`; that function only routes values to the three PIDs, so it becomes wires |
| `mixer` | module | | `AP_MotorsMatrix` (quad X): torque and throttle commands to four motor commands and the limit flags |
| `inner_loop` | system | `rate`, `mixer` | the mixer's limit flags feed the rate PIDs at the next tick (`prev`), as in ArduCopter, where the rate controller runs before the mixer |

After these: the plant node to close the inner loop (next section), then attitude, position, guidance, estimator, supervisor (doc 6).

## Composition by one call

A system does not have to be written wire by wire. `Harness/Compose.lean` builds ordinary system nodes from other nodes by port name:

| Operator | What it does |
|---|---|
| `composeAll name [H1, H2, …]` | one harness containing the listed harnesses, run in list order |
| `compose name a b` | `composeAll name [a, b]` |
| `rename n [(old, new), …]` | the same harness with interface fields renamed |
| `inst n name shared` | every field prefixed `name_`, except the shared ones; for several instances of one module |
| `fix n [(field, value), …]` | inputs or parameters fed by constants and removed from the interface |
| `hide n [output, …]` | outputs removed from the interface |
| `withInit`, `withRegime` | the first-tick value of an output used through `prev`; an added regime |

The rules of `composeAll`:

- An input with the same name and type as an output of an **earlier** harness in the list gets that output of the same tick. From a **later** harness it gets the previous tick's value. So list order is tick order, feedback is automatic, and an instantaneous loop cannot be written.
- An input matched by nothing becomes an input of the composite; two harnesses that need the same unmatched input share one. Parameters are the union by name. Every output is an output of the composite.
- Clashes (same name with different types, two outputs with one name) are errors that name the fields.
- The contained harnesses stay whole: `inner_loop_c/rate_c/roll` is still `rate_pid` with its own contract, evidence and monitors.
- The contract is computed. The guarantee is every child's guarantee. The assumption is every assumption clause that mentions only the composite's own parameters and inputs. An assumption clause about a wired signal is an **obligation**: the neighbor has to deliver it. `harness obligations NAME` lists them, the monitors check them every tick, and a Lean proof would discharge them for good.

The top-level file is `ardupilot/Top.lean`: imports, one `composeAll`, `#harness_check top` (a wiring error fails the build at that line) and `main`. `lake build` makes `.lake/build/bin/top`, which takes `tree`, `obligations`, `test`, `run`, `status`, `replay` and `serve`. In `serve` mode the compiled harness speaks the module protocol, so it can be a child of another harness or sit behind a lock-step driver.

`harness equiv A B` runs two nodes on the same generated inputs and requires bit-identical outputs. The composed `rate_c` and `inner_loop_c` are bit-identical to the hand-written `rate` and `inner_loop`, and the served `top` to `inner_loop_c`. Their declarations are 28 and 22 lines against 184 and 155.

**The first closed loop** is `closed_inner = composeAll [plant_sim, rate_c, mixer]` (ardupilot/harnesses/closed_inner/Composed.lean): the simulator's newest gyro sample of the tick feeds the rate PIDs, and the mixer's four PWM values feed the simulator at the next tick, starting at 1000. It is rate control only, so nothing holds attitude. With stock parameters and small rate targets it runs at about 500 steps per second, every assumption is met at every step, and the vehicle spools up and lifts a few centimeters in 400 ticks.

**Open obligation.** In the composed `inner_loop_c` nothing discharges the mixer's `commands_bounded`: `rate_pid`'s own contract does not bound its command (the code-derived clauses were added to the hand-written `rate`, one level up). It has held at every tested step, but only because short cases cannot grow the integrator far. The repair is to put the command-magnitude clause in `rate_pid`'s contract, where compose will carry it.

## What composing them found

Composition is where a contract is tested against its neighbor. Building `inner_loop` found four things, each kept on record in the declarations with its counterexample.

1. **The rate controller did not promise what the mixer assumed.** The mixer assumed each command within ±1; `rate_pid` guaranteed only a finite command. As first stated, the mixer's assumption failed in 285 of 300 cases.
2. **The first repair was false.** A rate guarantee `|command| ≤ (kpdmax + kimax)(1 + 1e-6)` passed its author's campaigns and was refuted by a rerun with another seed. Cause (`AC_PID.cpp`, the P+D limit): P and D are scaled separately and re-added, so the rounding scales with |P| + |D|, not with the limit.
3. **That repair also excluded the real vehicle.** It needed the P+D limit set; stock ArduCopter leaves it at 0.
4. **The correction is on the mixer's side.** `AP_MotorsMatrix` copes with commands beyond ±1 (it scales and raises limit flags). Its assumption is now `|command| ≤ 1e16`; with only "finite" the mix overflows to ∞ − ∞. `rate` now guarantees three code-derived clauses per axis (`command_sum`, `pd_limited`, `command_magnitude`), and `inner_loop` assumes the documented integrator limit `kimax ≤ 1`, which together discharge the mixer's assumption. The P+D limit may be 0.

Separately, the `flight` regime reached the mixer's current limiter and found a NaN (0 · ∞) when the time step is so small that `dt/(dt + tc)` rounds to 0. The mixer's assumption now has `1e-4 ≤ dt`.

With ArduCopter's stock gains and motor parameters (regime `stock_flight`), a case needs about 500 steps to finish spooling up; then about a fifth of the steps are in full flight with no limit flag set.

Caveats on `rate`: it stands for `rate_controller_run_dt` with the system-identification offsets at zero and without that function's feed-forward and gain-boost side effects, and it feeds one clock value to all three PIDs where ArduPilot reads the clock once per PID.

## The plant node: two plants, one contract

There are two plants, and both already exist. Neither is rebuilt here.

| Plant | What it is | Role |
|---|---|---|
| The Lean ODE | the X500's equations of motion over the reals with the motor lag, commands held over each 1/400 s period, `step` = the exact flow over one period (library `Plant`, Lean 4.35, in the ArduLean repository) | the plant **in the proofs**: the system theorem is about it, and its own contract is a Lean theorem, so it needs no ledger record |
| The gorge simulator | the X500 in gym-pybullet-drones in the gorge world, lock-step at 400 Hz, sensor samples out and PWM in (the repository's shared `sim/`; originally `sim/` in the ArduLean repository) | the plant **in the runs**: every closed-loop campaign and every monitored flight steps it |

In the algebra this is one plant harness slot with two implementations under one contract (the swap law). The plant's contract is stated once, as what the flight code may assume about the step from motor commands to the next state. The Lean ODE meets it by proof. The simulator meets it by test: the measured difference between the two over one period (`Plant/MODEL.md`, `tests/plant/numcheck.py`) is the evidence, and it enters the contract as a tolerance. A closed-loop run in the simulator is then evidence about the same contract the theorem uses, and a disagreement between a proved bound and a run points at that tolerance.

Both are harnesses now. The ODE plant is a formal harness (`formal/PlantHarness.lean`, checked by `formal/check.sh`): its claim is a Lean theorem, its evidence has no leaves, and closing a loop around it is backed exactly when the controller harness is (`closeLoop_backed`). The simulator is the module `plant_sim`: the simulator's own environment, motor lag and sensor layer behind the module protocol, four PWM values in, true state and sensor samples out. Two things stand between `plant_sim` and a closed loop: the vehicle writes PWM 0 while it boots, which the module's assumption `pwm_range` excludes, and the first sensor sample exists before any PWM, which the protocol's `init` reply cannot carry.

How the simulator is attached at the top level is not decided: as a node the harness steps (the harness keeps the control flow, which campaigns need), or with the outermost harness standing in for the vehicle behind the simulator's existing lock-step protocol (which the QGroundControl sessions need). Both use the same boundary: sensor samples and PWM as bit patterns.

## What a system replaces, and how that is checked

A system puts Lean wiring where ArduPilot has C++ glue. That the wiring is the glue is a claim. It is checked by building the same slice as one monolithic C++ module (the real glue function with the real parts linked in) and running both on the same inputs: outputs must agree bit for bit. Not built yet.

## Not in this design yet

- Children that run only on some ticks (modes, multi-rate).
- (Built since, doc 10: `harness link NAME` generates, from a system's declaration, the statement Lean proves, with the discharge conditions of the loop rule for its wiring as named hypotheses.)
