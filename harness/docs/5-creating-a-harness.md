# 5. Creating a harness

## Is it enough to pass a C++ file?

No. A C++ file does not say what the module is. Four things have to be stated that the file cannot tell you:

1. **The step.** Which function is called once per tick.
2. **The ports.** Which values go in each tick, which come out, and which are parameters fixed at start.
3. **The state.** Which objects persist between ticks, and which of their fields a contract will need to see.
4. **The cut.** What the code reaches for outside itself (other ArduPilot singletons, the clock, the hardware layer), and what stands in for each.

You state these in a short declaration. Everything else is generated or generic.

## How much you write depends on the kind of module

| Kind | Example | What you declare | What can be derived |
|---|---|---|---|
| A pure function | `sqrt_controller(error, p, second_ord_lim, dt)` | the function's name | everything: the compiler's view of the signature gives inputs and output; there is no state |
| An object with state | one `AC_PID` | the class, the step method, which fields are parameters and which state to expose | the port types, from the class layout |
| A subsystem | the rate controller with its three PIDs, reading the gyro and the motor limits | the above, plus one line per outside dependency saying which input port replaces it | the adapter skeleton |

Built so far: one object with state (doc 8), declared and adapted by hand. Only the C++ record definitions are generated, from the Lean declaration; nothing is derived from the compiler's view of the code yet.

## The steps

1. **Declare the module** in `ardupilot/modules/<name>/Module.lean`: schemas, contract, executable path, `stack := .ardupilot`. List the ArduPilot sources in `ardupilot/modules/<name>/sources.txt`. Add the module to the list in `Main.lean`.
2. **Write the adapter** `adapter.cpp`: `module_init` fills the real objects from the parameter record; `module_step` calls the step and reads the outputs back. Put what the code reaches for outside the module in `stubs.cpp`.
3. **Build** with `ardupilot/build.sh <name>`. It runs `harness gen <name>` (the record definitions, from the Lean declaration), compiles the listed sources, the adapter and the stubs with the shared flags, computes the code hash and links in `cpp/module_protocol.h`'s `main`.
4. **Register.** `harness describe <name>` runs the executable and checks its schemas against the declaration.
5. **Validate the cut.** Replay inputs recorded at the same boundary in the monolithic vehicle. Bit-identical outputs mean the ports are complete. A mismatch means a hidden dependency; it becomes a port. (Not built yet.)
6. **Write the contract** in `Module.lean`.
7. **Gather evidence** and let the harness write the ledger: test campaigns (`harness test`, built), flight monitoring and model-checker queries (not built).
8. **Wire it** into a system, or into a composite harness (not built).

Steps 1 to 5 make a module. Steps 6 and 7 make it a harness. Step 5 is the one that tells you whether the cut was right, before any contract is written.

## Example: one rate PID

This example is built and tested; doc 8 has the details and the results. It differs from the first sketch in three ports found by reading the code (the clock, the P/D and I scales, the internal-error count), in where the declaration lives (Lean, not TOML), and in its contract.

`ardupilot/modules/rate_pid/Module.lean` (excerpt)

```lean
def input : Schema := #[
  { name := "target", type := .f32 }, { name := "measurement", type := .f32 },
  { name := "dt", type := .f32 }, { name := "limit", type := .bool },
  { name := "pd_scale", type := .f32 }, { name := "i_scale", type := .f32 },
  { name := "now_ms", type := .u32 }]          -- the clock the slew limiter reads

def contract : Contract where
  assume := [
    ⟨"gains_bounded", abs "kp" ≤. 1e4 ∧. abs "ki" ≤. 1e4 ∧. abs "kd" ≤. 1e4⟩,
    ⟨"signals_bounded", abs "target" ≤. 1e4 ∧. abs "measurement" ≤. 1e4⟩,
    ⟨"dt_range", 0 <. "dt" ∧. "dt" ≤. 0.01⟩, ...]
  guarantee := [
    ⟨"integrator_bounded", abs "integrator" ≤. "kimax"⟩,
    ⟨"command_finite", finite "command"⟩,
    ⟨"no_internal_error", "internal_errors" =. 0⟩]
```

`ardupilot/modules/rate_pid/adapter.cpp` (excerpt)

```cpp
void module_step(const Input &in, Output &out)
{
    harness_clock_ms = in.now_ms;   // AP_HAL::millis(), read by the slew limiter
    out.command = pid->update_all(in.target, in.measurement, in.dt, in.limit, in.pd_scale, in.i_scale);
    out.integrator = pid->get_i();
    ...
}
```

The first contract, `finite target ∧ finite measurement ∧ 0 < dt ≤ 0.01 ∧ 0 ≤ kimax` with finite gains, was refuted by its first campaign: finite inputs and gains can overflow `target - measurement` and the P and D products, and the resulting ∞ turns into NaN in the filters. The signals and gains are now bounded.

What each piece of evidence for this contract is, or would be:

- **Tested (built):** the harness generates inputs satisfying `assume`, including edge values (zeros, subnormals, the largest floats, values next to the bounds), and checks `guarantee` after each step. 900,000 steps, no violation.
- **Monitored (not built):** the same check on every tick of a gorge flight.
- **Proved (not built):** a generated query that sets the PID to an arbitrary state with `|integrator| ≤ kimax`, takes arbitrary inputs satisfying `assume`, calls `step` once, and asserts `guarantee`.

The integrator bound is a property already proved for the translated code in ArduLean's corpus, so this module is a good first comparison of effort.
