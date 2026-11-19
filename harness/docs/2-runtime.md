# 2. Running modules in lock-step

**Status (2026-11-18):** several modules run in lock-step inside systems (doc 9): one process per module instance, bit-exact records, the manifest check, every exchange logged. Loops closed around the plant run (`closed_inner`, `est_loop`, `ap_flight`, `ap_full`, `ap_full_ekf`; for PX4 `px4_closed_rate` to `px4_full`, up to fifteen module processes in one tick, in real time at about 1.5 ms per tick).

## One architecture description, three uses

The architecture is a single Lean value: the modules, their ports, the wiring between ports, and the order in which modules run in a tick.

1. **The runner** executes it.
2. **The proofs** are about it: the composition theorem quantifies over this value.
3. **The evidence ledger** is indexed by it: one entry per module contract.

So the harness decides the control flow between modules, and the flow it runs is the object it proves things about.

## How a tick runs

Lean compiles to a native program that can start child processes and talk to them over pipes.

1. The harness starts one process per module.
2. Each tick, in schedule order, it sends a module its input record and blocks until the output record comes back.
3. It checks the module's contract on that exchange and logs both records.
4. The last module's outputs (motor commands) go to the plant; the plant's sensor samples start the next tick.

Blocking on every reply makes a tick deterministic. Seven or so pipe round trips per tick cost far less than the 2.5 ms period of a 400 Hz loop.

## Why separate processes

- Two ArduPilot components linked into one program would collide on ArduPilot's global singletons.
- Processes cannot touch each other's memory, so "modules interact only through their ports" holds by construction. The contract theory assumes this; here the operating system enforces it.

## Rules of the runtime

- **Bit-exact messages.** Floats cross as bit patterns.
- **Hash handshake.** At start a module reports its manifest: the hash of every file the compiler read, the flags and the compiler version, and its schemas. The harness refuses a binary whose schemas differ from the Lean declaration. A binary with a different hash still runs, but evidence recorded for another hash reports as stale.
- **No instantaneous loops.** Within a tick the schedule is acyclic. Feedback goes through the plant or an explicit one-tick delay.
- **Everything is logged.** Any module can be re-run alone from the log. That is the regression test and the isolated-test rig. (Built so far: test campaigns save replayable cases, and `harness replay` reruns them bit for bit; a full per-tick log is not.)
- **Same simulator.** The harness sits behind the lock-step protocol the simulator already uses, so the gorge world and the QGroundControl sessions do not change.
