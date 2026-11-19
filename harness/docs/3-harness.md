# 3. What a harness is

**Status (2026-11-18):** built for the ArduPilot and PX4 modules and their systems (docs 8 and 9): the protocol without `save`/`load` (C++ and Python sides), the declaration in Lean, the contract language with its executable and text readings, regimes and coverage observations, test campaigns, monitors, the ledger with the `tested` and `monitored` kinds (`monitored` also for the sessions of `harness serve`, under `evidence/served/`; a clause checked in a session with a discharge failure is `undischarged`, not backed). A system's evidence is in `<stack>/harnesses/<name>/evidence/` (`<stack>` is `ardupilot`, `px4` or `sim`). The proposition reading of a contract, model-checker queries and the `proved` kind are design.

A harness is three things about one module: its implementation, its contract, and the evidence that the implementation meets the contract.

## Generic by construction

The harness never needs to understand a module's code, only the shape of its messages.

**Every module executable speaks the same protocol:**

| Command | Reply |
|---|---|
| `describe` | its manifest: name, hash of sources and build flags, and the schemas of its parameters, inputs and outputs |
| `init` + parameter record | ready |
| `step` + input record | output record; internal state stays inside the process |
| `quit` | the process exits |
| `save` / `load` (optional, not built) | a snapshot of its internal state |

A schema is a flat list of named, fixed-size numeric fields. Built: binary32 floats, 32-bit signed and unsigned integers, Booleans. Fixed arrays are not built. Records cross the pipe as little-endian words, floats as bit patterns.

**In Lean every module is the same kind of data:**

```
Module
  name
  params, input, output : Schema
  contract : assumption over (input, params)
             guarantee  over (input, output, params)
  exe      : path
```

The expected code hash is not part of the declaration: the executable reports its hash, and each ledger record holds the hash its evidence was recorded for.

From this alone the harness can, for any module: check that wiring is type-correct, run it in the loop, log and replay its messages, generate inputs that satisfy its assumption and test the guarantee, monitor the contract every tick, emit a model-checker query, and validate its evidence. Built so far: run the module alone, generate inputs and test the guarantee, replay saved cases, validate the evidence. The declaration also generates the module's C++ record definitions (`harness gen NAME`), so the schemas are written once, in Lean.

## Two choices that make this work

- **Contracts use a small expression language** over field names: arithmetic, comparisons, Boolean connectives, the previous tick's values. One definition then has three readings: a proposition for Lean proofs, an executable check for monitors and tests, and text for a model checker. Built: the language without the previous tick; evaluation in binary32 exactly as written; printing; a margin for every `≤`/`<` atom. The proposition and the model-checker text are not built.
- **Internal state a contract mentions is an output.** If a contract says "the integrator stays bounded", the module reports the integrator as an output field that only the contract reads.

## Where genericity stops

- The adapter between the message records and the real code is written per module.
- `save` / `load` may not be possible for every module.
- Contracts that compare two executions (sensitivity) can be tested and model-checked, not monitored on one flight.
- Messages are fixed-size numeric records.

## Where the evidence is stored

A module is a folder. Its evidence lives in it, next to the code it is about.

```
ardupilot/modules/<name>/
  Module.lean        schemas, contract, executable path (the declaration)
  sources.txt        the ArduPilot sources compiled into the module
  adapter.cpp        the cut: message records to and from the real code
  stubs.cpp          what the cut leaves outside, and what stands in
  evidence/
    ledger.json      one record per contract clause per campaign
    tested/          campaigns: seed, cases, outputs seen, smallest margins, counterexamples
    proved/          (not built) generated queries and the tool's output
    monitored/       (not built) flights: id, ticks, smallest margins
```

The build flags are shared by all ArduPilot modules, in `ardupilot/build.sh` (PX4 modules: `px4/build.sh`). A PX4 module's folder is `px4/modules/<name>/` and the simulator's `sim/modules/plant_sim/`; the folder follows from the stack named in the declaration.

Each ledger record names the contract clause, the kind of evidence, the verdict, the tool and its version, the exact command, and three hashes: the code (every file the compiler read, the flags, the compiler version), the contract clause (with the assumption it is stated under), and the result file. A clause is backed when a passing record matches all three hashes as they are now, stale when none does, unbacked without a record.

- Change one source line and rebuild: the code hash changes and the harness reports every record for that module as stale. Before the rebuild, `status` reports that the sources changed since the executable was built.
- The executable carries its own code hash (it answers `describe`), so a binary can always be matched to its evidence.
- The code hash must not depend on where or when the repository was cloned and built, so a fresh clone matches the committed evidence. Inputs are labelled relative to their root (`$HARNESS/...`, `$SIM/...`, `$ARDUPILOT_ROOT/...`), never by absolute path, and generated sources must not name a path that depends on the checkout's location (the supervisor's generated `gen/out/shadow_*.cpp` include ArduPilot's headers relative to its `libraries/`). One input is hashed by its content instead of its bytes (since 2026-11-19): the simulator's world cache `sim/build/world-cache/gorge_s7.pkl` (a pickle that `sim/setup.sh` builds), read by `plant_sim` and `plant_formation`. Its bytes hold the build timings (`build_s`, `bake_times`) and absolute paths (`asset_dir`, `files`), so its line in `build/modules/NAME/code_inputs.txt` (marked `(content)`) is a digest of every other value, with `files` reduced to file names: an array by dtype, shape and bytes, an object by class name and fields, a dict by its sorted (key, value) digests, a float by its binary64 bits (`world_digest` in `sim/modules/plant_sim/adapter.py`, used by its `build.sh`). The meshes it names, which PyBullet loads, are hashed by their bytes as every other input. `tools/check_fresh_clone.sh` checks the rule: it builds a fresh clone and compares every module's code hash with the ledgers'.
- A saved case longer than `caseWordBudget` (20000 record words of outputs and instance logs) keeps only its last outputs and no instance logs. Since 2026-11-18 its inputs are written once per case, `tested/ID/case{i}-inputs.json` (the parameters and every input record of the case as indexed deltas: per step `[field index, word, ...]` of the fields that changed), and each saved `(case, step)` file names that file with its SHA-256 and the number of its records it uses (`inputs_file`, `inputs_sha256`, `inputs_count`; its parameters are in the inputs file too, `params_in`), and keeps the outputs of its own step only, as words in schema order (`outputs_words`); `harness replay` checks the hash. A system's saved cases, long or not, are written once per `(case, step)` and shared by the clauses whose evidence they are. Before, each saved `(case, step)` file carried the whole input history and each clause its own copy, which made one 14000-step campaign of `px4_cmd_loop` 592 MB. Replay still reads the earlier forms.
- Since 2026-11-19 every saved case, a module's too, is written once per `(case, step)` and shared by the clauses whose evidence it is (`tested/ID/case{i}-step{k}.json`), and a ledger record names its regime by `regime_hash` (the regime's text is in the result file; a generated node's regime text is hundreds of kilobytes and was repeated in every record). Campaign ids that would collide (one seed, two regimes, the same second) get a suffix `-2`, `-3`.
- A served session's `undischarged` records name the instance whose assumption failed; when that instance's assumption has changed since (its assumption record's hash differs from the current one), `status` no longer counts the session's `undischarged` verdicts (the failure was under a contract that is no longer the instance's).
- Lean reads the ledgers as data (`harness status`). The system theorem's hypotheses are to use the same clause names, so a report can list what backs each hypothesis; no system theorem exists yet.
