# harness

Contract-based verification of real, unmodified flight-stack C++ (ArduPilot and PX4), with Lean as the harness. The
C++ is not translated: each stage of a stack is compiled as its own executable (a module) behind a stdin/stdout
protocol. A harness is a Lean wrapper around one module or around a composition of harnesses: it holds the contract,
the parameters, the test evidence (a hash-bound ledger) and the runtime monitors, and `harness serve` runs the
composed real code with every clause monitored at every tick. Lean proves that the children's contracts, as wired,
give the system's contract (the formal link, `Harness/Link*.lean`), with the remaining hypotheses named. Docs:
[docs/](docs/), starting with [docs/0-status.md](docs/0-status.md) (state and layout) and the table below.

Lean is frozen at v4.35.0 (`lean-toolchain`); `lake-manifest.json` has no dependencies. Do not run `lake update`.

## Build

Prerequisites: macOS with the Xcode command line tools (clang), [elan](https://github.com/leanprover/elan) (it
installs Lean v4.35.0 from `lean-toolchain`), git, Python 3 (`python3`), [uv](https://github.com/astral-sh/uv) for
the simulator's environments. From this directory:

```
tools/fetch_deps.sh            # ArduPilot, PX4 v1.17.0, mavlink at pinned commits into deps/ (git-ignored)
../sim/setup.sh                # the shared simulator's Python environments and gorge world (once, about 3 min)
LEAN_NUM_THREADS=1 lake build  # the harness library and the `harness` command (.lake/build/bin/harness)
tools/build_modules.sh sim        # the simulator modules (plant_sim, plant_formation)
tools/build_modules.sh ardupilot  # the ArduPilot modules (about 15 min)
tools/build_modules.sh px4        # the PX4 modules (about 8 min)
```

`tools/fetch_deps.sh` can reuse clones you already have: set `ARDUPILOT_SRC`, `PX4_SRC`, `MAVLINK_SRC` to them.
Executables go to `build/modules/NAME/`.

## Run

The three gorge scenarios on the ArduPilot stack, from `ardupilot/`:

```
cd ardupilot
./fly_qgc.sh                   # one X500 through the gorge, flown from QGroundControl
./fly_qgc.sh abreast           # two X500s side by side (MAVLink systems 1 and 2)
./fly_qgc.sh staggered         # two X500s staggered, the rear one flying nose-backward
./fly_gorge.sh [single|abreast|staggered]   # the same with no ground station: prints PASS/FAIL
```

QGroundControl is unmodified with default settings: the vehicles send MAVLink to UDP 14550, the cameras (live video)
stream from UDP 5600 (`--udp-port`, `--video-port`, `--pose-port`, `--no-video` change that). The mission is uploaded
from QGroundControl (Plan view): `../sim/plans/gorge.plan`, or `formation-abreast-v1.plan` and `-v2.plan`, or
`formation-staggered-v1.plan` and `-v2.plan`, one per vehicle.

By default a flight or session leaves nothing on disk (it works in a temporary directory, removed on exit). Add
`--record [DIR]` to any of the four launchers to keep its files in DIR (default `out/SCENARIO` in the stack's
directory: record CSVs, monitor verdicts `serve.log`, logs) and append the session to the node's ledger. With
`fly_qgc.sh`, `--out DIR` keeps the files without the ledger record.

The same three on the PX4 stack, from `px4/` (`px4_full`; two vehicles: `px4_formation`, two `px4_full` stacks and
`plant_formation`):

```
cd px4
./fly_qgc.sh                   # one X500 through the gorge, flown from QGroundControl
./fly_qgc.sh abreast           # two X500s side by side (MAVLink systems 1 and 2)
./fly_qgc.sh staggered         # two X500s staggered, the rear one flying nose-backward
./fly_gorge.sh [single|abreast|staggered]   # the same with no ground station: prints PASS/FAIL
```

The same options and defaults (`--udp-port 14550`, `--video-port 5600`, `--pose-port`, `--no-video`). PX4 does not
fly spline waypoints, so its plans are `px4/plans/gorge.plan`, `formation-abreast-v1.plan` and `-v2.plan`,
`formation-staggered-v1.plan` and `-v2.plan` (made from `../sim/plans` by `px4/gorge/make_plans.py`): upload each
vehicle's in Plan view, then arm and start the mission; PX4 lands and disarms by itself
([docs/13-px4-gorge-scenarios.md](docs/13-px4-gorge-scenarios.md)).

The command a newcomer needs (`.lake/build/bin/harness`):

```
harness list                  # the modules and systems of both stacks
harness status ap_full_ekf    # each clause: backed (by which evidence), stale, failed or unbacked
harness test mixer --regime stock_flight --cases 20 --steps 100   # a campaign, recorded in the ledger
harness link ap_formation     # what the formal link proves and what stays a hypothesis
```

## Read in this order

| Document | Question it answers |
|---|---|
| [docs/0-status.md](docs/0-status.md) | What runs today, the layout, every development command |
| [docs/1-idea.md](docs/1-idea.md) | What is the approach, and what is proved versus tested? |
| [docs/2-runtime.md](docs/2-runtime.md) | How does Lean run C++ modules in lock-step? |
| [docs/3-harness.md](docs/3-harness.md) | What is a harness, and where is the evidence stored? |
| [docs/4-algebra.md](docs/4-algebra.md), [docs/harness-algebra.pdf](docs/harness-algebra.pdf) | How do harnesses compose and nest (formally)? |
| [docs/5-creating-a-harness.md](docs/5-creating-a-harness.md) | How do you make one? |
| [docs/6-arducopter.md](docs/6-arducopter.md) | How is ArduCopter partitioned? |
| [docs/7-open-questions.md](docs/7-open-questions.md) | What is undecided? |
| [docs/8-first-example.md](docs/8-first-example.md) | What was built first, and what did the first campaign find? |
| [docs/9-nesting.md](docs/9-nesting.md) | Harnesses containing harnesses; what composing them found |
| [docs/10-formal-link.md](docs/10-formal-link.md) | The Lean theorem from a system's wiring to its contract |
| [docs/11-two-vehicles.md](docs/11-two-vehicles.md) | Two vehicles in one gorge: instances, the formation contract, concurrency |
| [docs/12-gorge-scenarios.md](docs/12-gorge-scenarios.md) | The ArduPilot gorge scenarios: what flies, measured numbers |
| [docs/13-px4-gorge-scenarios.md](docs/13-px4-gorge-scenarios.md) | The PX4 gorge scenarios: plans, the formation, measured numbers |
| [docs/prior-art.md](docs/prior-art.md) | What exists already |
