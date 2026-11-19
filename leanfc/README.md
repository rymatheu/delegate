# leanfc

**Legacy: kept as it was when development stopped; no further development.**

A compact cascade flight controller for quadrotors written in Lean 4 over FloatLib's IEEE binary32: an error-state EKF,
a waypoint and spline navigator, position, attitude and rate control, quad-X mixing, a vehicle layer with ArduCopter's
modes (STABILIZE, AUTO, GUIDED, LOITER, RTL, LAND, BRAKE), arming checks and failsafes, and a MAVLink interface with
ArduCopter's conventions, so an unmodified QGroundControl flies it. It flies the X500 in the repository's shared gorge
simulator (`../sim/`). Lean v4.35.0, Mathlib v4.35.0.

## Build

Prerequisites: [elan](https://github.com/leanprover/elan), a C compiler, git, Python 3.12 and
[uv](https://github.com/astral-sh/uv) (for the simulator). From the repository root:

```
sim/setup.sh                                  # once: the simulator's Python environments and the gorge world
cd leanfc
lake exe cache get                            # prebuilt Mathlib (pinned in lake-manifest.json; never `lake update`)
LEAN_NUM_THREADS=1 lake build                 # the controller .lake/build/bin/leanfc (first build: about 55 min, FloatLib from source)
```

## Run

From `leanfc/`:

```
./fly_qgc.sh                                  # one X500 through the gorge, flown from QGroundControl
./fly_qgc.sh abreast                          # two X500s side by side (MAVLink systems 1 and 2)
./fly_qgc.sh staggered                        # two X500s staggered, vehicle 2 flying nose-backward
./fly_gorge.sh [single|abreast|staggered]     # the same flight with a scripted ground station; prints PASS/FAIL
```

- `fly_qgc.sh` runs in real time: MAVLink to UDP 14550, live video from each vehicle's camera (MAVLink camera
  component N/100; RTP/H.264 on UDP 5600 and up). Open QGroundControl with its default settings.
- The missions are onboard at boot: press Start Mission (one vehicle), or Select All, Arm and Start in the Multi-Vehicle
  panel (two). Uploading is optional: use leanfc's plan files in `plans/` (`gorge.plan`, `formation-PLAN-v1.plan`,
  `-v2.plan`), not `sim/plans/formation-staggered-v2.plan` (leanfc has no CONDITION_YAW; it turns vehicle 2 with
  `nav.yawReverse`). `../sim/.venv/bin/python -B sim/flights/leanfc_plans.py --plans` regenerates them, `--check-plans`
  checks them against what a session uses.
- Options: `--udp-port N`, `--video-port N`, `--pose-port N`, `--record [DIR]`, `--no-video`, `--tiles-port N` (a map tile
  server of the gorge); environment `NOISE=field|none`, `SEED=N`, `WIND="MEAN GUST"`, `SPEED=S` (1 = real time).
- `fly_gorge.sh` ends by itself, runs as fast as the simulation goes (`--speed 1` for real time), and uses MAVLink port
  14591 (one vehicle) or 14593 (two); `--port N` changes it.
- Output: none by default (a run leaves nothing on disk). `--record [DIR]` (or `--out DIR`) keeps the records in DIR,
  default `out/qgc-SCENARIO/` (sessions) or `out/gorge-SCENARIO/` (scripted flights): `flight.csv` or `formation.csv`,
  `v1.csv`, `v2.csv` (one row per 400 Hz tick), the MAVLink logs, the camera statistics, `report.txt`.
- Real-time factor (measured on the development machine, video on): one X500 1.000 (worst second 0.998), two X500s
  1.000 (worst second 0.93 to 0.95, a few seconds below 0.98, at most 0.09 s behind the wall clock). Without pacing
  the simulation runs at about 2.1x real time with one vehicle and 1.5x with two.

The controller alone, on flat ground (no gorge): `../sim/.venv/bin/python sim/run_leanfc.py --vehicle x500 --noise none
--out out/run/x500-det.csv`. `LEAN_NUM_THREADS=1 lake exe leanfc --check` runs the controller's own checks.

## More

[docs/reference.md](docs/reference.md) (the full description: architecture, parameters, navigator, EKF, vehicle
layer, MAVLink, results), [docs/DESIGN.md](docs/DESIGN.md), [docs/qgc.md](docs/qgc.md) (QGroundControl sessions),
[docs/qgc-requirements.md](docs/qgc-requirements.md), [docs/gorge.md](docs/gorge.md) (the gorge and formation
flights), [docs/plant.md](docs/plant.md) (the ODE plant library `Plant/`), [docs/import.md](docs/import.md) (what was
imported, what changed with the shared simulator). Pictures and two formation videos: [gallery/](gallery/).
