# Flight stacks in Lean

Four routes to a quadcopter flight controller that can be reasoned about in Lean 4, with one shared simulator.
Every controller flies the same three scenarios in the same gorge, from QGroundControl or without it.

| directory | what it is | status |
|---|---|---|
| [`harness/`](harness/README.md) | Contracts, evidence and runtime monitors around the real, unmodified C++ of ArduPilot and PX4, one harness per stage, composed into a flying stack. Lean v4.35.0. | current work |
| [`ardulean/`](ardulean/README.md) | ArduCopter translated to Lean, with a proof corpus and a model of the X500. | legacy |
| [`leanfc/`](leanfc/README.md) | A flight controller written directly in Lean. | legacy |
| [`cpp2lean/`](cpp2lean/README.md) | The C++-to-Lean translator, its differential tests and the proofs of the paper. | legacy |
| [`sim/`](sim/README.md) | The gorge simulator shared by all of the above: world, X500 airframe, sensors, cameras, mission plans. | shared |
| `tools/` | Repository checks. | |

Each subproject is self-contained: its own Lean toolchain and pinned dependencies, its own README with short
Build and Run sections. Third-party sources (ArduPilot, PX4, MAVLink) are not stored here; each subproject that
needs them fetches them at pinned commits into a git-ignored `deps/` folder.

## Quick start

```
sim/setup.sh                    # the simulator's Python environments and the gorge world, once
cd harness                      # or ardulean, leanfc
# build as that directory's README says, then, from the stack's directory
# (harness/ardupilot, harness/px4, ardulean, leanfc):
./fly_gorge.sh                  # one X500 through the gorge, no ground station; prints PASS or FAIL
./fly_gorge.sh abreast          # two X500s side by side
./fly_gorge.sh staggered        # two X500s staggered, the rear one flying nose-backward
./fly_qgc.sh                    # the same three flights for QGroundControl, with live video
./fly_qgc.sh abreast
./fly_qgc.sh staggered
```

## Flying from QGroundControl

QGroundControl is used unmodified with its default settings. Start a `fly_qgc.sh` session, then open
QGroundControl: the vehicles appear on UDP 14550 (two vehicles as MAVLink systems 1 and 2) and each vehicle's
camera is announced over MAVLink, so the video panel shows it without configuration (video on UDP 5600).
The mission plans are in `sim/plans/`; each stack's README says whether its mission is onboard at start or
uploaded from the Plan view. Ctrl-C ends a session. Every launcher accepts `--udp-port` and `--video-port`.

## Requirements

macOS on Apple silicon is what everything was run on. You need the Xcode command line tools, git, Python 3,
[uv](https://github.com/astral-sh/uv) and [elan](https://github.com/leanprover/elan); each subproject's README
lists anything further. Build with `LEAN_NUM_THREADS=1` and never run `lake update`: the dependency versions
are pinned.

## Checks

`tools/check_anonymous.sh` fails if a file that would be committed contains an absolute local path.
