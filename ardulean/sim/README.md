# ArduLean's side of the simulator

The simulator is the repository's shared `../../sim/` (package `gorgesim`; its README has the plant, cameras, plans and
checks). This folder holds only what is ArduLean's: how its executable is stepped, its protocol, its boot image.
Python: `../sim/.venv/bin/python` from `ardulean/` (the commands below run from there).

| path | what it is |
|---|---|
| `fly_gorge.py` | one X500: scripted flight (`../fly_gorge.sh`) or `--udp` real-time session (`../fly_qgc.sh`) |
| `fly_gorge_formation.py` | two X500s (`--plan abreast|staggered`), same two modes |
| `bridge/vehicle.py` | starts `.lake/build/bin/ardulean` in live mode as a lock-step vehicle (`LEAN_VEHICLE_EXE` selects another executable); `replay_check` for `--replay-check` |
| `bridge/protocol.py` | the per-step protocol: sensor samples, RC, battery, uplink bytes in; `t=<us> pwm=<16> [down=<hex>]` out; every float as its hexadecimal bit pattern |
| `bridge/storage_params.py` | writes parameters (MAV_SYSID, WP_YAW_BEHAVIOR) directly into a boot image |
| `storage/storage-x500.bin` | the X500's boot image (ArduPilot parameter storage); `params/storage-x500.txt` lists every parameter that differs from ArduPilot's defaults, with its reason |
| `params/gorge-{fast,smooth,scurve}-x500.txt` | parameter changes of the fast, smooth and S-curve flights (`--params FILE`) |
| `checks/replay_check.py RUN_DIR` | replays a recorded flight through the executable in file mode and compares the output with `outputs.txt` byte for byte |

The launchers `../fly_gorge.sh` and `../fly_qgc.sh` give the flight programs a temporary `--out` directory and remove
it at exit unless `--record [DIR]` is given; run directly, the programs write to `--out` (default `out/runs/...`).

Per 400 Hz tick the flight program takes the shared plant's sample (`gorgesim.plant.Plant` / `FormationPlant`),
encodes it as one protocol line for the vehicle, reads the vehicle's output line, and gives its PWM back to the plant;
the vehicle's downlink goes to the scripted ground station (`gorgesim.ground_station`) or, with `--udp`, to
QGroundControl through `gorgesim.udp_bridge`. Every scripted flight is deterministic: the same options give the same
record, byte for byte. Two vehicles use MAVLink system ids 1 and 2 (written into vehicle 2's copy of the boot image);
in `staggered` vehicle 2 flies nose-backward (CONDITION_YAW items and WP_YAW_BEHAVIOR 0; `--noses-forward` turns
this off). Other options: `--seed N` (sensor noise), `--wind MEAN GUST` (one X500), `--replay-check`, `--duration S`;
the programs' docstrings have the details. Examples:

```
../sim/.venv/bin/python sim/fly_gorge.py --params sim/params/gorge-fast-x500.txt --out out/runs/fast
../sim/.venv/bin/python sim/fly_gorge.py --straight-north 26.34,47.3,72.0 --params sim/params/gorge-scurve-x500.txt --out out/runs/scurve
../sim/.venv/bin/python sim/checks/replay_check.py out/single
../sim/.venv/bin/python ../sim/render_gorge.py --run out/single --out out/render/single
```
