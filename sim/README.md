# sim: the gorge simulator

One simulator shared by the four flight controllers of this repository (`leanfc/`, `ardulean/`, `harness/ardupilot`,
`harness/px4`): a procedural basalt gorge, a Holybro X500 V2 quadcopter (one, or two in formation) in
[gym-pybullet-drones](https://github.com/utiasDSL/gym-pybullet-drones) / PyBullet, its sensors with optional seeded
noise, wind, a live camera per vehicle announced to QGroundControl as a MAVLink camera, the QGroundControl plan files of
the three scenarios, and stand-in ground-station checks. Nothing here is specific to one flight controller: each
controller's own bridge (how its process is stepped, its protocol, its boot files) lives in its subproject.

## Build

Prerequisites: macOS (or Linux), Python 3.12, [uv](https://github.com/astral-sh/uv).

```
sim/setup.sh
```

Creates `sim/.venv` (simulator) and `sim/.venv-video` (video encoder and decoder) from the pinned `requirements*.txt`,
then builds the gorge world from its seed (about 3 minutes, 300 MB, once) into `sim/build/world-cache/`. Everything
generated goes under `sim/build/` (git-ignored).

## Run

The flights are started from each flight controller's directory (`./fly_qgc.sh [abreast|staggered]`,
`./fly_gorge.sh [single|abreast|staggered]`; see its README). The checks run against any of them:

```
sim/.venv/bin/python sim/checks/video_check.py abreast --launcher ardulean/fly_qgc.sh --mission
sim/.venv/bin/python sim/checks/qgc_session_check.py 14560 400 1=sim/plans/gorge.plan
```

## What is here

| path | what it is |
|---|---|
| `world/` | the gorge (`gorge.py`), fires, cameras (`sensors.py`), the X500 (`x500/x500.urdf`, `airframes.py`), wind, the aviaries, geodesy and origin, the mission geometry (`gorge_plan.py`, `formation_plan.py`), renderers, the live camera (`camera_component.py`, `camera_render.py`); `world/README.md` lists the files |
| `gorgesim/` | the Python package: `plant.py` (the plant API below), `simulator.py` (environment, constants, frames), `sensor_layer.py`, `motors.py`, `missions.py` (mission items), `ground_station.py` (scripted MAVLink ground station, ArduCopter modes), `record.py` (100 Hz record and flight numbers), `udp_bridge.py` (UDP bridge, wall-clock pacer, camera pose feed), `write_qgc_plans.py` |
| `plans/` | QGroundControl plan files (below) |
| `cameras.sh` | starts the cameras of a session (below) |
| `checks/` | `qgc_session_check.py` (stand-in QGroundControl: parameters, mission upload, arm, AUTO), `video_check.py` (stand-in QGroundControl video: camera discovery, RTP/H.264 decode) |
| `render_gorge.py`, `render_gorge_formation.py` | render a recorded flight (`track.csv`) as video and stills |
| `setup.sh`, `requirements.txt`, `requirements-video.txt` | the Python environments |

## Interface for flight controllers

Put `sim/` on `sys.path` and run with `sim/.venv/bin/python`; `import gorgesim` also puts `sim/world/` on the path.

**Plant.** One X500, or two:

```python
from gorgesim.plant import Plant, FormationPlant
p = Plant(seed=None, wind=None, pose_ports=None)   # seed: sensor noise (None: none); wind: (mean, gust) m/s
s = p.reset()                                      # sample 0: resting on the floor at the mission start, nose north
s = p.tick(pwm=[1500, 1500, 1500, 1500])           # one 400 Hz tick -> next sample (s.t_us += 2500)
s = p.tick(actuators=[0.5, 0.5, 0.5, 0.5])         # the same with actuators in [0, 1]
f = FormationPlant.for_plan("staggered", seed=None, pose_ports=None)   # "abreast" or "staggered"
s1, s2 = f.reset()
s1, s2 = f.tick(pwms=[pwm1, pwm2])                 # or actuators=[a1, a2]
```

A tick holds the four motor commands for three 1200 Hz physics substeps (X500 URDF, first-order motor lag, gorge
collision, ArduPilot's gravity 9.80665). Motor order: ArduPilot's quad-X slots 0..3 (front-right CCW, rear-left CCW,
front-left CW, rear-right CW), which are PX4's X500 `rotor_0..3`; PWM 1000..2000 us maps to actuator 0..1, thrust
proportional to the actuator. A `Sample` (`gorgesim/plant.py`) holds: `t_us`; `imu` (three samples, one per substep:
specific force m/s^2 and body rates rad/s, FRD); `baro` (Pa, degC; every 4th tick), `mag` (mGauss, FRD; every 4th),
`gps` (lat, lon deg, alt m AMSL, vn, ve, vd m/s; every 80th), `rc` (16 channels, every 8th), else `None`; `battery`
(16.0 V, 0.5 A); and the true state for records: `pos_ned`, `vel_ned`, `euler`, `rates_frd`, `quat_ned_frd`, `pos_enu`,
`quat_xyzw`, `actuators`. Lock-step: send sample k to the controller, give its reply to `tick`, get sample k + 1.
`p.clearance(i)` and `p.contacts(i)` measure vehicle i against the gorge; `p.env`, `p.obs`, `p.g` are the PyBullet
environment, its last observation and the gorge. The home is the gorge origin (`world/origin.params`: 38.8405556,
-105.0441667, 4302 m), world ENU (0, 0, 0). In `FormationPlant.for_plan`, vehicle 2's noise seed is seed + 100, and in
`staggered` vehicle 2 starts facing backward (`.reverse`, `.routes`, `.lands`). Real time: `gorgesim.udp_bridge.Pacer`
holds a loop to the wall clock; `UdpBridge(port)` gives each vehicle its own UDP socket toward the ground station.

**Video.** Start the cameras, then feed each vehicle's true pose:

```
sim/cameras.sh single|abreast|staggered --parent $$ --udp-port 14550 --video-port 5600 --pose-port 14601 --out DIR
```

It returns at once; the camera process announces vehicle N's camera as MAVLink component 100 of system N on the
`--udp-port` link and ends with process `--parent`. Poses go to UDP `--pose-port` + 2 (N - 1): construct the plant with
`pose_ports=[14601]` (two vehicles: `[14601, 14603]`), or send `udp_bridge.PoseSender(port).send(t_s, pos_enu,
quat_xyzw)` every 4th tick yourself. Streams (RTP/H.264 to 127.0.0.1): one vehicle RGB on the video port V, thermal on
V + 2; two vehicles both RGB on V (only the active vehicle's is sent; QGroundControl switches them), thermal V + 2 and
V + 6. Exit status 2 means no video environment or a pose port in use; start the session without video then. Video is
a separate process at low priority and never changes the flight. It costs about two cores; a busy machine slows the flight loop (it then runs
slower than real time rather than dropping steps).

**Missions and plans.** `plans/gorge.plan` (one X500), `plans/formation-abreast-v1.plan`, `-v2.plan`,
`plans/formation-staggered-v1.plan`, `-v2.plan` (vehicle 2 flies nose-backward: its plan has a CONDITION_YAW before each
spline waypoint). They hold exactly the items `gorgesim.missions` builds (`gorge_mission`, `formation_missions`) and the
scripted ground station uploads; `sim/.venv/bin/python sim/gorgesim/write_qgc_plans.py` rewrites them. A mission
reaches a vehicle either by upload from QGroundControl (Plan view, open the vehicle's file, Upload) or onboard at boot
(the controller loads the same items itself); each stack's README says which. `plans/gorge-leanfc.plan` is the
Lean-native controller's own variant (param4 of the spline items null instead of 0, home altitude rounded to mm; the
waypoints are the same): keep using it to reproduce its flights.

**Checks.** On test ports only (never 14550 or 5600-5607 in tests). `checks/video_check.py SCENARIO --launcher
PATH/fly_qgc.sh` starts the launcher as `fly_qgc.sh [abreast|staggered] --udp-port P --video-port V --pose-port X
--out DIR` (every stack's launcher takes these, plus `--no-video`), checks each camera's HEARTBEAT,
CAMERA_INFORMATION and VIDEO_STREAM_INFORMATION, decodes every stream for 8 s (size, rate, not blank), with two
vehicles the RGB switch, then ends the session with SIGTERM and checks no process is left. `--mission` adds
`qgc_session_check.py` with the plans above; `--attach` checks a session already running. `qgc_session_check.py PORT
TIMEOUT SYSID=PLAN ...` plays QGroundControl (parameter download, mission upload and download, GUIDED, arm, takeoff,
AUTO, past the first spline waypoint) with ArduCopter mode numbers. Both print `RESULT PASS` or `RESULT FAIL`.

## Variants for the Lean-native controller

The world, sensors and airframe are one: `world/x500/x500.urdf` differs from the Lean-native controller's copy in
comments only, and `world/gorge.py` only in where it caches the world. Differences that change a flight are kept
selectable: the single-vehicle plan (`plans/gorge.plan` for ArduPilot-dialect stacks, `plans/gorge-leanfc.plan` for
the Lean-native controller). That controller's own formation-study and parameter-overlay code (`formation_plan.py`
extras: clearance probe, re-centering study, `write_overlay`) is controller-specific and stays in `leanfc/`.
