# The import into this repository

leanfc was developed as its own project and is kept here as a legacy subproject: the controller (`Leanfc/`, `Shell/`,
`Main.lean`), the ODE plant library (`Plant/`), the parameter files (`params/`), the Lake project (toolchain and
manifest unchanged: Lean v4.35.0, Mathlib v4.35.0, FloatLib, DynamicalSystems) and its documents are copied as they
were. The Lean sources changed in two comments only (a local path removed from `Leanfc/EKF.lean` and from the header of
the generated `Leanfc/Mavlink/Messages.lean`); nothing that is compiled changed.

## What comes from the shared simulator

The world, the airframe and the video are the repository's `sim/` (shared by every flight controller here):

| what | where |
|---|---|
| the gorge (terrain, walls, boulders, vegetation, fires), its cache | `sim/world/gorge.py` (cache in `sim/build/world-cache/`) |
| the X500 URDF and the motor lag | `sim/world/x500/x500.urdf`, `sim/world/airframes.py` |
| the gym-pybullet-drones environments of the gorge (one vehicle, two) | `sim/world/gorge_aviary.py` (`GorgeAviary`, `FormationAviary`), `sim/world/wind.py` |
| the origin, the gorge mission, the formation routes, start and land sites | `sim/world/geo.py`, `gorge_plan.py`, `formation_plan.py` |
| the cameras (MAVLink camera components, RTP/H.264) | `sim/cameras.sh`, `sim/world/camera_component.py`, `camera_render.py` |
| the Python environments | `sim/.venv` (simulator, pymavlink), `sim/.venv-video` (PyAV) |
| the stand-in ground-station checks | `sim/checks/video_check.py`, `sim/checks/qgc_session_check.py` |

## What stays in leanfc

| file | what it is |
|---|---|
| `fly_qgc.sh`, `fly_gorge.sh` | the launchers (README.md, "Run") |
| `sim/run_leanfc.py`, `sim/run_copter.py` | how the controller process is run and stepped (one line per 400 Hz tick), the sensor layer, the flat-ground runs |
| `sim/flights/gorge_session.py` | one X500 in the gorge: run_leanfc's loop with the shared `GorgeAviary`, the pose feed for the camera |
| `sim/flights/formation.py` | two X500s, two controllers, the shared `FormationAviary`; batch (air start) and session (MAVLink) |
| `sim/flights/leanfc_plans.py` | leanfc's parameter overlays (start, onboard mission as TAKEOFF / SPLINE / LAND lines, `nav.yawReverse`), plan files, the formation-offset study |
| `sim/flights/gorge_flight.py`, `formation_flight.py` | the scripted flights of `fly_gorge.sh` (a scripted ground station in QGroundControl's place) |
| `sim/flights/formation_study.py` | batch formation flights over seeds, wind and skew |
| `plans/` | leanfc's plan files (the gorge; abreast and staggered, vehicles 1 and 2), the ones every session uses; `sim/flights/leanfc_plans.py --plans` writes them, `--check-plans` compares |
| `sim/flights/tile_server.py` | an optional map tile server of the gorge (`fly_qgc.sh --tiles-port N`) |
| `sim/mavlink/` | the MAVLink message generator, the codec test, the scripted services test, flight metrics |
| `sim/analyze.py`, `ekf_*`, `nav_*`, `mixer_inverse.py`, `render_flight.py`, `render_gif.py`, `missions/` | the flat-ground analyses and renderers of docs/reference.md |

## Differences from the original project

- The gorge world, the X500 URDF, the aviaries and the motor lag are the shared ones. They are the same code as
  leanfc's own copies (the URDF differs in comments, `gorge.py` in where it caches the world, the aviaries and the wind
  in names only). leanfc's parameter overlays and plan files written over the shared geometry are byte for byte the
  ones the original modules write (checked for the gorge and both formation plans; only the comment line naming the
  writing module differs).
- The shared Python environment pins a newer gym-pybullet-drones commit and NumPy 2.5.5 (leanfc's was 2.5.4). The
  deterministic flat-ground X500 flight (`sim/run_leanfc.py --vehicle x500 --noise none`) gives the numbers of
  reference.md ("Results") to the printed digits (mission time 11.70 s, navigator complete 12.20 s, tracking error max
  67.6 mm, rms 25.6 mm, tilt max 18.2 deg, motors 0.307 to 0.948).
- The gorge flights from the ground are close to the recorded ones of the original project but not identical: the
  scripted ground station's commands reach the simulation at other simulated times (they are sent on the wall clock),
  and the scripted flights of `fly_gorge.sh` run faster than real time. Field noise, seed 0, no wind, on 2026-11-19
  against the original records (formation: `test_formation_flight.py`, real time, after the world's redesign):

  | flight | separation on the route min / mean / max (m) | clearance in the air v1 / v2 (m) | tracking max v1 / v2 (m) |
  |---|---|---|---|
  | abreast, original | 1.70 / 1.92 / 2.17 | 1.65 / 1.85 | 0.31 / 0.42 |
  | abreast, here (real time, video) | 1.71 / 1.91 / 2.18 | 1.60 / 1.91 | 0.32 / 0.42 |
  | abreast, here (`fly_gorge.sh`, 1.5x) | 1.67 / 1.88 / 2.11 | 1.52 / 1.90 | 0.34 / 0.41 |
  | staggered, original | 2.48 / 2.66 / 2.92 | 1.62 / 1.86 | 0.31 / 0.42 |
  | staggered, here (real time, video) | 2.47 / 2.65 / 2.90 | 1.54 / 1.93 | 0.32 / 0.42 |
  | staggered, here (`fly_gorge.sh`, 1.5x) | 2.53 / 2.74 / 2.97 | 1.47 / 1.93 | 0.34 / 0.42 |

  One X500 (`fly_gorge.sh single`): 12 mission items flown in order, arm to disarm 51.5 s, clearance in the air at least
  1.76 m, tracking error max 0.32 m. The original single-vehicle record predates the world's redesign (11 items, so
  not comparable).
- The cameras are the shared ones: one process for both vehicles, RGB 640 x 480 at 10 fps, thermal 640 x 512 at
  8.7 fps; with two vehicles both RGB streams share the video port (only the active vehicle's is sent; QGroundControl
  switches them). The original single-vehicle launcher used its own camera settings.
- Nothing is written to disk by default (`--record [DIR]` keeps the records); a run's overlays live in a temporary
  directory removed at exit.
- The map tile server is off by default (QGroundControl needs a non-default map setting to use it).
- Removed: the original QGroundControl drivers (`run_qgc.py`, `run_qgc_gorge.py`, which started the application), the
  frozen controller snapshots (`sim/world/snapshot*/`), the air-start camera flight `fly_gorge.py` and the wind study
  that used the snapshot, the formation test series driver, the original launchers, the leanfc copies of the world, the
  airframe meshes and their licenses (now in `sim/`), the generated GIFs of `sim/render/` (about 48 MB; their PNG
  stills are kept), and the Python requirement files (the shared `sim/requirements*.txt` cover them). The two
  formation videos of `gallery/` were re-encoded (H.264, CRF 30) from 22 MB to 3.5 MB each.
- `sim/mavlink/test_services.py` uses pymavlink's bundled ArduPilot dialect unless the dialect generated from the
  MAVLink definitions (`test_codec.py`, needs a MAVLink clone in `MAVLINK_DEFS`) is present.
