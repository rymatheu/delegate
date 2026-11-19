# The gorge world

The procedural gorge, the X500, its sensors and the cameras. The modules import each other by name; importing the
package `sim/gorgesim` puts this directory on `sys.path`. The world came from the Lean-native flight controller's
simulator (`leanfc/`, its `sim/world/`) by way of the ArduLean simulator, which kept only what its flight programs use
and adapted the live camera to poses sent by the flight program; numerics, constants, random seeds and operation order
are unchanged, and the gorge it builds is byte-identical (terrain and hull meshes compared). The QGroundControl plans
are in `sim/plans/`.

| file | what |
|---|---|
| `gorge.py` | the procedural basalt gorge (terrain, walls, boulders, rocks, vegetation, fires, baked RGB and thermal textures) from a seed; `Gorge(seed)` builds it on first use (about 3 minutes, 300 MB) and caches it in `sim/build/world-cache/` (git-ignored) under a key of the seed and this file's source; `Gorge.load` puts it into a PyBullet client (physics, visual or thermal) |
| `fire.py` | flames, smoke and firelight of the fires, drawn per frame in image space |
| `sensors.py` | the onboard RGB camera and the LWIR thermal camera (radiometry, optics, detector, AGC), camera mounts |
| `airframes.py` | the airframe table (the X500's URDF and motor lag), `AirframeAviary` (gym-pybullet-drones CtrlAviary with an external URDF and the lag) |
| `wind.py` | the gorge's wind (mean flow along the axis, Dryden-style gusts), the aerodynamic force on the X500, `WindAviary` |
| `gorge_aviary.py` | `GorgeAviary` (the environment of one vehicle in the gorge, without the package's ground plane) and `FormationAviary` (several vehicles, lag and wind per vehicle); `FCOLS` |
| `geo.py` | the geographic origin (integers, binary32 cosine of latitude) and the NED / latitude-longitude mapping |
| `origin.params` | the origin's ORIGIN line (38.8405556, -105.0441667, 4302 m) |
| `gorge_plan.py` | the X500's rest height on the floor and the gorge mission's plan items |
| `formation_plan.py` | the two formation plans (abreast, staggered): route centre, level start and land sites, the two routes, plan files |
| `render_flight.py` | the vehicle's render model and the propellers' motion blur |
| `render_world.py` | the scene camera (`Scene.shoot`), fonts (DejaVu Sans from Matplotlib) and labels |
| `camera_component.py` | the live camera of the QGroundControl sessions: MAVLink camera component, H.264 encoder and RTP sender (in `sim/.venv-video`; started by `sim/cameras.sh`; `sim/README.md`) |
| `camera_render.py` | its render workers: the forward RGB and thermal cameras of `sensors.py` on the live level of detail, fed one pose per frame (in `sim/.venv`) |
| `render_formation.py` | the cameras split for sharded rendering (`SplitThermal`, `KeepRaw`, `expose`), the two-vehicle frame layout (`Setup`, `Pair`), the H.264 encoder script and `render_sharded` |
| `x500/x500.urdf` | the X500's physics model (Holybro X500 V2 from PX4's Gazebo model; sources in its comment) |
| `x500/x500_render_noprops.urdf`, `x500/x500_meshes/` | the X500's render model: PX4-gazebo-models `x500_base` meshes and texture, BSD 3-Clause, notice in `x500/x500_meshes/LICENSE`; used for drawing only |
