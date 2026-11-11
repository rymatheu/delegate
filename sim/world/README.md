# Gorge world: a windswept mountain gorge with firebrands, for the leanfc test bench

A PyBullet environment in which the X500 flies, with the frozen Lean controller in the loop, up a
narrow procedural rock gorge (layered walls, boulders, vegetation, small spot fires hidden behind
boulders), in a wind channeled by the gorge, carrying a forward RGB camera, a downward RGB camera and
a forward uncooled LWIR thermal camera (FLIR Lepton 3.5 class) whose images are detected for hot spots.
Everything in the world is generated from a seed by the scripts here (see ASSETS.md); the harness of
`sim/run_leanfc.py` (sensors, controller protocol, lock-step loop, X500 model with motor lag) is
imported unmodified.

![overview](out/overview.png)

## Files

| file | lines | concern |
|---|---|---|
| `gorge.py` | 765 | the world: centerline, walls, floor, mesh, textures, boulders, firebrands, temperature classes; loading into a PyBullet client; corridor-clearance check |
| `wind.py` | 145 | mean flow, Dryden-style gusts, aerodynamic force, `WindAviary`; wind-off check |
| `sensors.py` | 348 | camera mounts, RGB camera, thermal camera (radiometry, optics, noise), false color, detection, matching; self-test |
| `fly_gorge.py` | 287 | the closed-loop flight: `GorgeAviary`, mission overlay, contact, clearance, cameras, detections.md |
| `wind_study.py` | 164 | wind flights in steps, metrics, wind.md |
| `render_world.py` | 409 | overview.png, oblique.png, onboard contact sheets, flight.gif |
| `gorge_session.py` | 183 | the gorge as a ground-start, real-time MAVLink session: sim/run_leanfc.py's loop with the gorge world, the vehicle resting on the floor, pose feed for the camera, clearance and real-time record |
| `gorge_plan.py` | 114 | the gorge mission as a QGroundControl `.plan` and as the session's parameter overlay; the rest height at the start |
| `camera_component.py` | 522 | the simulated camera payload: MAVLink component N/100 (`--sysid`, default 1), its answers to QGroundControl, two RTP/H.264 streams (libx264 via PyAV), render worker pool |
| `camera_render.py` | 79 | render worker of the camera (sensors.py's RGB and thermal cameras from the latest pose); the thermal display mapping |
| `tile_server.py` | 216 | XYZ map tiles of the gorge for QGroundControl's CustomURL provider: top-down rendering, georeference, HTTP |
| `geo.py` | 121 | the controller's NED <-> latitude/longitude conversion and QGroundControl's Web Mercator tile arithmetic |
| `fly_gorge_qgc.sh` | 59 | the launcher of the session, camera and tile server |
| `test_camera.py`, `test_tiles.py`, `test_gorge_flight.py`, `run_qgc_gorge.py` | | the camera protocol and stream test, the tile test, the full scripted flight, the real QGroundControl run (`--formation PLAN`: the formation session) |
| `formation_plan.py` | 336 | two vehicles: the plans `abreast` and `staggered` (offset vectors), the routes, plan files and overlays per vehicle, the nominal geometry (clearance, separation, skew); `--sweep`: the offsets study |
| `formation.py` | 533 | two X500s in one world (`FormationAviary`: motor lag and wind per vehicle), two controllers: batch (air start, `--skew`) and the real-time MAVLink session; separation, contacts and clearance every tick; `summarize`; `--self-check` |
| `formation_study.py` | 141 | the batch flights over seeds, wind and skew, and their tables (`out/formation/study/`) |
| `fly_formation_qgc.sh` | 87 | the launcher of the formation session: two vehicles, two cameras, the tile server, the plan files |
| `test_formation_flight.py` | 454 | the scripted two-vehicle flight from the ground (one ground-station link as QGroundControl's), its checks and numbers |
| `formation_tests.py` | 94 | the scripted flights one after the other, and their table (`out/formation/tests/`) |
| `render_formation.py` | 185 | the formation animations: both vehicles from outside, the four onboard views under them |
| `QGC-CAMERA.md` | | what QGroundControl 5.1.5 asks of a MAVLink camera, its streams and a tile server, with the sources |
| `snapshot/` | | the frozen controller `leanfc` and its parameter files (not modified) |
| `assets/` | | generated meshes and textures (rewritten from the seed by every script) |
| `out/` | | evidence: images, GIF, `detections.md`, `wind.md`, `main/` (the camera flight), `runs/` (wind flights) |

## How to run

```
PY=sim/.venv/bin/python
cd sim/world          # from the repository root
$PY -B gorge.py                       # build seed 7, write assets/, print the world summary and corridor clearance
$PY -B sensors.py                     # self-test: texel pass-through of the thermal twin, band radiance, camera cost
$PY -B fly_gorge.py --out out/main    # the camera flight (field noise, no wind): flight.csv/json, cams_*.npz, detections.md
$PY -B fly_gorge.py --wind 4 1 --cameras off --out out/runs/w4   # options: --wind MEAN GUST, --seed, --gorge-seed,
                                      #   --noise none|field, --cameras on|off, --out DIR
$PY -B wind.py out/runs/off/flight.csv   # wind off = run_leanfc physics, bit for bit
$PY -B wind_study.py --jobs 6         # 23 flights -> out/wind.md (--reuse: recompute the report only)
$PY -B render_world.py                # out/overview.png, oblique.png, onboard-rgb.png, onboard-thermal.png, flight.gif
```
`fly_gorge.py` defaults: `--noise field`, `--cameras on`, `--seed 0` (sensor noise, gusts, thermal
noise), `--gorge-seed 7`, no wind. A run takes about 20 s of wall time without cameras and 74 s with
them for the 47 s flight.

## The world (`gorge.py`)

All numbers are for seed 7 and are printed by `python gorge.py`.

- Frame: ENU (PyBullet's), axis toward north from the origin; the flight covers north 0 to 72 m; the
  terrain runs from 12 m south to 92 m north, beyond the flight at both ends.
- Centerline: two sines (wavelengths 55 to 70 m and 24 to 32 m) scaled so that the axis heading stays
  within 22 deg of north (measured: 21.9 deg). The controller snapshot holds the heading north; nothing
  else assumes it (camera mounts are in the body frame, the FOV wedges use the true attitude).
- Floor: width 7.2 m +- 1.3 m of slow noise with two Gaussian narrows (minimum 4.2 and 4.6 m), clipped
  to 4 to 9 m (measured 4.20 to 8.22 m; narrows at N 22.4 and 54.7 m); height rising 3.5 % up the gorge
  plus 0.35 m of noise (2.13 m over the flight), a 0.3 m deep channel across, 0.12 m of 2D noise.
- Walls: horizontal strata 0.8 to 2.6 m thick from 8 m below to 45 m above the origin; 45 % are hard
  (cliff 80 to 88 deg, with a bench 0.3 to 1.2 m wide on top where the layer above is soft), the rest
  soft (65 to 74 deg); bench widths and angles vary along the axis (smooth noise, +-3 deg). Rim 15.5 to
  24.5 m above the floor (west 15.5 to 23.5, east 16.5 to 24.5 m); mean angle toe to rim 68.4 to 73.4
  deg. Roughness: 0.08 m of lateral displacement of the wall vertices.
- Mesh: rows every 0.8 m along the axis; columns across: 13 floor columns, the toe, one column per
  height level on each wall (every stratum top, every bench's outer edge and steps of at most 0.7 m),
  6 plateau columns beyond each rim; offsets are perpendicular to the axis (x shifted by 1/cos of the
  heading), so the grid never folds. Wall columns at constant height make every stratum boundary a mesh
  edge: a first version with columns at fixed horizontal offsets gave sawtoothed strata, because a
  horizontal plane cuts coarse cliff triangles along a zigzag. Levels below the floor edge or above the
  rim of a row collapse onto the toe or rim; the zero-area faces are dropped: 26,343 triangles.
  Physics: one static body, `GEOM_MESH` with `GEOM_FORCE_CONCAVE_TRIMESH`, loaded from the OBJ (PyBullet
  refuses this mesh as an inline vertex list: "createCollisionShape failed").
- Texture (1536 x 1024): each texel is colored from the 3D point it covers, interpolated on the mesh's
  own triangles: stratum color by height (six sandstone and limestone tones), a dark line under each
  stratum top, noise and vertical varnish streaks; gravel floor; vegetation where noise exceeds a
  threshold that falls toward the floor edges, on benches (normal z > 0.8) and in patches on the
  plateau; dry grass on the plateau. Cast shadows are baked in (texel color x 0.62 where a ray toward the
  sun hits terrain or a boulder; 1.57 million ray tests; the whole build takes 3.6 s).
- Sun: azimuth 225 deg (south-west), elevation 55 deg; the same direction lights TinyRenderer.
- Boulders: 23, deformed icospheres (320 faces, radial noise 22 %, flattened vertically to 0.65 to
  0.95, random yaw), sunk 8 % into the ground; seven large ones (1.7 to 2.5 m) are placed first at
  stations every 8.5 m, then smaller ones (0.5 to 1.7 m); 45 % against a wall. A boulder is rejected if
  it overlaps another or if any vertex within 1.75 m (horizontally) of the flight path rises above 2.5 m
  over the floor (corridor margin 0.5 m). Physics: static convex hulls.
- Flight corridor, verified on the collision geometry (closest points of a 1 cm probe sphere,
  `Gorge.corridor_clearance`): the planned path at 3.5 m above the floor stays at least 1.89 m from
  terrain and boulders; the corridor box (+-1.25 m across the path, 3.0 to 4.0 m above the floor,
  sampled every 0.5 m along) at least 1.29 m.
- Data exposed by `Gorge`: `y, xc, theta, width, floor0, height[side]` (per row), `xc_fn`, `floor_c(y)`,
  `width_at(y)`, `axis_dir(y)`, `lateral(x, y)`, `rim_xi`, `rim_z`, `grid` (mesh vertices per row and
  column), `path` (waypoints) and `path_points`, `boulders` (center, size, height, top, vertices, faces,
  wall), `firebrands` (center, radius, temp_c, hidden, boulder, pieces), `texel_class` and
  `texel_temp_k` (per terrain texel), `CLASSES` (temperature classes), `ground_z(xy)`, `rays(a, b)`,
  `visibility(k, pts)`, `load(client, "physics"|"visual"|"thermal")` returning `{body id: (class,
  index)}` with classes terrain, boulder, ash, ember.

Temperature classes (deg C; a surface's temperature is shade + (sun - shade) x cos(incidence) x lit,
lit from the baked sun ray test, plus about 1 K of spatial noise):

| class | shade | full sun | emissivity | reason (assumption) |
|---|---|---|---|---|
| floor (gravel, sand) | 29 | 47 | 0.93 | dry mineral surface, air 30 C |
| rock (walls, boulders) | 28 | 50 | 0.93 | sunlit rock 15 to 25 K above air |
| vegetation | 27 | 32 | 0.97 | transpiring leaves stay near air temperature |
| plateau (dry grass, scrub) | 30 | 44 | 0.95 | |
| ash bed under a fire | 150 | 150 | 0.95 | smoldering ground around a spot fire |
| ember | per piece, 0.9 to 1.0 x the fire's temperature (600 to 900) | | 0.90 | glowing char |
| sky | brightness temperature 30 C at the horizon, 50 K colder at the zenith (by sin elevation) | | 1 | clear sky |

## Firebrands: how they are built, drawn and seen

- Geometry (`Gorge._firebrands`, `_add_fire`, `fire_meshes`): 8 spot fires. Each is a disk of ash
  (16-sided fan, radius 0.15 to 0.35 m, the fire's size, its rim draped 1.5 cm over the ground by ray
  tests) and 7 to 12 ember pieces (icospheres of 80 faces, radius 2.5 to 6 cm, deformed and flattened to
  0.4 to 0.7 of their width, half buried, scattered within 0.8 of the disk radius). The fire's
  temperature is drawn in 600 to 900 C; the hottest piece has it, the others 0.9 to 1.0 times it. Two
  PyBullet bodies per fire: the ash body and the ember body (visual only, no collision).
- Placement: 6 hidden, 2 open. A hidden fire sits just beyond a boulder at least 0.9 m tall, on the line
  from a point 8, 12 or 16 m back along the flight path through the boulder's center, 0.1 m clear of the
  boulder; it is kept only if it lies on the floor, clear of other boulders and 3 m from other fires,
  and its hottest piece is out of sight (ray tests against terrain and boulders) from at least 80 % of
  the path points 3 to 20 m before it. An open fire is in sight from at least 80 % of the path points
  3 to 25 m before it.
- Visual drawing: the ash uses a dark char color (38, 34, 32); each ember piece's texel gets a display
  color interpolated between two hand-chosen control points, dull red (190, 45, 12) at 600 C and
  orange-yellow (255, 165, 40) at 900 C (not a measured blackbody color). TinyRenderer would shade the
  embers like any surface, so after rendering, `sensors.glow` sets every pixel whose segmentation is an
  ember body to the fire's emission color (unlit) and adds a Gaussian bloom of those pixels (sigma 1 px
  at 320 px width, weight 1.6; in the overview sigma 2 px, weight 5, so that 3 to 6 cm embers show at
  3 cm per pixel). The bloom is computed from the rendered segmentation, so an ember behind a boulder
  gets no glow. The orange rings in the overview are annotations.
- Thermal: the thermal twin of the world gives the ash and every ember piece its own texel holding its
  temperature and emissivity; they enter the radiometric chain like every other surface (band radiance,
  emissivity, atmosphere, pixel average, PSF, noise, saturation). Occlusion comes from the rendering
  only. No flame, smoke or plume is modeled.

## Wind (`wind.py`)

- Mean flow along the local axis; `--wind MEAN GUST`, MEAN > 0 up-gorge (north: a daytime up-valley
  wind, a tailwind for the vehicle), MEAN < 0 down-gorge. MEAN is the speed 3.5 m above the floor where
  the floor has the median width (6.44 m). Speed = |MEAN| x min(6.44 / W(y), 2) (continuity at constant
  depth, capped) x ln((h + 0.1)/0.1) / ln(3.6/0.1) (log profile over a rough floor, z0 = 0.1 m; the
  factor capped at 1.6). In the narrowest section the mean is 1.53 x MEAN.
- Gusts: three first-order shaping filters on seeded white noise (along, across, vertical), discrete
  exact update at 1200 Hz with stationary standard deviation sigma and correlation length L at the
  advection speed max(local mean, 1 m/s). L_u = 26 m and L_w = 3.5 m from the MIL-F-8785C low-altitude
  formulas at 3.5 m (11.5 ft); L_v = min(26 m, local width) (assumption: no cross-gorge eddy larger than
  the gorge); sigma_u = sigma_v = GUST, sigma_w = GUST / 1.96 (MIL-F-8785C ratio at 11.5 ft). The default
  study case is 4 m/s with GUST = 1 m/s; the steps use GUST = 0.25 x MEAN.
- Force on the vehicle from the air-relative velocity v - w: rotor drag of the gz MulticopterMotorModel
  that PX4's X500 model uses, -C_R sum|omega_i| v_perp (rotor-plane component), C_R = 8.06428e-05
  N/(m/s)/(rad/s) (PX4-gazebo-models x500/model.sdf rotorDragCoefficient), with the rotor speeds of the
  lagged thrust (omega = sqrt(T / 8.54858e-06)); at hover 4 x C_R x 769 rad/s = 0.248 N/(m/s). Plus body
  drag -1/2 rho CdA |v_rel| v_rel with rho = 1.16 kg/m^3 (30 C, 1000 hPa) and CdA = 0.04 m^2 (assumption:
  about 0.035 m^2 frontal area of plates, battery, arms, motors and legs, Cd about 1.1), isotropic, at
  the center of mass, no moment.
- Applied in `WindAviary._physics` (1200 Hz, after run_leanfc's motor lag and thrust) with
  `applyExternalForce` at the base. Wind off (no `--wind`): no force at all. Check: the 18,881 motor
  commands of the wind-off gorge flight replayed through run_leanfc's own `make_env` and through
  `GorgeAviary` give a maximum state difference of exactly 0.0 (`python wind.py`).

## The flight (`fly_gorge.py`)

- Mission overlay (`OUT/mission.params`, after the snapshot's x500.params and, for `--noise none`,
  mocap.params): start hovering at the first waypoint (north 0, 3.5 m above the floor), heading north,
  then 9 waypoints along the centerline 3.5 m above the floor; `nav.vMax 2.0`, `nav.aMax 2.0`,
  `nav.radius 0.2`, `nav.lagMax 0.6` (x500 values, restated). Spacing: the navigator stops at every
  waypoint (1 s to accelerate and 1 s to brake at 2 m/s^2, 1 m each), so legs are as long as possible:
  at most 10 m and with the centerline within 0.35 m of each chord: 9 legs of 6.7 to 10.0 m, path 73.3
  m. Nominal time sum(L/2 + 1) = 45.6 s, of which the stops cost 9 s (25 %); flown: all waypoints
  reached at 45.2 s.
- Sensors: run_leanfc's `Sensors` and `Noise` (`field`: 10 Hz GPS-like fixes, the field profile;
  `none`: zero noise and 100 Hz fixes). Physics as run_leanfc (1200 Hz, motor lag 12.5/25 ms).
- Contact: after every tick `getContactPoints` of the vehicle; any contact ends the run with time,
  body class, position, depth, normal force and speed in flight.json. Clearance: `getClosestPoints`
  from the vehicle's collision cylinder (radius 0.25 m, 0.22 m tall) to the terrain and every boulder,
  up to 4 m, every tick (CSV column `clearance`).
- The run ends 2 s after the last waypoint, or at the time limit 2 x nominal + 10 s (101 s).
- Cameras (`--cameras on`) render from the true pose after each tick's physics, in two extra PyBullet
  clients (visual world, thermal twin), at their own rates; they do not feed the controller.

## Sensors (`sensors.py`)

- Mounts (body FLU): FORWARD at (0.20, 0, -0.03) m, 30 deg below the nose; DOWN at (0, 0, -0.10) m
  looking straight down, image top = forward. Neither sees the airframe (the vehicle is not in the
  rendering clients).
- RGB camera: 320 x 240, 90 deg horizontal FOV, 10 Hz, near 0.05 m, far 200 m; TinyRenderer with
  diffuse light from the sun direction; sky pixels (segmentation -1) painted with a gradient; ember glow;
  returns RGB, depth in meters (linearized: z = far near / (far - (far - near) d)) and segmentation.
- Thermal camera, FLIR Lepton 3.5 class (Lepton 3.5 datasheet values): 160 x 120, 57 deg HFOV
  (44.3 deg vertical), 8.7 Hz, NETD 50 mK (used in low gain too, where it is likely optimistic),
  low-gain saturation at 400 C (datasheet: up to 400 C, typically 450 C), 8 to 14 um band. PSF: Gaussian,
  sigma 0.5 px (diffraction of an f/1.1 lens at 10 um gives 0.39 px at 12 um pitch; rounded up for
  aberrations, an assumption).
- Radiometry (per frame): render the thermal twin at 4 x 4 samples per pixel (640 x 480) with lighting
  reduced to the ambient term at 1, so each sample returns its texel exactly (check: 100.000 % of
  307,200 surface samples equal a texel); decode temperature and emissivity; sky by elevation; band
  radiance by Planck's law integrated over 8 to 14 um (600-point trapezoid, tabulated every 0.05 K from
  150 to 1800 K); L = tau [e L(T) + (1 - e) L(T_air)] + (1 - tau) L(T_air), tau = exp(-4e-4 r) (0.96 at
  100 m, an assumption for humid air); mean of the 16 samples per pixel (sub-pixel fill); PSF; white
  noise of NETD in radiance at 30 C; clip at L(400 C); invert to apparent (brightness) temperature with
  emissivity 1. Outputs: radiometric image in C (float), false color with a fixed 20 to 100 C scale, and
  an automatic-gain version (histogram equalization). Palette: seven control points (black, violet,
  magenta, red, orange, yellow, near white).
- Why not T^4: the 8 to 14 um band holds 37.8 % of the total radiance at 30 C but 14.0 % at 600 C and
  7.5 % at 900 C, so T^4 overstates the contrast of a 600 C ember over 30 C rock by 2.7 x and of a 900 C
  ember by 5.0 x. With the band integral, an ember lifts a 30 C pixel by the 40 K detection margin at a
  fill fraction of 2.87 % (600 C) or 1.62 % (900 C).
- Detection: hot pixels above the frame median + 40 K; connected groups; each placed in the world from
  its hottest pixel's bearing and the range of that pixel's hottest sample; matched to the nearest
  firebrand within 1.5 m, otherwise a false positive.
- Rendering cost per frame (main flight, 473 / 473 / 411 frames, measured in the run): forward RGB 20.8
  ms, downward RGB 19.6 ms, thermal 84.4 ms (max 24.3, 27.7, 136.5 ms). What limits it: TinyRenderer is
  a single-threaded CPU rasterizer whose cost grows with the pixel count (`getCameraImage` with the
  whole world: 8.6 ms at 320 x 240, 32.3 ms at 640 x 480, 134 ms at 1280 x 960; with an empty scene
  3.1, 14.2 and 72.6 ms, so buffer clearing, readback and the conversion to Python lists are about half
  of it); the 34k triangles add the other half. The thermal frame is 32 ms of rendering at 4 x 4
  supersampling plus about 52 ms of NumPy radiometry on 307,200 samples. With cameras the 47 s flight
  takes 74 s of wall time (20 s without). 8 x 8 supersampling would cost about 134 ms of rendering alone.

## Results (seed 7, field noise seed 0)

- Flight without wind: completed in 47.2 s; path error max 0.14 m, rms 0.06 m; minimum clearance 1.67 m
  (north 25.6 m, first narrows); tilt max 22.5 deg; motors 0.282 to 0.953, no saturation. With
  `--noise none`: path error max 0.024 m, clearance 1.64 m.
- Thermal detection (`out/detections.md`, the camera flight): all 8 firebrands detected, no false
  positive in 411 frames. The two open fires are detected in the first frame they enter the image, at
  30.4 and 22.6 m: their range is limited by the line of sight down the meandering gorge, not by
  resolution (at 30.4 m the best pixel had an ember fill of 0.375 and read 232 C). The six hidden fires
  enter the image, and are detected, only at 4.2 to 5.9 m, when the vehicle is nearly over the boulder;
  two of them (fires 2 and 4) are first detected from their hot ash bed alone (ember fill 0, 122 C), and
  fire 4's embers are never seen at all. Embers seen at close range saturate at 400 C.
- Wind (`out/wind.md`, 23 flights): with 4 m/s and gusts of 1 m/s either way the flight is unchanged
  (path error 0.14 to 0.15 m). The mission completes up to a mean of 9 m/s in both directions (13.8 m/s
  in the narrows). From 10 m/s the vehicle holds about 0.5 m downwind of a waypoint in a narrows and
  waits there for a gust to carry its estimate inside `nav.radius` 0.2 m. Measured at -10 m/s: a
  horizontal aerodynamic force of 4.26 m/s^2 per unit mass against the velocity integrator's limit
  iMax = 1 m/s^2 needs a steady error of (4.26 - 1) / (1.5 x 4) = 0.54 m; the measured mean is 0.70 m true
  and 0.66 m estimated. It holds within 3 m of its waypoint up to 12 m/s up-gorge (18.4 m/s in the
  narrows) and 11 m/s down-gorge (16.9 m/s). Up-gorge at 14 and 16 m/s it is pushed 8 to 11 m past its
  waypoint; at 16 m/s it comes within 0.23 m of the west wall (north 29.3 m, 3.1 m above the floor) with 12 saturated ticks. At 18 and 20 m/s up-gorge it hits
  the wall (terrain contact at north 28.5 and 49.1 m). Down-gorge at 18 and 20 m/s it is blown back down
  the gorge, 40 and 230 m from its waypoint at the time limit.

## The gorge with QGroundControl: session, camera payload, map (`fly_gorge_qgc.sh`)

```
sh sim/world/fly_gorge_qgc.sh                                   # then open QGroundControl (sim/mavlink/QGC.md)
sim/world/.venv-video/bin/python sim/world/test_camera.py        # camera protocol and both streams
$PY -B sim/world/test_tiles.py                                   # tiles and their georeference
$PY -B sim/world/test_gorge_flight.py --seed 0                   # a full scripted flight, video on
sim/mavlink/.venv/bin/python sim/world/run_qgc_gorge.py --seconds 90 [--home $(mktemp -d)]   # the real QGroundControl
```

- Session (`gorge_session.py`): sim/run_leanfc.py's loop and options with the gorge world in place of
  the ground plane, current build and parameter files (not the snapshot), `--ground --mav --realtime 1
  --trace-vehicle`; the X500 rests on the floor at the first waypoint (its base 5 mm above the highest
  ground point under its collision disc plus its rest height, then settled); the controller's onboard
  mission is the gorge route; wind with `WIND="MEAN GUST"` (wind.py; gust seed = noise seed + 1000).
- Camera payload (`camera_component.py`, `camera_render.py`): the forward RGB camera of sensors.py at
  640 x 480, 90 deg, 15 fps (two render workers, about 90 ms per frame each) and the forward thermal
  camera at its native 160 x 120, 57 deg, 8.7 fps (one worker, about 90 ms), libx264 constrained baseline,
  a keyframe every second; thermal display: apparent temperature 20 C (black) to 80 C (near white)
  through sensors.PALETTE. The workers render from the newest pose of the 100 Hz feed.
- Map (`tile_server.py`): a top-down rendering of the generated world at 1.5 cm per pixel (4648 x 6934
  pixels, built in about 8 s at start), served at zoom 0 to 23 through the controller's own flat-earth
  conversion and QGroundControl's Web Mercator arithmetic; everything outside the terrain is the uniform
  color (138, 132, 118).

Results (outputs in `out/test-camera/`, `out/test-tiles/`, `out/test-flight/`, `out/qgc-real*/`):

- **Camera protocol** (`test_camera.py`, a pymavlink ground station replaying QGroundControl 5.1.5's
  discovery with its timeouts): 22 of 22 protocol steps pass: heartbeat (type CAMERA, 1.00 Hz), each
  request answered by COMMAND_ACK ACCEPTED within 0.3 ms and then its message (both forms of every
  request), CAMERA_FOV_STATUS refused, an unknown command refused, a command for the autopilot ignored,
  every frame valid for pymavlink.
- **Streams** (FFmpeg's own RTP demuxer and H.264 decoder via PyAV, 20 s): both decodable from the first
  keyframe (the first decoded frame is the first keyframe's; 6 and 4 packets before it; no decode error
  after it); RGB 640 x 480 at 15.02 fps, thermal 160 x 120 at 8.70 fps, no slot dropped, no packet lost;
  frames saved as PNG (`out/test-camera/*-frame*.png`). Latency from the pose's time stamp to the decoded
  frame, with a marker-bit depacketizer (as GStreamer's rtph264depay) and FFmpeg's decoder: RGB mean 97 ms
  (p95 113, max 119), thermal mean 98 ms (p95 107, max 111), of which the render and encode take 89 and
  90 ms, the pose's age at the frame's slot 8 ms and the network and decoding 0.3 ms; through FFmpeg's RTP
  demuxer, whose parser holds each frame until the next one starts, 169 and 214 ms. QGroundControl adds
  its jitter buffer (80 ms by default) and its display.
- **Tiles** (`test_tiles.py`): 15 of 15: every zoom 0 to 23 answers a 256 x 256 PNG (4.6 ms mean per
  fetch), the background far away, 404 above 23; the georeference against QGroundControl's tile
  arithmetic: a 2.5 m boulder 0.72 cm off at zoom 23 (1.45 cm pixels) and 1.49 cm at zoom 21, a
  firebrand's embers 0.96 and 1.79 cm (open and hidden fire) at zoom 23, the ash beds 1.8 to 3.0 cm, the
  start 0.00 cm and the landing point 0.10 cm through the controller's integer latitude and longitude;
  mosaics `out/test-tiles/mosaic-z20.png` (the whole gorge) and `mosaic-z23-firebrand3.png`.
- **A full flight** (`test_gorge_flight.py --seed 0`: field noise, no wind, video on): 8 of 8: ready to
  fly 2.8 s after the first heartbeat; the plan uploaded (MISSION_ACK ACCEPTED); Start Mission from the
  ground as QGroundControl does it; landed states ON_GROUND, TAKEOFF, IN_AIR, LANDING, ON_GROUND;
  MISSION_CURRENT and MISSION_ITEM_REACHED 1 to 11 in order; landed and disarmed 51.7 s after the arm;
  no contact in the air. Tracking error (vehicle to target) max 0.37 m, rms 0.16 m; distance to the
  planned route max 0.33 m, rms 0.14 m; clearance to terrain and boulders in the air at least 1.69 m
  (37.8 s in the air); tilt at most 17.6 deg, motors 0.156 to 0.845, no saturation, ground speed at most
  2.28 m/s; touchdown at 0.49 m/s on the floor 2.19 m above home, 0.15 m from the land item, 1.8 deg of
  tilt after the disarm. Real time: 59.0 s simulated in 59.0 s, every 1 s window at least 0.9987, at
  most 12 ms behind the wall clock. Video during the flight: 912 RGB frames at 15.00 fps and 529 thermal
  frames at 8.70 fps sent, and the same numbers received on 5600 and 5602; no slot dropped. With wind
  (`--seed 1 --wind 4 1`, `out/test-flight-w4-s1/`): 8 of 8, tracking max 0.26 m, route max 0.29 m,
  clearance at least 1.67 m, tilt at most 20.1 deg, no saturation, touchdown 0.50 m/s, 0.12 m from the land
  item; real-time factor 1.000, one 1 s window at 0.968 (at most 34 ms behind the wall clock).
- **A smaller RGB stream** (`RGB=320x240@20 RGB_WORKERS=1`, `test_camera.py --rgb 320x240@20 --rgb-workers 1`):
  32 of 32, 19.99 fps decoded, render 22.9 ms, pose to decoded frame 31 ms mean (38.7 at most).
- **The real QGroundControl 5.1.5** (`run_qgc_gorge.py --seconds 90`, nothing clicked; `out/qgc-real-fresh/`
  with a fresh settings directory, `out/qgc-real/` with the user's): camera heartbeat 1.0 s after "Initial
  load complete", CAMERA_INFORMATION in the same millisecond, the streams 1.0 s later, then "New Video
  Source: UDP h.264 Video Stream", both receivers started, the main one decoding 640 x 480 (decoder
  vtdec_hw, QGroundControl's choice) 0.24 s after the stream information and the thermal one 160 x 120
  0.52 s after; QGroundControl's sink delivered 1200 RGB frames in 80 s and 600 thermal frames in 69 s,
  none dropped, no receiver timeout. The simulation kept real time with QGroundControl, the camera and
  the tile server running: 98.7 s simulated in 98.7 s, every second at least 0.9988, at most 42 ms behind.
  The camera's render time rose to 91 ms mean and 191 to 203 ms at most (still no slot dropped).
  QGroundControl wrote `[Video] videoSource=UDP h.264 Video Stream` into its settings by itself; nothing
  else of ours. The map setting was not tried in the application (it would be a GUI action).

## Two vehicles in formation (`formation*.py`, `fly_formation_qgc.sh`)

![abreast](out/formation-abreast-still.png)
![staggered](out/formation-staggered-still.png)

Animations: `out/formation-abreast.gif` and `out/formation-staggered.gif` (WebP beside them; the frames
in `out/formation-abreast-frames/`, `out/formation-staggered-frames/`): the two X500s from a chase camera
behind the pair, and under it vehicle 1's forward RGB and thermal views and vehicle 2's, which in the
staggered plan look behind the formation. Field noise, seed 0, no wind (the batch flights
`out/formation/study/abreast-field-s0-off` and `staggered-field-s0-off`).

```
PY=sim/.venv/bin/python
cd sim/world          # from the repository root
$PY -B formation_plan.py --sweep                                # the offsets study (nominal geometry)
$PY -B formation_plan.py                                        # plan files and overlays -> out/formation/plans/
$PY -B formation.py --self-check                                # FormationAviary with 1 vehicle = GorgeAviary, bit for bit
$PY -B formation.py --plan staggered --noise none --out out/formation/runs/staggered-det   # deterministic
$PY -B formation.py --plan abreast --seed 3 --wind 6 2 --skew -1.25 --out DIR               # one batch flight
$PY -B formation_study.py --set all --jobs 8                    # 82 batch flights -> out/formation/study/study-all.md
$PY -B formation_study.py --set skew --plans staggered --skews -0.5 -0.75 -1.25 -1.5 -1.75 -2.5 --tag skew-fine
$PY -B render_formation.py --run out/formation/study/staggered-field-s0-off              # out/formation-staggered.*
PLAN=staggered sh fly_formation_qgc.sh                          # the real-time session for QGroundControl
$PY -B test_formation_flight.py --plan staggered --seed 0 [--wind 6 2] [--skew -2] [--start mv]
$PY -B formation_tests.py --set all                             # 30 scripted flights -> out/formation/tests/tests-all.md
sim/mavlink/.venv/bin/python run_qgc_gorge.py --formation staggered --home "$(mktemp -d)" --out out/formation/qgc-real
```

### Design

- **No link between the vehicles, no follow mode.** Each vehicle has its own unchanged controller
  (`.lake/build/bin/leanfc`, MAVLink systems 1 and 2) and its own mission. Vehicle 2's route is vehicle
  1's plus one constant offset vector, so both navigators fly the same speed profile (same leg lengths,
  curvatures and slopes) and the nominal offset stays constant: in the deterministic flights the centre
  distance is 1.8002 to 1.8003 m (abreast) along the whole route.
- **Offsets** (`formation_plan.PLANS`), in the frame of the gorge's mean direction (the chord from the
  first to the last waypoint, 0.5 deg east of north at seed 7: "lateral" is to its right, about east):
  - `abreast`: lateral 1.8 m, along 0. Both noses forward. Offset ENU (+1.800, -0.016, -0.028) m,
    centre distance 1.800 m.
  - `staggered`: lateral 2.2 m, along -1.8 m (vehicle 2 behind). Vehicle 2 flies with `nav.yawReverse 1`,
    nose against the direction of travel, so its camera looks behind the formation. Offset ENU
    (+2.184, -1.820, +0.086) m, centre distance 2.844 m.

  The vertical component is not chosen: it is the difference of the two rest heights at the start points
  (a plan's altitudes are relative to each vehicle's own home on the floor), so that both takeoff items
  have the same relative altitude and both climbs take the same time. Without it the vehicle on lower
  ground would climb longer and start its route late.
- **Level start sites: what broke the synchronization.** The first scripted flights from the ground
  (abreast, seeds 0 and 1) started vehicle 2's route 4.7 and 5.4 s after vehicle 1's, although both took
  off within 0.05 s of each other and climbed the same height, so the pair flew 8 to 11 m apart along the
  gorge. Cause: vehicle 2 rested on the floor's slope at 4.4 deg, while a ground start calibrates and
  starts the estimator level (`Controller.initAt` with `levelQuat`); at liftoff its estimate still read
  2.1 deg, and the 2.3 deg error pushed it 0.5 m east during the climb. The takeoff item ends when the
  estimate is within `nav.radius` (0.2 m) of its top, so the target waited there 4.9 s for the vehicle to
  come back. The single vehicle's start (the centerline at north 0) is nearly level, the two offset
  points beside it are not (abreast 1.1 and 4.4 deg, staggered 3.2 and 5.6 deg). So the route's first
  point (both vehicles' takeoff column, the offset unchanged) is moved to level ground
  (`formation_plan.level_start`: within 3 m back and 1 m across the axis, ranked by a plane fit to the
  floor, the best 12 settled in PyBullet): 2.5 m back and 0.75 m to the right (east) for abreast,
  settled tilts 0.81 and 0.68 deg; 1.5 m back and 0.25 m to the right for staggered, 1.28 and 0.60 deg.
  The same at the end: the floor under the routes' last points slopes by 5 to 12 deg, and in the first
  flights both vehicles slid on touchdown toward the channel between them, by up to 0.45 m (abreast:
  the closest approach of the flight, 1.10 to 1.24 m, came after touchdown). The plan's NAV_LAND item
  has its own location, so each vehicle lands on a level site within 4 m ahead of and 1 m across its own
  last point, the two at least the offset apart (`formation_plan.land_sites`; settled tilts abreast 1.73
  and 0.75 deg, 3.87 m apart; staggered 1.05 and 2.15 deg, 4.27 m apart). The routes are unchanged.
- **Why mostly lateral.** The two routes are parallel curves 1.8 m (abreast) apart; if one vehicle runs
  ahead of or behind its nominal place by s m of path (a start-time skew), the distance between them is
  the distance between the curves, not less: over every s from -30 to +30 m it stays at least 1.68 m for
  abreast (`formation_plan.skew_distance`). For staggered the along-track component is cancelled when
  vehicle 2 gets about 2.5 m of path ahead of its place (it starts early); there the lateral component
  alone separates the curves, and since the axis turns by up to 22 deg and the offset is fixed, the
  closest the curves come is 1.42 m. The first choice, lateral 2.0 m and along -2.0 m (2.83 m), had
  1.16 m there, and a noisy flight with vehicle 2 starting 1.25 s early came to 0.99 m
  (`out/formation/study-staggered-2.0/`), so the lateral component was raised to 2.2 m at about the same
  centre distance.
- **Route centre.** The pair is centered on the gorge route (3.5 m above the floor on the centerline).
  Re-centering each waypoint to balance the two vehicles' clearances (`--sweep`) raised the smaller
  nominal clearance of abreast from 1.57 to 1.63 m and lowered it for staggered, so it is not used. The
  nominal clearances (vehicle level, the X500's collision cylinder, every 0.2 m of the routes): abreast
  1.57 m (vehicle 1, north 25.2 m, the first narrows) and 1.85 m; staggered 1.56 m and 1.85 m. The gorge is
  wide enough at the flight height that every candidate from 1.5 to 2.5 m lateral kept both clearances
  above 1.5 m; no wider gorge variant was needed and the world is unchanged.
- **The rear vehicle's heading.** Both vehicles start nose north (a batch start's estimator assumes the
  identity attitude; a ground start levels at the heading fix). With `nav.yawReverse 1` the heading
  target becomes the reversed direction of travel as soon as the target moves horizontally, and the
  setpoint turns 180 deg at 60 deg/s with 60 deg/s^2 at the start of the first leg (during the vertical
  takeoff climb the heading is held). In every flight it is within 5 deg of the reversed direction 3.2 to
  3.6 s into the route, at north 2.8 to 3.6 m, long before the first narrows (north 22.4 m).
- **The world** (`formation.py`): one gym-pybullet-drones world (`Physics.PYB`, 1200 Hz under the 400 Hz
  control step) with the gorge's collision bodies and both X500s. `FormationAviary` keeps the motor lag
  and the wind per vehicle (LeanfcAviary and WindAviary keep one state per aviary, right for one vehicle
  only); with one vehicle it is GorgeAviary bit for bit, with and without wind (`--self-check`). Each
  vehicle has its own sensor noise (vehicle 2: seed + 100) and its own gust process (seeds + 1000 and
  + 1100): the gusts at the two vehicles are uncorrelated, which overstates their relative motion (at
  1.8 to 2.8 m apart, with gust lengths of 3.5 to 26 m, real gusts would be largely shared).
- **Not modeled: any aerodynamic interaction between the vehicles.** `Physics.PYB` applies thrust and drag
  torque only; the package's downwash model (`Physics.PYB_DW`) is not used, the X500 URDF's downwash
  coefficients are zero, and wind.py's force does not depend on the other vehicle. The vehicles meet only
  through contact of their collision cylinders (radius 0.25 m, 0.22 m tall), which needs a centre
  distance below 0.5 m; the rotor tips reach 0.386 m from the centre, so real rotor discs would touch below
  0.77 m. They fly at the same height (the vertical offset is under 0.1 m), so neither is in the other's
  downwash in the model or, at these distances and with no vertical offset, much in reality; that is an
  assumption, not a measurement.
- **Measured from the simulator, every tick** (`out/.../formation.csv`): the centre distance, the closest
  distance between the two collision bodies, the contact points vehicle-vehicle and vehicle-world, and
  each vehicle's clearance (closest distance of its collision body to terrain and boulders, as
  fly_gorge.py measures it; in the real-time session every 4th tick, where the terrain query costs
  0.32 ms per vehicle).

### Batch flights (no MAVLink, deterministic, as fast as possible)

`formation.py` without `--session`: both vehicles start in the air, hovering at their routes' first
points (the controller's batch start), and fly their routes as SPLINE legs. `--skew S` starts vehicle 2
S s after vehicle 1 (S < 0: before); the vehicle that waits is held at its start point and its
controller and sensors start at its start. A run ends 2 s after both routes are complete or at any
contact. Each flight takes about 50 s of wall time for 40 s simulated with 8 at a time
(`out/formation/study/study-all.md`, every row; `study-skew-fine.md`).

| plan | flights | distance on the route min / max m | abs(d - nominal) max m (p95 max) | body gap min m | contacts | clearance min m | tracking max m |
|---|---|---|---|---:|---:|---:|---:|
| abreast, deterministic | 1 | 1.8002 / 1.8003 | 0.0001 | 1.30 | 0 | 1.57 | 0.06 |
| abreast, field noise, seeds 0-4, wind off, 4 1, 6 2, -6 2 | 20 | 1.37 / 2.17 | 0.43 (0.38) | 0.86 | 0 | 1.52 | 0.59 |
| staggered, deterministic | 1 | 2.80 / 2.85 | 0.04 | 2.28 | 0 | 1.56 | 0.06 |
| staggered, field noise, seeds 0-4, wind off, 4 1, 6 2, -6 2 | 20 | 2.53 / 3.17 | 0.33 (0.28) | 1.98 | 0 | 1.51 | 0.52 |

All 42 completed. The band: in every noisy flight the distance stayed within 0.43 m of nominal along the
route (abreast) and 0.33 m (staggered), 95 % of the time within 0.38 and 0.28 m. Per wind: abreast min 1.50
m without wind and with 4 1, 1.43 m with 6 2, 1.37 m with -6 2 (down-gorge); staggered 2.59, 2.58, 2.58,
2.53 m. The deterministic staggered flight dips to 2.80 m during vehicle 2's 180 deg turn. No motor
saturated. The rear vehicle's heading against the reversed direction of travel, after its turn: 95th
percentile at most 5.7 deg, rms at most 3.0 deg (0.5 deg 95th percentile deterministic); the maxima,
11 to 24 deg in five flights, all fall in the last half second of the route, where the vehicle brakes to
its final stop and its speed falls through the 0.5 m/s below which the direction of travel is not
measured (the direction of a slow, noisy velocity, not a turn of the vehicle). The forward-facing
vehicles' heading against their direction of travel has a 95th percentile of at most 5.9 deg.

**Start-time skew** (field noise, seed 0, without wind and with 6 2; the smallest centre distance over the
whole flight, the smaller of the two winds):

| vehicle 2 starts ... s after vehicle 1 | -10 | -5 | -3 | -2.5 | -2 | -1.75 | -1.5 | -1.25 | -1 | -0.75 | -0.5 | +1 | +2 | +3 | +5 | +10 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| abreast | 1.79 | 1.79 | 1.76 | – | 1.72 | – | – | – | 1.65 | – | – | 1.66 | 1.62 | 1.70 | 1.76 | 1.70 |
| staggered | 2.40 | 2.37 | 2.39 | 2.32 | 2.00 | 1.64 | 1.38 | **1.26** | 1.31 | 1.54 | 1.89 | 2.80 | 2.83 | 2.84 | 2.84 | 2.84 |

No contact in any of the 52 skew flights, all completed. Abreast never comes below 1.62 m whatever the
skew: a late or early vehicle only moves along its own curve. Staggered never comes below 1.26 m (vehicle
2 starting 1.25 s early: it has reached cruise speed about 2.5 m of path ahead of its place, where the
along-track offset is cancelled); a late vehicle 2 only falls further behind (its own route keeps it
2.2 m to the side). So in the batch flights both plans stay above 1.0 m for every skew tried, from -10 to
+10 s, and the staggered plan's margin is smallest for vehicle 2 starting 1 to 1.5 s early.

## Not modeled

- Smoke and flame as participating media (absorption, emission and scattering in the visible and the
  LWIR), the fire's plume, buoyant updrafts and flame radiation onto the walls.
- Heat transfer of any kind: fires do not heat the ground or vegetation, do not spread, embers do not
  cool; temperatures are static per run (no diurnal cycle, no thermal inertia).
- Airborne embers (the optional wind-advected particles were not implemented), rotor wash on embers,
  ash or vegetation.
- CFD-resolved wind: no separation, recirculation behind boulders, wall shear layers, wake of the
  vehicle or ground effect; gusts are a function of time at the vehicle only (no spatial gust field),
  the cross-gorge component does not vanish at the walls; the drag force has no moment.
- Terrain-induced GPS degradation (multipath, satellite masking by the walls), barometer errors from
  wind, magnetometer disturbance by rock; the sensor model is run_leanfc's, unchanged.
- The visual renderer's lack of global illumination, soft shadows, specular reflection, atmospheric
  haze, motion blur and lens effects; cast shadows are baked into the textures for the fixed sun; the
  RGB camera has no exposure, noise, rolling shutter or lens distortion.
- Thermal sensor effects: microbolometer time constant (about 12 ms, i.e. thermal motion blur), fixed
  pattern noise and shutter (FFC) events, radiometric accuracy (+-5 C or 5 %), 14-bit quantization and
  TLinear resolution, gain-mode switching, vignetting, lens transmission; the reflected sky and the
  narcissus effect; the reflected component uses the air temperature for all surroundings.
- Sub-sample detail: fill fractions are resolved to 1/16 of a pixel (4 x 4 supersampling) by a renderer
  without antialiasing, so an ember smaller than a sample at range can vanish or flicker between frames.
- Vegetation and boulders as obstacles of their own shape (vegetation is texture only; boulders collide
  as convex hulls of their visual meshes); dynamic objects; rockfall.

## Deviations from the brief

- Airborne wind-advected embers (optional) are not implemented.
- The wind-off check compares against run_leanfc's reference environment, which loads the package's
  `plane.urdf`; the gorge world itself never loads it.
- "Survives" in the wind search is reported two ways: completing the mission, and no contact while
  holding within 3 m of the current waypoint. The time limit is 2 x the nominal mission time + 10 s.
- The fixed-scale thermal display is 20 to 100 C (the scene spans about 25 to 52 C, ash 150 C, embers
  saturate), next to the automatic-gain display.
