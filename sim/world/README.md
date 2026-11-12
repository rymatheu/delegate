# Gorge world: a windswept mountain gorge with firebrands, for the leanfc test bench

A PyBullet environment in which the X500 flies, with the frozen Lean controller in the loop, up a
narrow procedural basalt gorge (columnar walls, talus with shrubs and small trees, a dry wash with
boulders, cobbles and grass, small surface fires hidden behind boulders), in a wind channeled by the
gorge, carrying a forward RGB camera, a downward RGB camera and a forward uncooled LWIR thermal camera
(640 x 512 drone core class) whose images are detected for hot spots.

The world, the fires and the thermal camera were redesigned on 2026-11-11 (screen grabs, the before and
after comparison and the fire GIF in `out/redesign/grabs/`; `out/redesign/grabs.py` makes them,
`out/redesign/bench.py` measures the render cost). Results below that predate the redesign are marked.
Everything in the world is generated from a seed by the scripts here (see ASSETS.md); the harness of
`sim/run_leanfc.py` (sensors, controller protocol, lock-step loop, X500 model with motor lag) is
imported unmodified.

![overview](out/overview.png)

## Files

| file | lines | concern |
|---|---|---|
| `gorge.py` | 2757 | the world: centerline, columnar walls, talus, wash, mesh, baked textures (lighting, temperature), boulders, rocks, vegetation, fires (burned patches, flame tongues, embers, fire heating), collision compounds; cache; loading into a PyBullet client (with level of detail); corridor-clearance and free-width checks |
| `fire.py` | 567 | flames, smoke and firelight drawn per frame in image space with the depth buffer, for the RGB and the thermal camera, deterministic in seed and time |
| `wind.py` | 145 | mean flow, Dryden-style gusts, aerodynamic force, `WindAviary`; wind-off check |
| `sensors.py` | 734 | camera mounts, RGB pipeline (sky, fires, haze, exposure, tone), thermal camera (radiometry, flames, optics with halo, non-uniformity, noise, gain states, quantization), palette, AGC, detection, matching; self-test |
| `fly_gorge.py` | 294 | the closed-loop flight: `GorgeAviary`, mission overlay, contact, clearance, cameras, detections.md |
| `wind_study.py` | 164 | wind flights in steps, metrics, wind.md |
| `render_world.py` | 411 | overview.png, oblique.png, onboard contact sheets, flight.gif |
| `gorge_session.py` | 183 | the gorge as a ground-start, real-time MAVLink session: sim/run_leanfc.py's loop with the gorge world, the vehicle resting on the floor, pose feed for the camera, clearance and real-time record |
| `gorge_plan.py` | 114 | the gorge mission as a QGroundControl `.plan` and as the session's parameter overlay; the rest height at the start |
| `camera_component.py` | 544 | the simulated camera payload: MAVLink component N/100 (`--sysid`, default 1), its answers to QGroundControl, two RTP/H.264 streams (libx264 via PyAV), render worker pool |
| `camera_render.py` | 96 | render worker of the camera (sensors.py's RGB and thermal cameras from the latest pose and its simulated time; AGC display; `--lod`) |
| `tile_server.py` | 225 | XYZ map tiles of the gorge for QGroundControl's CustomURL provider: top-down rendering, georeference, HTTP |
| `geo.py` | 121 | the controller's NED <-> latitude/longitude conversion and QGroundControl's Web Mercator tile arithmetic |
| `fly_gorge_qgc.sh` | 59 | the launcher of the session, camera and tile server |
| `test_camera.py`, `test_tiles.py`, `test_gorge_flight.py`, `run_qgc_gorge.py` | | the camera protocol and stream test, the tile test, the full scripted flight, the real QGroundControl run (`--formation PLAN`: the formation session) |
| `formation_plan.py` | 336 | two vehicles: the plans `abreast` and `staggered` (offset vectors), the routes, plan files and overlays per vehicle, the nominal geometry (clearance, separation, skew); `--sweep`: the offsets study |
| `formation.py` | 533 | two X500s in one world (`FormationAviary`: motor lag and wind per vehicle), two controllers: batch (air start, `--skew`) and the real-time MAVLink session; separation, contacts and clearance every tick; `summarize`; `--self-check` |
| `formation_study.py` | 141 | the batch flights over seeds, wind and skew, and their tables (`out/formation/study/`) |
| `fly_formation_qgc.sh` | 87 | the launcher of the formation session: two vehicles, two cameras, the tile server, the plan files |
| `test_formation_flight.py` | 454 | the scripted two-vehicle flight from the ground (one ground-station link as QGroundControl's), its checks and numbers |
| `formation_tests.py` | 94 | the scripted flights one after the other, and their table (`out/formation/tests/`) |
| `render_formation.py` | 186 | the formation animations: both vehicles from outside, the four onboard views under them |
| `QGC-CAMERA.md` | | what QGroundControl 5.1.5 asks of a MAVLink camera, its streams and a tile server, with the sources |
| `snapshot/` | | the frozen controller `leanfc` and its parameter files (not modified) |
| `assets/` | | generated meshes and textures (not tracked: about 300 MB, built from the seed on first use by any script, about 3 minutes; `sim/setup.sh` builds them once) |
| `out/` | | evidence: images, GIF, `detections.md`, `wind.md`, `main/` (the camera flight), `runs/` (wind flights) |

## How to run

```
PY=sim/.venv/bin/python
cd sim/world          # from the repository root
$PY -B gorge.py                       # build seed 7 (about 140 s, then cached), write assets/, print the summary
$PY -B out/redesign/grabs.py          # the screen grabs of the redesign (--only NAME ...)
$PY -B sensors.py                     # self-test: texel pass-through of the thermal twin, band radiance, camera cost
$PY -B fly_gorge.py --out out/main    # the camera flight (field noise, no wind): flight.csv/json, cams_*.npz, detections.md
$PY -B fly_gorge.py --wind 4 1 --cameras off --out out/runs/w4   # options: --wind MEAN GUST, --seed, --gorge-seed,
                                      #   --noise none|field, --cameras on|off, --out DIR
$PY -B wind.py out/runs/off/flight.csv   # wind off = run_leanfc physics, bit for bit
$PY -B wind_study.py --jobs 6         # 23 flights -> out/wind.md (--reuse: recompute the report only)
$PY -B render_world.py                # out/overview.png, oblique.png, onboard-rgb.png, onboard-thermal.png, flight.gif
```
`fly_gorge.py` defaults: `--noise field`, `--cameras on`, `--seed 0` (sensor noise, gusts, thermal
noise), `--gorge-seed 7`, no wind. With cameras the 49 s flight takes 150 s of wall time (cameras
rendered at full quality in the loop; without cameras about 20 s, not re-measured after the redesign).

## The world (`gorge.py`)

All numbers are for seed 7 and are printed by `python gorge.py`. The build takes about 140 s (ray tests
for the sun's shadow now and at six earlier positions, sky visibility and fire heating, for 6144 x
4096 terrain texels and every object texel); its result is cached in `assets/gorge_s7.pkl` under a key
made of the seed and gorge.py's own source, so later scripts load the world in about a second.

Look, and what drove it in the reference photographs (the "important" one most): dark columnar basalt
whose columns differ in tone from dark grey-brown to buff, with shadowed recesses and vertical stains,
under a blocky entablature; rock faces alternating along the gorge with vegetated slopes and talus cones
of fallen column blocks with shrubs between them; conifers, sage and dry grass on the plateau; grey,
lichen-mottled, angular boulders that belong to the rock around them; a dry floor (the references with a
river were used for the rock only). Second pass (2026-11-11, after a review): walls, wall variety,
boulders, texture magnification, flames, burned patches, smoke, vegetation, thermal background and fire,
automatic gain, all reworked.

- Frame: ENU (PyBullet's), axis toward north from the origin; the flight covers north 0 to 72 m; the
  terrain runs from 16 m south to 100 m north; plateau 45 m wide on each side.
- Centerline: two sines scaled so that the axis heading stays within 22 deg of north (21.9 deg).
- Wash (floor): 6.30 to 8.59 m wide (narrows at N 22.4 and 54.7 m); rising 2.32 m over the flight; a
  shallow channel and noise across, flattened in the start and landing zones (ground relief within 0.6 m
  of the start 0.018 m, of the landing 0.124 m). No water: sand, gravel and pebbles (Voronoi cells of
  at least 3 texels), patches of low green and straw-colored cover.
- Walls, per side and row (all profile parameters smoothed over 3 m along the gorge), in two kinds of
  section that alternate along each side: a cliff section (a talus apron 0.6 to 2.8 m high at the foot,
  then the colonnade) and a vegetated-slope section (a talus cone of fallen blocks up to about 30 % of
  the wall, a steep vegetated band with outcrops above it, then the colonnade). Above: a ledge up to 1 m
  wide with shrubs, a blocky entablature 74 to 82 deg up to the rim 19.3 to 26.0 m above the wash, a
  rounded soil cap and the plateau. Talus height 1.0 to 5.8 m (west) and 2.2 to 4.8 m (east) over the
  flight; mean angle toe to rim 64.6 to 79.0 deg.
- Wall relief: columns (a 1D Voronoi pattern along the wall, 0.5 to 1.3 m wide) with a ridge-shaped
  front, their own depth, cross joints every 1.5 to 5.5 m where 40 % of the segments step in or out, and
  their own top height; the entablature as wavy rows (0.22 to 0.65 m high) of irregular blocks (0.25 to
  1.0 m) with their own depth and tilt. The mesh gets this relief low-passed to its own resolution (rows
  every 0.35 m), so it shows no stair steps; the texture gets the detail: albedo per column and per block
  from dark grey-brown (74, 66, 58) to buff (158, 136, 106) (+-25 % around the mean), some greyer, recesses
  40 to 60 % darker within 4 to 16 cm of a column's or block's edge with a smooth falloff (no dashed
  lines), a shadow under protruding segments and blocks, dark vertical varnish stains, white mineral
  streaks on a few columns, pale and orange lichen; the shading normal follows the facets. Soil and
  plants only on a ledge's flat top.
- Mesh: rows every 0.35 m; columns across: 21 wash columns, the toe, and per side 12 talus, 6 slope,
  30 colonnade, 2 ledge, 16 entablature, 4 cap and 12 plateau columns: 62,084 vertices, 123,132 triangles.
- Terrain texture (6144 x 4096): as above for the walls; talus of dark angular blocks (two scales,
  irregular outlines) with soil and plants between; wash; golden and olive grass, sage-grey patches and
  soil on the plateau; contact darkening around each boulder; the burned patches baked in with a noisy,
  feathered edge. Prefiltered (Gaussian, 0.6 texel), so that no single texel stands out when the
  renderer magnifies it.
- Lighting is baked into every texture (the visual world is rendered with the ambient term only):
  sun with cast shadows, sky light through the unoccluded hemisphere (12 rays per texel at 1/8
  resolution), warm reflected light. Sun: from the solar position at latitude 39 deg, mid May, about
  14:00 (azimuth 235 deg, elevation 55 deg).
- Boulders: 54 (0.6 to 2.5 m): lumpy icospheres cut by 6 to 16 fracture planes, the facets flat-shaded
  (sharp edges), flattened, tilted, sunk 10 to 30 %; the wall's own basalt palette with mottling, pale
  grey-green and orange lichen on the upper faces, dark undersides, moss at the base; ten large ones at
  stations every 6.9 m with smaller companions, the rest on the wash and the talus. Physics: convex hulls.
- Rocks: 4129: 3259 column fragments (prisms with knocked edges) in rubble clusters on the talus,
  coarser toward the cliff, and scattered; 757 cobbles on the wash; 113 chips around the boulders. Every
  small object is placed on the terrain height and rejected where a boulder is above the terrain there
  (the first pass put grass and stones on boulder tops). The 3297 rocks of 0.1 m or more collide.
- Vegetation (meshes): 560 shrubs in clusters of 2 to 8 on the talus, the vegetated slopes and the wash
  edges (a few large lumpy foliage blobs each, normals from the crown center, olive and sage greens),
  ledge shrubs, 900 sage bushes, pines (102: trunk and 8 to 12 drooping cones) and junipers (136: an
  irregular column of blobs) on the plateau, along the rim and on the talus, 12 small broadleaf trees,
  8937 grass tufts (bunchgrass on the plateau, green to straw on the wash and talus). Trunks and foliage
  collide (compounds of convex hulls); grass and thin branches do not.
- Keep-out rule (`Gorge.keep_ok`): nothing taller than 2.5 m above the centerline floor within 3.6 m of
  the flight path (vegetation: 1.6 m), boulders within 2 m of the route at most 1.6 m tall, nothing in
  the start and landing zones; objects are kept off the open fires' sight lines and out of the patches.
- Flight corridor on all collision geometry (`Gorge.corridor_clearance`): the path line at least 2.05 m
  from everything, the corridor box (+-1.25 m, 3.0 to 4.0 m above the floor) at least 1.27 m. Free width
  across the axis at 3.5 m above the floor (`Gorge.free_width`): 10.32 to 16.84 m (median 14.24 m).

Temperature classes (deg C; shade + (sun - shade) x insolation, plus fine-scale variation (about +-2 K),
plus the fire heating below; emissivity varies by about +-0.012):

| class | shade | full sun | emissivity | time constant (h) |
|---|---|---|---|---|
| sand and gravel of the wash | 30 | 52 | 0.92 | 1.0 |
| rock (basalt walls, blocks, boulders) | 29 | 56 | 0.94 | 2.5 |
| soil | 30 | 50 | 0.94 | 1.5 |
| dry grass | 30 | 46 | 0.96 | 0.4 |
| leaves | 28 | 34 | 0.97 | 0.25 |
| bark | 29 | 44 | 0.95 | 0.8 |
| burned ground and ash | 150 to 350, glowing cracks and coals 350 to 750 | | 0.95 | fire model |
| ember (coals) | 0.55 to 1.0 x the fire's temperature (620 to 900), glowing in its cracks | | 0.90 | |
| sky | 30 C at the horizon, 50 K colder at the zenith | | 1 | |

Thermal inertia: the insolation that sets a surface's temperature is the present one averaged with the
sun's positions every 30 min over the last 3 h (each ray-tested for shadow), weighted by exp(-age / tau)
with the class's time constant: rock that has just gone into shade stays warm, sand cools faster, leaves
follow the present sun. The class parameters are blurred over about 25 cm, so material boundaries blend.

Fire heating (`Gorge.fire_heating`): each fire's radiated power is split over points along its flaming
front (and its burning shrub or tree); a surface in sight of a point at distance d gets P cos / (4 pi
d^2) and rises by 0.5 x 0.9 q / (12 + 6.5) K (capped at 250 K; 15 % out of sight), so the ground ahead
of the front is hotter than the burned interior.

## Fires: how they are built, drawn and seen

- 8 small surface fires: a burned patch of mean radius 0.32 to 0.84 m with a ragged rim; the flaming
  front is an irregular partial edge (40 to 55 % of the rim on the downwind side, plus one or two short
  flaming stretches), the rest smolders. Tongues every 4 to 7 cm along the front, 0.18 to 0.5 m wide so
  that they merge, heights lognormal (a few licks 2 to 2.6 times the median) times a variation along the
  front; tongues behind the front; on a burning shrub (a charred twig skeleton), a burning log or the
  base of a small pine. Radiated power 17 to 97 kW.
- Placement and visibility bookkeeping as before: 6 hidden (in sight from 8 to 20 % of the path points
  3 to 20 m before; each behind a boulder at least 1.15 m tall), 2 open (in sight from 100 %). Seed 7:
  litter (N 16.3), grass (N 23.1), burning shrub (open, N 31.4), litter (N 36.2), fire at a pine (open, N
  42.6), grass (N 42.9), burning log (N 50.5), litter (N 58.9).
- Burned patch: char baked into the terrain with a feathered edge; over it a mesh inside 0.88 of the rim
  with char, ash, thin glowing cracks and small coals behind the front; 10 to 15 coal pieces with a crack
  texture of their own.
- Flames, smoke and light: `fire.py` (its docstring has the model). Flames are orange-dominant and
  translucent (color capped at (255, 215, 120), sooty dark-red tips); smoke puffs are at most 12 %
  opaque, shaded by the sun, bent downwind and flattened into a thin haze drifting up the gorge, faded
  near the camera; in the thermal image smoke is nearly invisible (emissivity 0.02 x opacity, excess
  temperature falling as height^(-5/3)) and flames have filaments.
- Quality: still images use `Fires(g, "still")` (flames at full resolution), the onboard cameras
  `"live"` (flames at half, smoke at a third).

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
  then 10 waypoints along the centerline 3.5 m above the floor; `nav.vMax 2.0`, `nav.aMax 2.0`,
  `nav.radius 0.2`, `nav.lagMax 0.6` (x500 values, restated). Spacing: the navigator stops at every
  waypoint (1 s to accelerate and 1 s to brake at 2 m/s^2, 1 m each), so legs are as long as possible:
  at most 10 m and with the centerline within 0.35 m of each chord: 10 legs of 4.2 to 10.0 m, path 73.4
  m (seed 7 after the redesign); flown: all waypoints reached at 46.7 s.
- Sensors: run_leanfc's `Sensors` and `Noise` (`field`: 10 Hz GPS-like fixes, the field profile;
  `none`: zero noise and 100 Hz fixes). Physics as run_leanfc (1200 Hz, motor lag 12.5/25 ms).
- Contact: after every tick `getContactPoints` of the vehicle; any contact ends the run with time,
  body class, position, depth, normal force and speed in flight.json. Clearance: `getClosestPoints`
  from the vehicle's collision cylinder (radius 0.25 m, 0.22 m tall) to every collision body of the world
  (terrain, boulders, the rock and vegetation compounds), up to 4 m, every tick (CSV column `clearance`).
- The run ends 2 s after the last waypoint, or at the time limit 2 x nominal + 10 s (101 s).
- Cameras (`--cameras on`) render from the true pose after each tick's physics and at its simulated
  time, in two extra PyBullet clients (visual world, thermal twin), at their own rates; they do not feed
  the controller.

## Sensors (`sensors.py`)

- Mounts (body FLU): FORWARD at (0.20, 0, -0.03) m, 30 deg below the nose; DOWN at (0, 0, -0.10) m
  looking straight down, image top = forward.
- RGB camera: TinyRenderer with the ambient term only (the textures carry the lighting); sky by
  elevation with a glow around the sun and procedural clouds; the fires (fire.py); aerial perspective
  (haze, 900 m scale); automatic exposure (mean luminance to 118, gain 0.85 to 1.7, damped); a mild tone
  curve. Returns RGB, z-depth (m) and optionally the segmentation.
- Thermal camera (`ThermalSpec`, the docstring lists what is modeled): a 640 x 512, 12 um uncooled VOx
  core with a 7.5 mm f/1.0 lens: 54.2 deg HFOV, 1.6 mrad IFOV, 8.7 Hz. Chain per frame: the thermal twin
  (100.000 % texel pass-through, `selftest`); band radiance (Planck, 8 to 14 um); emissivity with
  surroundings at air temperature; atmosphere; flames (soot emissivity, filaments) and smoke (nearly
  transparent, fire.py); optics with a core PSF and a 2-term halo (the glow around saturated flames);
  residual non-uniformity (0.4 % gain; 30 mK pixel, 15 mK column, 10 mK row offsets: all below the NETD,
  so no visible stripes), temporal noise (NETD 40 mK high gain, 100 mK low gain), two gain states with
  automatic switching, saturation, 14-bit quantization; apparent temperature out. The scene behind it:
  thermal inertia (insolation of the last 3 h, per-class time constants), blended material boundaries,
  fine-scale temperature and emissivity variation, fire heating from the flaming front, burned ground at
  150 to 350 C with hot cracks and coals. Not modeled: motion smear, shutter events, vignetting,
  narcissus.
- Display: `PALETTE` (ten control points written in code: deep blue, indigo, purple, magenta, red,
  orange, yellow, near white). `AGC`: without a fire in view, plateau histogram equalization blended with
  a linear map; with a fire in view (pixels above 72 C), a two-part mapping: the pixels below 72 C are
  equalized into the lower 45 % of the palette (blue to magenta), hotter ones mapped linearly in log
  radiance onto the upper 48 % (red to white), so sunlit sand and boulders stay purple and only the fire
  and the ground it heats are orange to white; smoothed over frames.
- Why not T^4: the 8 to 14 um band holds 37.8 % of the total radiance at 30 C but 14.0 % at 600 C and
  7.5 % at 900 C, so T^4 overstates the contrast of a 600 C ember over 30 C rock by 2.7 x.
- Detection: hot pixels above the frame median + 40 K; connected groups placed in the world from the
  hottest pixel's bearing and range (the flame's depth where a flame is in front, upsampled by nearest
  neighbor); matched to the fire whose extent (burned patch, 1.5 m of flame) is within 2.0 m.
- Live level of detail (third pass): the onboard cameras' render workers (`camera_render.py`, default
  `--lod 2`) load a decimated visual world (`Gorge._live_lod`, `Gorge.load(..., lod=2)`): the same
  terrain and fires; boulders from their icospheres' subdivision-2 vertices (320 faces each, the same
  shape); rocks under about 0.12 m left out, cobbles as octahedra; each shrub, juniper and broadleaf
  tree one rounded crown, sage one small crown, pines a trunk and three cones, the fires' own fuel as it
  is; no grass. Baked into its own atlas with the same materials (`objectslive_s7_*.png`). Triangles:
  still 1,247,559 (terrain 123,132, boulders 69,120, rocks 114,172, plants and grass 941,135), live
  280,337 (terrain 123,132, boulders 17,280, rocks 55,700, plants 84,225). The live world is split into
  14 chunks of 8.4 m along the gorge (53 bodies); each camera hides the chunks outside its view frustum
  before a frame (`sensors.Culler`; the image is pixel-identical to the unculled one). The live fire
  layer draws every second smoke puff (larger, a little more opaque, no noise), distant fires with every
  second flame tongue, firelight at quarter resolution, cheap 2x upsampling; occlusion culling of fires
  by sample points; the texel softening at half resolution (`sensors.soften_live`). The live thermal
  image is the full radiometric chain rendered at 320 x 256 and resized to the 640 x 512 stream.
  Collision geometry, the still path (grabs, `render_world.py`, `render_formation.py`) and the in-loop
  cameras of `fly_gorge.py` are unchanged.
- Rendering cost per frame (`out/redesign/bench.py`, 19 poses along the route, with the empty-frame
  TinyRenderer baseline at 640 x 480 measured at the same moment; idle machine: 14 ms). Before the
  redesign (idle): RGB 640 x 480 85.7 ms, thermal 160 x 120 82.8 ms. Second pass, still world (baseline
  32.5 ms): RGB 278 ms, thermal 640 x 512 242 ms, thermal at half resolution 92 ms. Third pass, live
  level of detail (baseline 32.4 / 33.1 ms, load average 5.6): RGB 640 x 480 160 ms (p95 222), thermal
  (320 x 256 rendered, 640 x 512 out) 50 ms (p95 66). Of the live RGB frame under that load: TinyRenderer
  about 70 ms, the fire layer up to 50 ms where fires are in view, softening 16 ms, tone 6 ms.
- Launcher defaults: `fly_gorge_qgc.sh` RGB 640 x 480 at 10 Hz with 3 workers and the thermal stream with
  1 (4 render processes); `fly_formation_qgc.sh` per vehicle RGB 640 x 480 at 10 Hz with 2 workers and
  thermal with 1 (6 render processes for two vehicles); both use the live level of detail.

## Results (seed 7, field noise seed 0; after the second pass)

- Flight without wind (`out/main`): completed in 48.7 s (all waypoints at 46.7 s), no contact; tracking
  error max 0.28 m; minimum clearance 1.79 m (north 13.9 m).
- Thermal detection (`out/main/detections.md`): all 8 fires detected; the open fires at 30.5 and 26.3 m,
  the hidden ones from 8.1 to 43.1 m (several first from the heated ground or flames over the boulder).
  40 unmatched detections in 34 of 424 frames, from a flame-depth upsampling error found after the
  flight (bilinear blending of the flame's depth with the far background placed some detections on the
  boulder in front of the fire); fixed (nearest-neighbor depth); re-rendering the frames from t 14 to 18.5
  s of the recorded flight with the fix gave 313 detections, none unmatched. The flight was not rerun.
- Formation batch flights (`formation.py --plan P --noise field --seed 0`): abreast completed, no contact,
  separation 1.66 to 2.05 m, clearance at least 1.55 / 1.93 m, tracking max 0.21 / 0.24 m; staggered
  completed, no contact, separation 2.72 to 3.12 m, clearance at least 1.50 / 1.95 m, tracking max 0.21 /
  0.23 m; no motor saturation. Plans: nominal clearance abreast 1.55 / 1.92 m, staggered 1.50 / 1.93 m.
- The wind study (`out/wind.md`) predates the redesign.

## The gorge with QGroundControl: session, camera payload, map (`fly_gorge_qgc.sh`)

```
sh sim/world/fly_gorge_qgc.sh                                   # then open QGroundControl (sim/mavlink/QGC.md)
sim/world/.venv-video/bin/python sim/world/test_camera.py        # camera protocol and both streams
$PY -B sim/world/test_tiles.py                                   # tiles and their georeference
$PY -B sim/world/test_gorge_flight.py --seed 0                   # a full scripted flight, video on (plan uploaded)
$PY -B sim/world/test_gorge_flight.py --seed 0 --no-upload       # the same with the onboard mission, no upload
sim/mavlink/.venv/bin/python sim/world/run_qgc_gorge.py --seconds 90 [--home $(mktemp -d)]   # the real QGroundControl
```

- Session (`gorge_session.py`): sim/run_leanfc.py's loop and options with the gorge world in place of
  the ground plane, current build and parameter files (not the snapshot), `--ground --mav --realtime 1
  --trace-vehicle`; the X500 rests on the floor at the first waypoint (its base 5 mm above the highest
  ground point under its collision disc plus its rest height, then settled); the vehicle boots with the
  complete gorge mission onboard, as an ArduCopter boots with the mission in its storage (the overlay
  `gorge.params` carries it as `TAKEOFF`, `SPLINE` and `LAND` lines, `gorge_plan.write_overlay`): the
  items of `gorge.plan` in the same order, takeoff, the spline waypoints, land; so after connecting,
  QGroundControl's Start Mission (Guided, arm, MISSION_START) works from the ground with no upload, and
  uploading `gorge.plan` is optional (it replaces the onboard mission with the same items); wind with `WIND="MEAN GUST"` (wind.py; gust seed = noise seed + 1000).
- Camera payload (`camera_component.py`, `camera_render.py`): the forward RGB camera of sensors.py at
  640 x 480, 90 deg, 15 fps (three render workers, about 160 to 230 ms per frame each) and the forward thermal
  camera at 640 x 512, 54 deg, 8.7 fps (two workers, about 160 ms; before the redesign 160 x 120, 57 deg, one worker, 90 ms), libx264 constrained baseline,
  a keyframe every second; thermal display: apparent temperature 20 C (black) to 80 C (near white)
  through sensors.PALETTE. The workers render from the newest pose of the 100 Hz feed.
- Map (`tile_server.py`): a top-down rendering of the generated world at 1.5 cm per pixel (4648 x 6934
  pixels, built in about 8 s at start), served at zoom 0 to 23 through the controller's own flat-earth
  conversion and QGroundControl's Web Mercator arithmetic; everything outside the terrain is the uniform
  color (138, 132, 118).

Results after the third pass (live level of detail): `test_camera.py --rgb 640x480@10 --rgb-workers 3`
(the single-vehicle defaults: 3 RGB and 1 thermal render process; baseline 29.9 ms just before): 32 of
32; RGB 9.93 fps sent of 10 (4 slots dropped in 35 s), 9.87 fps decoded, render 209 ms mean; thermal
8.71 fps of 8.7, none dropped, render 65 ms mean; pose to decoded frame 132 ms (RGB) and 49 ms (thermal).
Detection on the live level of detail (`out/redesign/live_detect.py 9.5 14.5`: the recorded `out/main`
frames re-rendered): every fire in view detected except hidden fire 5, in view in one frame only; 368
detections, none unmatched (the full camera on the same frames: 768, none unmatched, hidden fire 7 in
view in one frame and not detected). The two-vehicle session was not run.

Results after the second pass (2026-11-11): `test_camera.py --rgb 640x480@10 --rgb-workers 4`: 32 of 32
protocol and stream checks pass, but with six render workers (four RGB, two thermal) on a machine
already loaded by other work the streams fell far short of their rates: RGB 4.40 fps sent of 10 (210
slots dropped, render 941 ms mean), thermal 2.72 fps of 8.7 (213 dropped, render 743 ms); the camera drops
slots rather than stalling. `test_tiles.py`: 15 of 15. The live sessions were not run.

Results before the redesign (outputs in `out/test-camera/`, `out/test-tiles/`, `out/test-flight/`, `out/qgc-real*/`):

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
$PY -B test_formation_flight.py --plan staggered --seed 0 [--wind 6 2] [--skew -2] [--start mv] [--no-upload]
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
- **After the redesign** (`formation_plan.py` rerun; batch flights `formation.py --plan P --noise field
  --seed 0`, no wind, `out/formation/P-field-s0/`): nominal clearance abreast 1.61 and 1.82 m, staggered
  1.57 and 1.94 m; start rest tilt abreast 1.96 / 2.37 deg, staggered 0.68 / 1.30 deg; land 3.0 / 2.4 and
  4.5 / 3.4 deg. Flights: both completed, no contact; abreast separation 1.67 to 2.06 m, clearance at least
  1.61 / 1.82 m, tracking max 0.21 / 0.24 m; staggered separation 2.72 to 3.12 m, clearance at least 1.57 /
  1.96 m, tracking max 0.21 / 0.23 m; no motor saturation. The study tables below predate the redesign.
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

- Smoke and flame as participating media in 3D (they are image-space layers with a soft depth test,
  fire.py), the plume's buoyancy and updrafts; fires do not spread, burned patches do not grow, embers do
  not cool; fire heating is a static radiative balance computed at build time; no diurnal cycle.
- Airborne embers (the optional wind-advected particles were not implemented), rotor wash on embers,
  ash or vegetation.
- CFD-resolved wind: no separation, recirculation behind boulders, wall shear layers, wake of the
  vehicle or ground effect; gusts are a function of time at the vehicle only (no spatial gust field),
  the cross-gorge component does not vanish at the walls; the drag force has no moment.
- Terrain-induced GPS degradation (multipath, satellite masking by the walls), barometer errors from
  wind, magnetometer disturbance by rock; the sensor model is run_leanfc's, unchanged.
- The visual renderer's limits: lighting is baked for the fixed sun (no dynamic shadows of the vehicle or
  the smoke), no specular reflection, no motion blur; TinyRenderer has no texture filtering or
  antialiasing, so texels and leaf clumps show as small facets up close; the RGB camera has no noise,
  rolling shutter or lens distortion.
- Thermal sensor effects: microbolometer time constant (thermal motion blur), shutter (FFC) events and
  drift, radiometric accuracy, vignetting, narcissus; the reflected component uses the air temperature
  for all surroundings. Live frames render one sample per pixel (the stills two).
- Obstacles: boulders and rocks collide as convex hulls of their meshes, shrubs and trees as compounds of
  convex hulls of their trunks and leaf clumps; grass and thin branches have no collision; no dynamic
  objects or rockfall.

## Deviations from the brief

- Airborne wind-advected embers (optional) are not implemented.
- The wind-off check compares against run_leanfc's reference environment, which loads the package's
  `plane.urdf`; the gorge world itself never loads it.
- "Survives" in the wind search is reported two ways: completing the mission, and no contact while
  holding within 3 m of the current waypoint. The time limit is 2 x the nominal mission time + 10 s.
- The fixed-scale thermal display is 20 to 100 C (the scene spans about 25 to 52 C, ash 150 C, embers
  saturate), next to the automatic-gain display.
