# Flying the real leanfc controller from QGroundControl 5.1.5

`sh sim/fly_qgc.sh` starts the PyBullet simulation in real time with the X500 resting on the ground,
disarmed, and the real controller (`leanfc`: MAVLink services, vehicle layer, flight law) sending to
QGroundControl's UDP port 14550. QGroundControl treats it as an ArduCopter 4.7 quadcopter.

What this checklist rests on:

- **Observed with the real application** (`sim/mavlink/run_qgc.py`: QGroundControl 5.1.5, unmodified, as a
  child process with its console log; every frame recorded on the vehicle side; nothing clicked): the
  whole connect sequence against the real controller in the real-time simulation: vehicle created 0.9 s
  after QGroundControl's UDP link came up, all 159 parameters of that build (160 since
  `nav.yawReverse`) loaded 3.2 s later ("Initial load complete"), the 5-item mission downloaded, geofence and rally skipped, "Ready To Fly", no warning
  caused by leanfc (README.md, "From the ground, with a ground station", has the log excerpts). Logs:
  `sim/mavlink/out/qgc-real1/`.
- **The scripted ground station** (`sim/mavlink/test_services.py`): every action below, as
  QGroundControl 5.1.5 sends it (its message sequences, timeouts and acceptance checks, from its source),
  against the real controller flying from the ground: 57 of 57 steps pass for the X500 deterministic and with
  field noise on seeds 0..4, 7 and 11, and for the CF2X deterministic and with field noise (README.md, "From the ground, with a ground station").
- Nobody has clicked through the steps below in the real application yet: that is what this checklist is
  for. The button names are QGroundControl 5.1.5's (`src/FlyView/GuidedActionsController.qml`,
  `src/PlanView/PlanView.qml`).

## Start

1. Build once and start the simulation (it builds if needed):

   ```
   cd /Users/ryan/Research/leanfc
   sh sim/fly_qgc.sh
   ```

   It prints `leanfc: MAVLink system 1, 127.0.0.1:<port> -> 127.0.0.1:14550` and runs in real time
   until Ctrl-C (at most 2 hours), then writes `sim/out/qgc/flight.csv` (the simulation, one row per
   tick, with the mode, armed, landed state and mission item) and `sim/out/qgc/vehicle.log` (every
   MAVLink frame). Options: `VEHICLE=cf2x`, `NOISE=none` (100 Hz noiseless fixes instead of the
   GPS-like 10 Hz field noise), and any `sim/run_leanfc.py` option after the command, such as
   `--origin LAT LON ALT`.

2. Open QGroundControl (Applications, or `/Applications/QGroundControl.app/Contents/MacOS/QGroundControl`).
   No settings need changing: UDP autoconnect on 14550 is on by default. On its first run it asks for
   units and vehicle preferences; the link comes up behind that dialog anyway.

The field is the summit of Pikes Peak, Colorado (38.8405556 N, 105.0441667 W, 4302 m AMSL;
`params/ground.params`, line `ORIGIN`). The physics does not model the thin air.

## Connect

Within a few seconds of opening QGroundControl:

- [ ] The toolbar shows the vehicle, flight mode **Stabilize**, **Disarmed**. For the first 3 s after
      the simulation starts (1 s gyro calibration, 2 s estimator settling) the status says "Not Ready"
      with a PreArm message; then **Ready To Fly**.
- [ ] The map centers on Pikes Peak with the vehicle and the **H** (home) marker under it.
- [ ] A progress bar fills while 160 parameters load (80 of leanfc, 80 compatibility values for
      QGroundControl's setup pages). No dialog appears; in particular none of: "Parameters are missing from
      firmware", "Configuration tasks remain before this vehicle is ready to fly", "unable to retrieve the
      full set of parameters", "not running latest stable firmware", "MAVLink v1 traffic detected".
- [ ] The parameter file's mission shows on the map: a 4 m square north and east of home (four
      waypoints at 2 m and 3 m).
- [ ] Messages (the bell): "leanfc V0.1.0 (ArduCopter 4.7 MAVLink)" and "Frame: QUAD/X".
- [ ] The instrument panel: level, heading north, altitude 0, ground speed 0.

## Parameters (Vehicle Configuration → Parameters)

- [ ] leanfc's parameters are there with ArduPilot's names where ArduPilot has the same parameter (WP_SPD,
      WP_ACC, WP_RADIUS_M, PSC_*, ATC_ANG_*, EK3_*, RTL_ALT_M, RTL_LOIT_TIME, LAND_SPD_MS,
      LAND_ALT_LOW_M, DISARM_DELAY, FS_GCS_ENABLE, FS_GCS_TIMEOUT, FS_EKF_ACTION, MOT_SPIN_ARM,
      MOT_SPOOL_TIME, TKOFF_SLEW_TIME, TKOFF_THR_MAX) and LFC_* otherwise, with QGroundControl's ArduPilot
      descriptions for the ArduPilot names.
- [ ] Set **WP_SPD** to 1.5 and save: it stays 1.5. The next mission legs cruise at 1.5 m/s instead of 2.
- [ ] Set **RTL_ALT_M** to 8: the next RTL returns at 8 m (or higher if the vehicle is higher).
- [ ] Set LFC_DT to -1: refused, the value returns to 0.0025, "Param write denied (LFC_DT): `dt` must be
      positive" appears and QGroundControl reports the write as failed (intended).

## Fly: takeoff, change altitude, go to location, pause, RTL

- [ ] Choose **Auto** in the flight-mode selector, then **Arm** (slide to confirm): refused with the
      critical message "Arm: Auto mode not armable" (ArduCopter's behavior). Choose **Guided** again.
- [ ] **Takeoff** (left tool strip), set the altitude on the slider (e.g. 5 m), slide to confirm.
      QGroundControl switches to Guided, arms ("Arming motors"), and sends the takeoff. The motors idle for
      0.5 s, the throttle ramps up, the vehicle lifts off and climbs straight up at 1 m/s; the state shows
      flying. At the altitude it holds.
- [ ] **Actions → Change Altitude**: drag the slider (e.g. +3 m), confirm. The vehicle climbs and holds.
- [ ] Click on the map → **Go to location** → confirm. The vehicle flies there in a straight line at
      WP_SPD (nose along the track), stops and holds. With field noise it holds within a few decimeters.
- [ ] During a go-to: **Pause** (tool strip). The mode becomes **Brake**; the vehicle stops within a
      second and holds.
- [ ] **Return** (tool strip) → confirm. The mode becomes **RTL**: the vehicle climbs to RTL_ALT_M (15 m)
      if it is lower, flies straight back over home, waits 5 s (RTL_LOIT_TIME), descends (1 m/s above 10 m,
      then 0.5 m/s), touches down, spools down and disarms ("Disarming motors"). The state shows
      landed and disarmed.

## Fly: a planned mission with spline waypoints

- [ ] **Plan** view: **Takeoff** (adds a takeoff item, e.g. 5 m), then **Waypoint** and click four
      points on the map within about 30 m of home; in the editor of the third and fourth, change the
      command from "Waypoint" to **Spline waypoint**; then **Return**. Set the altitudes to 5 to 10 m (the
      Plan view's default is 50 m, a long climb at 1 m/s). Leave the flight speed unset.
- [ ] **Upload**. "Flight plan received" appears and the upload button stops flashing.
- [ ] Back in **Fly**: **Start Mission** (slide to confirm, on the ground). QGroundControl switches to
      Guided, arms and sends MISSION_START: the mode becomes **Auto**, the vehicle takes off (item 1) and
      flies the waypoints; the current-waypoint marker advances 1, 2, 3, ...; the two waypoint legs stop at
      their corner, the spline legs curve through their points at speed.
- [ ] **Pause** during a leg: Brake, the vehicle stops and holds. **Actions → Continue Mission**: Auto
      again, the current item continues from where the vehicle is.
- [ ] At the Return item the vehicle returns, lands at home and disarms; the mission shows complete.

## Fly: land

- [ ] **Takeoff** again, then **Land** (tool strip) → confirm. The mode becomes **Land**; the vehicle
      descends where it is at 0.5 m/s, touches down, and about 1.5 s later (1 s touchdown detection, 0.5 s
      spool-down) disarms.

## Failsafe

- [ ] With the vehicle flying, quit QGroundControl. After FS_GCS_TIMEOUT (5 s) the vehicle starts RTL
      (`params/ground.params` sets FS_GCS_ENABLE 1; 5 would land instead) and lands at home. Reopen
      QGroundControl: it reconnects, the messages show "GCS Failsafe" and "GCS Failsafe Cleared".

## Not supported, and what QGroundControl shows

- **Flight modes** other than Stabilize, Auto, Guided, Loiter, RTL, Land and Brake (AltHold, PosHold,
  Smart RTL, Circle, Acro, ...): refused, the message "No such mode N", and QGroundControl's mode
  selector stays on the old mode. Stabilize cannot fly (there is no RC): selected in the air it is
  refused with "Mode change to Stabilize failed: no pilot input".
- **Change heading** (CONDITION_YAW): COMMAND_ACK UNSUPPORTED; QGroundControl shows its "command not
  supported" error.
- **Plan items** other than Takeoff, Waypoint, Spline waypoint, Land and Return (a mission-wide flight
  speed, which becomes a DO_CHANGE_SPEED item, loiters, jumps, camera items, ...), and terrain altitude
  frames: the upload ends with "Mission transfer failed".
- **Hold time** at a waypoint works (the vehicle stops and waits); acceptance radius and yaw in the
  waypoint editor are ignored.
- **GeoFence and Rally Points** are not offered (not advertised by the vehicle).
- **Battery**: no measurement; the battery widget shows no value.
- **Vehicle Setup** pages beyond the summaries (calibrations, motor test, radio, servo outputs) show
  compatibility parameters with nothing behind them; a calibration started there does nothing.
- **Orbit, ROI, Set Estimator Origin**: not offered for this vehicle or answered UNSUPPORTED.
- **Set Home** works (map click → Set Home), but QGroundControl needs internet access for its terrain
  query first.
- No MAVLink signing, no MAVLink FTP (parameters load by PARAM_REQUEST_LIST), no log download.

## Recording and the automatic observation

`sim/out/qgc/vehicle.log` has every frame (simulated time, direction, ids, name, payload hex);
`run_qgc.py`'s `decode_log` decodes it. `sim/mavlink/flight_metrics.py` summarizes the flights of
`sim/out/qgc/` if a `steps.json` is not needed (it names flights by steps when there is one).

To repeat the automatic observation (it starts and stops QGroundControl itself; do not click while it
runs):

```
sim/mavlink/.venv/bin/python sim/mavlink/run_qgc.py --seconds 100 --out sim/mavlink/out/qgc-real1
```

## The gorge session: video and map

`sh sim/world/fly_gorge_qgc.sh` flies the same controller in the generated gorge of `sim/world/` (seed 7)
instead of on Pikes Peak's flat ground, with a simulated camera payload and the gorge as the map:

- the X500 rests, disarmed, on the gorge floor at the mission start (north 0 on the centerline), and the
  controller (`.lake/build/bin/leanfc`, `params/x500.params`, `params/ground.params` and the overlay
  `sim/world/out/qgc/gorge.params`) sends to UDP 14550 in real time, field noise; `WIND="4 1"` adds wind
  (mean m/s up-gorge, gust sigma m/s), `ORIGIN="lat lon alt"` another origin, `NOISE=none`, `SEED=N`;
- the camera payload is its own MAVLink component, system 1 component 100 (`sim/world/camera_component.py`):
  two RTP/H.264 streams, the forward RGB camera (640 x 480, 15 fps, 90 deg) to UDP 5600 and the forward
  thermal camera (Lepton 3.5 class, 160 x 120, 8.7 fps, 57 deg) to UDP 5602, rendered from the vehicle's
  true pose; `VIDEO=off` leaves it out, `RGB=320x240@20 RGB_WORKERS=1` changes the RGB stream;
- the map tile server: `http://127.0.0.1:8765/{z}/{x}/{y}.png`, a top-down picture of the gorge (terrain,
  boulders, ash beds and embers) placed at the run's origin, and a neutral background everywhere else;
- the plan file of the gorge mission: `sim/world/out/qgc/gorge.plan` (for the default origin also
  `sim/world/gorge.plan`): takeoff at the start, the nine gorge waypoints as spline waypoints 3.5 m above
  the floor, land at the last one; altitudes relative to home.

The first run creates `sim/world/.venv-video` (uv: PyAV, NumPy) for the camera. The world is built in
every process at start (about 5 s); the camera is up about 15 s after the command, the vehicle is
"Ready To Fly" a few seconds after the simulation starts. Ctrl-C ends everything and writes
`sim/world/out/qgc/` (flight.csv, vehicle.log, session.json with the real-time factor and the clearance,
camera.json with the frame statistics, tiles.log).

### What appears in QGroundControl

- **Video, no setting needed.** About 1 s after the vehicle's parameters have loaded QGroundControl hears
  the camera's heartbeat, asks for its information and its streams, switches its video source to
  "UDP h.264 Video Stream" by itself, and both of its receivers start and decode (seen in its log, below).
  By its QML (`FlyView/FlightDisplayViewVideo.qml`) the Fly view then shows the forward RGB video, with the
  thermal video drawn over it, blended at 85 % opacity and 85 % of the video's height (QGroundControl's
  default thermal mode; the camera's controls offer off, blend, full and picture in picture). Nobody has
  looked at the screen yet: what the windows show is not confirmed. QGroundControl writes one setting by
  itself when it sees the streams: Application Settings > Video > Video Source > **Source** becomes
  "UDP h.264 Video Stream" (settings file: `[Video] videoSource`); from then on it also starts the video
  receiver at launch. To return: set Source back to "Video Stream Disabled".
- **The map, two settings.** Application Settings (the QGroundControl logo at the top left, then
  "Settings") > Maps > Map Provider: **Provider** `CustomURL`, **Type** `Custom`; and under
  "Custom Map URL" the field **Server URL**: `http://127.0.0.1:8765/{z}/{x}/{y}.png`. To return to the
  normal map: Provider `Bing`, Type `Hybrid` (QGroundControl's defaults; any other provider works too). The
  Server URL can stay; it is used only with CustomURL. QGroundControl fetches tiles only while macOS
  reports the network as online (`QGeoMapReplyQGC.cpp` `_cacheError`), and keeps the tiles in its tile
  cache (Application Settings > Maps > Offline Maps / Tile Cache).
- **The mission.** Plan view > the file menu (Open) > `sim/world/out/qgc/gorge.plan`, open it while the
  vehicle is connected (QGroundControl changes its offline-editing settings when a plan is opened without a
  vehicle), Upload, then in the Fly view **Start Mission**: the vehicle takes off, flies the gorge on spline
  legs, lands on the floor at the end and disarms. The plan has no flight speed (WP_SPD, 2 m/s, applies).

`sim/world/QGC-CAMERA.md` lists what QGroundControl 5.1.5 asks of the camera, the streams and the tile
server, with the source of each request.

### Observed with the real application

`sim/world/run_qgc_gorge.py` (QGroundControl 5.1.5 unmodified, a child process with the camera and video
log categories, nothing clicked, terminated at the end; `--home DIR` runs it with a fresh settings
directory):

```
sim/mavlink/.venv/bin/python sim/world/run_qgc_gorge.py --seconds 90 --home "$(mktemp -d)" --out sim/world/out/qgc-real-fresh
sim/mavlink/.venv/bin/python sim/world/run_qgc_gorge.py --seconds 90 --out sim/world/out/qgc-real
```

From its log on a fresh settings directory (`sim/world/out/qgc-real-fresh/qgc.log`, seconds since its start):

```
 3.707 Adding new vehicle link:vehicleId:componentId:vehicleFirmwareType:vehicleType "UDP Link (AutoConnect)" 1 1 3 2
 6.960 "V:1" Initial load complete
 7.925 Heartbeat from "Camera1 (100)"
 7.926 Camera information received from "Camera1 (100)" Model: gorge forward camera
 7.927 Adding real camera to list - simulated camera will be removed if present
 8.428 Received CAMERA_SETTINGS
 8.928 Received VIDEO_STREAM_INFORMATION / Create stream handler for stream ID: 1 (then 2: "All stream handlers done")
 8.930 New Video Source: "UDP h.264 Video Stream"
 8.930 Starting "udp://0.0.0.0:5600" ; 8.931 Starting "udp://127.0.0.1:5602"
 9.087 Decodebin3 selected codec:rank - "applemedia" / vtdec_hw ; Video "videoContent" resized. New resolution: 640 x 480
 9.172 Video "videoContent" decoding changed, active: yes
 9.451 Video "thermalVideo" decoding changed, active: yes (160 x 120)
49.013 frame flow: CPU delivered= 600 input= 600 dropped= 0
```

With the user's settings (`sim/world/out/qgc-real/`, where QGroundControl had already written the video
source), the main receiver starts at launch from that setting, the thermal one when the streams are
announced; QGroundControl's video sink delivered 1200 RGB frames in 80 s and 600 thermal frames, none
dropped, no "Stream timeout". The simulation kept real time throughout (`session.json`: real-time factor
1.000, every second at least 0.9988). The camera also answered QGroundControl's other requests: capture
status, storage (not supported), stream status, the CAMERA_FOV_STATUS request refused, and the gimbal
controller's six GIMBAL_MANAGER_INFORMATION probes refused. The controller received the 13 commands
addressed to the camera on the shared link and answered none of them.

Settings QGroundControl wrote by itself because of the streams: `[Video] videoSource=UDP h.264 Video
Stream` (`settings.diff`). The map settings were not set (that would be a GUI action); the tiles were
tested with their own client (`sim/world/test_tiles.py`). QGroundControl did not exit within 10 s of
SIGTERM and was killed in these runs (one earlier run aborted on SIGTERM, exit -6); `pgrep` found none
left.

Why the streams' uri is a URL: with a bare port ("5600"), as first tried, QGroundControl 5.1.5 set the
receivers' URLs but never started them (`VideoManager::_videoSourceChanged` sees no change because the
`videoStreamInfoChanged` handler has already set the URL; `sim/world/QGC-CAMERA.md` item 19); the next
launch started the main receiver from the saved setting, never the thermal one. With
`udp://127.0.0.1:5600` and `udp://127.0.0.1:5602` both start, on a fresh installation as well.

## The formation session: two vehicles, two plans

`PLAN=abreast sh sim/world/fly_formation_qgc.sh` (or `PLAN=staggered`) flies two X500s in the same gorge,
each with its own controller and its own plan, and no link between them (`sim/world/README.md`,
"Two vehicles in formation"):

- **abreast**: side by side, both noses along the direction of travel; vehicle 2's route is vehicle 1's
  moved 1.8 m to the right of the gorge's mean direction (centre distance 1.80 m);
- **staggered**: vehicle 2 is 2.2 m to the right and 1.8 m behind (2.84 m), and flies with its nose against
  the direction of travel (`nav.yawReverse 1`, MAVLink `LFC_WP_YAW_REV`), so its camera looks behind the
  formation. The launcher sets this parameter through the plan's overlay; a plan file cannot carry it.

What runs: one PyBullet world with both vehicles resting on the floor (`sim/world/formation.py --session`),
two controllers, MAVLink systems 1 and 2, both sending to UDP 14550; two camera payloads, components 1/100
and 2/100, vehicle 1's RGB and thermal streams to UDP 5600 and 5602, vehicle 2's to 5604 and 5606 (RGB
640 x 480 at 10 fps, two render workers each, thermal 160 x 120 at 8.7 fps: four streams); the tile server on
8765. The two plan files are written to `sim/world/out/formation/qgc/plans/formation-PLAN-v1.plan` (for
vehicle 1) and `formation-PLAN-v2.plan` (for vehicle 2). Same options as the gorge session (`NOISE`, `SEED`,
`WIND`, `VIDEO=off`, `RGB`, `RGB_WORKERS`, `ORIGIN`), and the ports (`GCS_PORT`, `TILES_PORT`, `POSE_PORT1`,
`POSE_PORT2`, `RGB_PORT1`, `THERMAL_PORT1`, `RGB_PORT2`, `THERMAL_PORT2`); it refuses to start when the tile or
pose ports are taken.

### How QGroundControl 5.1.5 handles two vehicles on one UDP link (from its source)

Paths relative to `sim/mavlink/qgc-5.1.5/src`.

- **Two vehicles, one link.** Every HEARTBEAT from component 1 of a new system id creates a Vehicle
  (`Vehicle/MultiVehicleManager.cc` `_vehicleHeartbeatInfo`; `multiVehicleEnabled()` is true,
  `API/QGCOptions.h`); components 100 (the cameras) never become vehicles. The first vehicle heard becomes
  the active one; the second only shows "Connected to Vehicle 2". The active vehicle changes only when the
  user picks another (or the active one is lost). Each Vehicle downloads its own parameters and mission, and
  requests its own streams (REQUEST_DATA_STREAM with its system id).
- **One link, every frame to every sender.** `Comms/UDPLink.cc` sends every frame QGroundControl writes to
  every address it has heard from (both controllers, both cameras), and never forwards one vehicle's frames
  to another. Each controller therefore receives the commands addressed to the other and acts only on its
  own system id (leanfc's services check `target_system`; the cameras check system and component).
- **Choosing the active vehicle.** The toolbar's vehicle indicator ("Vehicle 1", `Toolbar/MultiVehicleSelector.qml`):
  click it, then the vehicle's button. With more than one vehicle the Fly view also shows the Multi-Vehicle
  panel at the top right (`FlyView/FlyViewTopRightPanel.qml`, on by default: "Enable Multi-Vehicle Panel"
  in the same drawer); clicking a vehicle's card there selects it for the panel's actions, it does not
  make it active. The map shows both vehicles (the inactive one at 50 % opacity, both labeled "Vehicle N").
- **Video follows the active vehicle, but the main view's port does not.** `VideoManager` takes the
  streams of the active vehicle's camera (`VideoManager.cc` `_setActiveVehicle`, `_videoSourceChanged`),
  and on a switch sends VIDEO_STOP_STREAMING to the old camera and VIDEO_START_STREAMING to the new one
  (RGB stream only; this simulated camera acknowledges both and keeps streaming). The thermal receiver
  uses the uri the camera announces, so it shows vehicle 1's thermal (5602) or vehicle 2's (5606). The
  main receiver's URL is replaced, after the announced one, by the setting Application Settings > Video >
  **UDP URL** (default `0.0.0.0:5600`; `_updateSettings`, `QGC-CAMERA.md` item 18). So with vehicle 2
  active the main view still shows UDP 5600, vehicle 1's RGB, with vehicle 2's thermal blended over it.
  To see vehicle 2's RGB, set that UDP URL to `0.0.0.0:5604` while vehicle 2 is active (and back to
  `0.0.0.0:5600` for vehicle 1). This is a setting the user changes; nothing here writes it.
- **Plans go to the active vehicle.** Plan view's Upload sends to the active vehicle only
  (`PlanMasterController::sendToVehicle`); there is no vehicle choice in the Plan view. When the active
  vehicle changes while the Plan view holds a plan that was opened from a file and not edited, the editor
  silently shows the new vehicle's mission instead (`PlanMasterController::_activeVehicleChanged`), so
  switch first, then open and upload.
- **Starting both.** The Fly view's Start Mission acts on the active vehicle only. The Multi-Vehicle
  panel has Arm, Disarm, Start and Pause for the selected vehicles (`GuidedActionsController.qml`
  `actionMVArm`, `actionMVStartMission`): Start sends MISSION_START to each selected vehicle that is
  armed and not in AUTO, one after the other. leanfc accepts MISSION_START from any mode when armed on the
  ground with a mission (it switches to AUTO and takes off), as ArduCopter does.

### Manual steps

1. `PLAN=staggered sh sim/world/fly_formation_qgc.sh` (or `abreast`); wait for its "Plans: ..." line.
2. Open QGroundControl. Both vehicles appear within a few seconds ("Connected to Vehicle 2"); both become
   "Ready To Fly" about 3 s after the simulation starts, and both cameras are discovered (the video shows
   vehicle 1's RGB with its thermal blended over it).
3. Vehicle 1 is active. Plan view > Open > `sim/world/out/formation/qgc/plans/formation-PLAN-v1.plan` >
   **Upload**.
4. Toolbar vehicle indicator > **Vehicle 2**. Then (in this order) Plan view > Open >
   `formation-PLAN-v2.plan` > **Upload**. Each plan holds one vehicle's route; uploading a plan to the
   wrong vehicle would put both on the same route.
5. Fly view, Multi-Vehicle panel (top right): **Select All**, then **Arm** (slide to confirm), then within
   10 s (DISARM_DELAY: an armed vehicle that has not taken off disarms after 10 s) **Start** (slide to
   confirm). Both take off together, fly their routes and land at the end of the gorge.
   Alternatively start each from the Fly view's Start Mission with the vehicle active, vehicle 1 (the lead)
   first: the second then starts a few seconds later. In the abreast plan a late start only moves the
   vehicles apart along the gorge; in the staggered plan vehicle 2 starting first brings it toward vehicle
   1's side (closest 1.26 m in the batch flights, when it starts 1.25 s early; `sim/world/README.md`).
6. Ctrl-C in the terminal ends the session and writes `sim/world/out/formation/qgc/` (formation.csv with the
   separation, contacts and clearances, v1.csv, v2.csv, formation.json with the real-time factor,
   camera1.json, camera2.json).

The scripted equivalent, on other ports, is `sim/world/test_formation_flight.py` (`--start mv` for the
Multi-Vehicle panel's Arm and Start). The real application has not been run against this session and
nobody has clicked through these steps.
