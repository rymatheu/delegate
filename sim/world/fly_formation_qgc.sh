#!/bin/sh
# Two X500s in the gorge from QGroundControl: a formation plan flown by two independent leanfc controllers,
# with a camera payload on each vehicle and the gorge as map. Starts, in real time (sim/mavlink/QGC.md,
# "The formation session"):
#   - one gorge world in gym-pybullet-drones with both vehicles resting on the floor at their routes' starts,
#     disarmed, and two controllers (.lake/build/bin/leanfc, params/x500.params + params/ground.params + the
#     plan's overlay per vehicle), MAVLink systems 1 and 2, both to QGroundControl's UDP port 14550
#     (sim/world/formation.py --session); vehicle 2 of the staggered plan has nav.yawReverse 1;
#   - a camera payload per vehicle, MAVLink components 1/100 and 2/100, RTP/H.264 RGB and thermal streams:
#     vehicle 1 to UDP 5600 and 5602, vehicle 2 to 5604 and 5606 (sim/world/camera_component.py);
#   - the map tile server on http://127.0.0.1:8765/{z}/{x}/{y}.png (sim/world/tile_server.py).
# Writes the two plan files, OUT/plans/formation-PLAN-v1.plan (upload to vehicle 1) and -v2.plan (vehicle 2).
# Then open QGroundControl (manual steps in sim/mavlink/QGC.md). Ctrl-C ends everything; outputs in
# sim/world/out/formation/qgc/ (formation.csv, v1.csv, v2.csv, vehicle1.log, vehicle2.log, camera*.json, plans/).
#
#   PLAN=abreast sh sim/world/fly_formation_qgc.sh             # side by side, both noses forward (default)
#   PLAN=staggered sh sim/world/fly_formation_qgc.sh           # vehicle 2 behind, flying backward (rear view)
#   WIND="4 1" NOISE=none SEED=3 VIDEO=off RGB=320x240@15 RGB_WORKERS=1 sh sim/world/fly_formation_qgc.sh
cd "$(dirname "$0")/../.." || exit 1
PY=${PY:-sim/.venv/bin/python}
VPY=sim/world/.venv-video/bin/python
PLAN=${PLAN:-abreast}
NOISE=${NOISE:-field}
SEED=${SEED:-0}
VIDEO=${VIDEO:-on}
RGB=${RGB:-640x480@10}
RGB_WORKERS=${RGB_WORKERS:-2}
THERMAL_FPS=${THERMAL_FPS:-8.7}
GCS_PORT=${GCS_PORT:-14550}
TILES_PORT=${TILES_PORT:-8765}
POSE_PORT1=${POSE_PORT1:-14601}
POSE_PORT2=${POSE_PORT2:-14603}
RGB_PORT1=${RGB_PORT1:-5600}
THERMAL_PORT1=${THERMAL_PORT1:-5602}
RGB_PORT2=${RGB_PORT2:-5604}
THERMAL_PORT2=${THERMAL_PORT2:-5606}
SECONDS_MAX=${SECONDS_MAX:-7200}
OUT=${OUT:-sim/world/out/formation/qgc}
case "$PLAN" in abreast|staggered) ;; *) echo "PLAN must be abreast or staggered"; exit 1 ;; esac
# the ports this session binds (tiles: TCP; poses: UDP) must be free
"$PY" - "$TILES_PORT" "$POSE_PORT1" "$POSE_PORT2" <<'EOF' || exit 1
import socket, sys
t, *u = map(int, sys.argv[1:])
for port, kind in [(t, socket.SOCK_STREAM)] + [(q, socket.SOCK_DGRAM) for q in u]:
    s = socket.socket(socket.AF_INET, kind)
    try:
        s.bind(("127.0.0.1", port))
    except OSError:
        sys.exit(f"port {port} is in use (another session?): set TILES_PORT / POSE_PORT1 / POSE_PORT2")
    finally:
        s.close()
EOF
LEAN_NUM_THREADS=1 lake build leanfc >/dev/null || { echo "lake build failed"; exit 1; }
if [ "$VIDEO" = on ] && [ ! -x "$VPY" ]; then
  echo "creating sim/world/.venv-video (uv: PyAV, NumPy) ..."
  uv venv sim/world/.venv-video --python 3.12 >/dev/null && uv pip install --python "$VPY" av numpy >/dev/null \
    || { echo "could not create sim/world/.venv-video"; exit 1; }
fi
mkdir -p "$OUT"
PARAMS="--params params/x500.params --params params/ground.params"
ORIG=""
[ -n "$ORIGIN" ] && ORIG="--origin $ORIGIN"
PIDS=""
"$PY" -B sim/world/tile_server.py --port "$TILES_PORT" $PARAMS $ORIG --log "$OUT/tiles.log" > "$OUT/tiles.out" 2>&1 &
PIDS="$!"
POSES="--pose-ports $POSE_PORT1 $POSE_PORT2"
if [ "$VIDEO" = on ]; then
  L2="V2 forward"
  [ "$PLAN" = staggered ] && L2="V2 rear-view"
  "$VPY" sim/world/camera_component.py --sysid 1 --label "V1 forward" --gcs "127.0.0.1:$GCS_PORT" --pose-port "$POSE_PORT1" \
    --rgb "$RGB" --rgb-workers "$RGB_WORKERS" --thermal-fps "$THERMAL_FPS" --rgb-port "$RGB_PORT1" --thermal-port "$THERMAL_PORT1" \
    --seed "$SEED" --stats "$OUT/camera1.json" --log "$OUT/camera1.log" > "$OUT/camera1.out" 2>&1 &
  PIDS="$PIDS $!"
  "$VPY" sim/world/camera_component.py --sysid 2 --label "$L2" --gcs "127.0.0.1:$GCS_PORT" --pose-port "$POSE_PORT2" \
    --rgb "$RGB" --rgb-workers "$RGB_WORKERS" --thermal-fps "$THERMAL_FPS" --rgb-port "$RGB_PORT2" --thermal-port "$THERMAL_PORT2" \
    --seed "$((SEED + 100))" --stats "$OUT/camera2.json" --log "$OUT/camera2.log" > "$OUT/camera2.out" 2>&1 &
  PIDS="$PIDS $!"
else
  POSES=""
fi
trap 'kill $PIDS 2>/dev/null' EXIT INT TERM
echo "leanfc formation: plan $PLAN, two x500s on the gorge floor, systems 1 and 2 -> 127.0.0.1:$GCS_PORT, noise $NOISE, seed $SEED, wind ${WIND:-off}, video $VIDEO, real time."
echo "Video: vehicle 1 RGB $RGB_PORT1 thermal $THERMAL_PORT1; vehicle 2 RGB $RGB_PORT2 thermal $THERMAL_PORT2 (QGroundControl's main view listens on its UDP URL setting, 5600 by default)."
echo "Map: QGroundControl Application Settings > Maps > Provider CustomURL, Type Custom; Server URL http://127.0.0.1:$TILES_PORT/{z}/{x}/{y}.png"
echo "Plans: $OUT/plans/formation-$PLAN-v1.plan (vehicle 1) and $OUT/plans/formation-$PLAN-v2.plan (vehicle 2). Ctrl-C here ends the session."
"$PY" -B sim/world/formation.py --session --plan "$PLAN" ${WIND:+--wind $WIND} $POSES --mav-port "$GCS_PORT" $ORIG \
  --noise "$NOISE" --seed "$SEED" --seconds "$SECONDS_MAX" --out "$OUT" "$@"
