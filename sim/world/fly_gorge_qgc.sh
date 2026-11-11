#!/bin/sh
# Fly the real leanfc controller in the gorge from QGroundControl, with live video and the gorge as map.
# Starts, in real time (see sim/mavlink/QGC.md, "The gorge session"):
#   - the gorge world in gym-pybullet-drones with the X500 resting on the floor at the mission start,
#     disarmed, and the controller (.lake/build/bin/leanfc, params/x500.params + params/ground.params + the
#     gorge overlay) with its MAVLink link to QGroundControl's UDP port 14550 (sim/world/gorge_session.py);
#   - the camera payload, MAVLink component 1/100, with RTP/H.264 streams to UDP 5600 (forward RGB) and 5602
#     (forward thermal) (sim/world/camera_component.py; its Python environment sim/world/.venv-video is made
#     on the first run with uv: PyAV and NumPy);
#   - the map tile server on http://127.0.0.1:8765/{z}/{x}/{y}.png (sim/world/tile_server.py).
# Then open QGroundControl. Ctrl-C ends everything; outputs in sim/world/out/qgc/ (flight.csv, vehicle.log,
# session.json, camera.json, gorge.plan, ...).
#
#   sh sim/world/fly_gorge_qgc.sh
#   WIND="4 1" sh sim/world/fly_gorge_qgc.sh                 # mean wind 4 m/s up-gorge, gusts 1 m/s
#   ORIGIN="46.5576 7.8350 2061" sh sim/world/fly_gorge_qgc.sh  # another geodetic origin (default: ground.params)
#   NOISE=none SEED=3 VIDEO=off RGB=320x240@20 RGB_WORKERS=1 sh sim/world/fly_gorge_qgc.sh
cd "$(dirname "$0")/../.." || exit 1
PY=${PY:-/Users/ryan/Research/cpp2lean/sim/.venv/bin/python}
VPY=sim/world/.venv-video/bin/python
NOISE=${NOISE:-field}
SEED=${SEED:-0}
VIDEO=${VIDEO:-on}
RGB=${RGB:-640x480@15}
RGB_WORKERS=${RGB_WORKERS:-2}
GCS_PORT=${GCS_PORT:-14550}
TILES_PORT=${TILES_PORT:-8765}
POSE_PORT=${POSE_PORT:-14601}
RGB_PORT=${RGB_PORT:-5600}
THERMAL_PORT=${THERMAL_PORT:-5602}
SECONDS_MAX=${SECONDS_MAX:-7200}
OUT=${OUT:-sim/world/out/qgc}
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
if [ "$VIDEO" = on ]; then
  "$VPY" sim/world/camera_component.py --gcs "127.0.0.1:$GCS_PORT" --pose-port "$POSE_PORT" --rgb "$RGB" \
    --rgb-workers "$RGB_WORKERS" --rgb-port "$RGB_PORT" --thermal-port "$THERMAL_PORT" --seed "$SEED" --stats "$OUT/camera.json" --log "$OUT/camera.log" > "$OUT/camera.out" 2>&1 &
  PIDS="$PIDS $!"
else
  POSE_PORT=0
fi
trap 'kill $PIDS 2>/dev/null' EXIT INT TERM
echo "leanfc: x500 on the gorge floor (params/ground.params origin${ORIGIN:+ overridden: $ORIGIN}), noise $NOISE, seed $SEED, wind ${WIND:-off}, video $VIDEO, real time."
echo "Map: QGroundControl Application Settings > Maps > Provider CustomURL, Type Custom; Server URL http://127.0.0.1:$TILES_PORT/{z}/{x}/{y}.png"
echo "Plan: $OUT/gorge.plan. Open QGroundControl now; Ctrl-C here ends the session."
"$PY" -B sim/world/gorge_session.py ${WIND:+--wind $WIND} --pose-port "$POSE_PORT" --session-out "$OUT" $PARAMS $ORIG \
  --noise "$NOISE" --seed "$SEED" --ground --mav --mav-port "$GCS_PORT" --realtime 1 --trace-vehicle \
  --seconds "$SECONDS_MAX" --mav-log "$OUT/vehicle.log" --out "$OUT/flight.csv" "$@"
