#!/usr/bin/env bash
# Fly leanfc through the gorge from QGroundControl, in real time, with live video.
#
#   ./fly_qgc.sh [single|abreast|staggered] [--udp-port 14550] [--video-port 5600] [--pose-port 14601]
#                [--out DIR] [--no-video] [--tiles-port N] [OPTIONS of the session program ...]
#
#   single     one X500 (MAVLink system 1)                                                       (default)
#   abreast    two X500s side by side (systems 1 and 2)
#   staggered  two X500s, vehicle 2 behind and to the side, flying nose-backward (nav.yawReverse 1)
#
# The vehicles rest on the gorge floor, disarmed, each with its whole mission onboard (takeoff, the route as spline
# waypoints, land), so QGroundControl's Start Mission (one vehicle) or Select All, Arm, Start (Multi-Vehicle panel)
# flies it with no upload. The same missions are written as plan files into the session folder (gorge.plan, or
# plans/formation-SCENARIO-v1.plan and -v2.plan); uploading them is optional.
# MAVLink goes to 127.0.0.1:--udp-port (QGroundControl's default 14550). The cameras (the shared sim/cameras.sh) are
# MAVLink camera components 1/100 and 2/100 with RTP/H.264 streams on --video-port and up; --no-video runs without
# them. --tiles-port N also starts a map tile server of the gorge on http://127.0.0.1:N/{z}/{x}/{y}.png (QGroundControl
# needs a non-default map setting to use it). Environment: NOISE (field|none, default field), SEED (0), WIND ("MEAN
# GUST", off), ORIGIN ("LAT LON ALT"), SPEED (pacing, default 1 = real time). Ctrl-C or SIGTERM ends the session;
# records in the session folder (default out/qgc-SCENARIO).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(dirname "$HERE")"
PY="${SIM_PYTHON:-$REPO/sim/.venv/bin/python}"
cd "$HERE"
scenario=single
case "${1:-}" in single|abreast|staggered) scenario="$1"; shift ;; esac
udp_port=14550; video_port=5600; pose_port=14601; out=""; video=on; tiles_port=""; extra=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --udp-port) udp_port="$2"; shift ;;
    --video-port) video_port="$2"; shift ;;
    --pose-port) pose_port="$2"; shift ;;
    --out) out="$2"; shift ;;
    --no-video) video=off ;;
    --tiles-port) tiles_port="$2"; shift ;;
    *) extra+=("$1") ;;
  esac
  shift
done
out="${out:-out/qgc-$scenario}"
NOISE="${NOISE:-field}"; SEED="${SEED:-0}"; SPEED="${SPEED:-1}"
[[ -x "$PY" ]] || { echo "no simulator environment at $PY: run sim/setup.sh at the repository root" >&2; exit 1; }
LEAN_NUM_THREADS=1 lake build leanfc >/dev/null || { echo "lake build failed" >&2; exit 1; }
mkdir -p "$out"
params=(--params params/x500.params --params params/ground.params)
orig=(); [[ -n "${ORIGIN:-}" ]] && orig=(--origin $ORIGIN)
wind=(); [[ -n "${WIND:-}" ]] && wind=(--wind $WIND)
if [[ "$video" == on ]]; then
  if ! "$REPO/sim/cameras.sh" "$scenario" --parent $$ --udp-port "$udp_port" --video-port "$video_port" \
      --pose-port "$pose_port" --out "$out"; then
    echo "no video (see above): the session runs without cameras" >&2; video=off
  fi
fi
if [[ -n "$tiles_port" ]]; then
  "$PY" -B sim/flights/tile_server.py --port "$tiles_port" "${params[@]}" ${orig[@]+"${orig[@]}"} --log "$out/tiles.log" \
    > "$out/tiles.out" 2>&1 &
  tpid=$!
  ( while kill -0 $$ 2>/dev/null; do sleep 0.5; done; kill "$tpid" 2>/dev/null ) &
  echo "Map tiles: http://127.0.0.1:$tiles_port/{z}/{x}/{y}.png"
fi
pp=0; [[ "$video" == on ]] && pp="$pose_port"
if [[ "$scenario" == single ]]; then
  echo "leanfc: one X500 on the gorge floor, MAVLink system 1 -> 127.0.0.1:$udp_port, noise $NOISE, seed $SEED, speed $SPEED."
  echo "Mission onboard: Start Mission works with no upload (same items: $out/gorge.plan). Ctrl-C ends the session."
  exec "$PY" -B sim/flights/gorge_session.py ${wind[@]+"${wind[@]}"} --pose-port "$pp" --session-out "$out" \
    "${params[@]}" ${orig[@]+"${orig[@]}"} --noise "$NOISE" --seed "$SEED" --ground --mav --mav-port "$udp_port" \
    --realtime "$SPEED" --trace-vehicle --seconds 7200 --mav-log "$out/vehicle.log" --out "$out/flight.csv" \
    ${extra[@]+"${extra[@]}"}
else
  poses=(); [[ "$video" == on ]] && poses=(--pose-ports "$pose_port" "$((pose_port + 2))")
  echo "leanfc: two X500s ($scenario) on the gorge floor, MAVLink systems 1 and 2 -> 127.0.0.1:$udp_port, noise $NOISE, seed $SEED, speed $SPEED."
  echo "Missions onboard: Select All, Arm, Start (Multi-Vehicle panel) works with no upload (same items: $out/plans/formation-$scenario-v1.plan, -v2.plan). Ctrl-C ends the session."
  exec "$PY" -B sim/flights/formation.py --session --plan "$scenario" ${wind[@]+"${wind[@]}"} ${poses[@]+"${poses[@]}"} \
    --mav-port "$udp_port" ${orig[@]+"${orig[@]}"} --noise "$NOISE" --seed "$SEED" --realtime "$SPEED" --seconds 7200 \
    --out "$out" ${extra[@]+"${extra[@]}"}
fi
