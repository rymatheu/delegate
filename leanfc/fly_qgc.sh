#!/usr/bin/env bash
# Fly leanfc through the gorge from QGroundControl, in real time, with live video.
#
#   ./fly_qgc.sh [single|abreast|staggered] [--udp-port 14550] [--video-port 5600] [--pose-port 14601]
#                [--record [DIR] | --out DIR] [--no-video] [--tiles-port N] [OPTIONS of the session program ...]
#
#   single     one X500 (MAVLink system 1)                                                       (default)
#   abreast    two X500s side by side (systems 1 and 2)
#   staggered  two X500s, vehicle 2 behind and to the side, flying nose-backward (nav.yawReverse 1)
#
# The vehicles rest on the gorge floor, disarmed, each with its whole mission onboard (takeoff, the route as spline
# waypoints, land), so QGroundControl's Start Mission (one vehicle) or Select All, Arm, Start (Multi-Vehicle panel)
# flies it with no upload. The same missions are in plans/ (uploading them is optional).
# MAVLink goes to 127.0.0.1:--udp-port (QGroundControl's default 14550). The cameras (the shared sim/cameras.sh) are
# MAVLink camera components 1/100 and 2/100 with RTP/H.264 streams on --video-port and up; --no-video runs without
# them. --tiles-port N also starts a map tile server of the gorge on http://127.0.0.1:N/{z}/{x}/{y}.png.
# Environment: NOISE (field|none, default field), SEED (0), WIND ("MEAN GUST", off), ORIGIN ("LAT LON ALT"), SPEED
# (pacing, default 1 = real time). Ctrl-C or SIGTERM ends the session.
#
# Nothing is written to disk by default: the controllers' parameter overlays live in one temporary directory, removed
# on exit. --record [DIR] (default out/qgc-SCENARIO; --out DIR is the same) keeps the records there: flight.csv or
# formation.csv, v1.csv, v2.csv, the MAVLink logs, the overlays and plan files, the camera statistics.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(dirname "$HERE")"
PY="${SIM_PYTHON:-$REPO/sim/.venv/bin/python}"
export PYTHONDONTWRITEBYTECODE=1
cd "$HERE"
scenario=single
case "${1:-}" in single|abreast|staggered) scenario="$1"; shift ;; esac
udp_port=14550; video_port=5600; pose_port=14601; rec=""; video=on; tiles_port=""; extra=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --udp-port) udp_port="$2"; shift ;;
    --video-port) video_port="$2"; shift ;;
    --pose-port) pose_port="$2"; shift ;;
    --out) rec="$2"; shift ;;
    --record) if [[ $# -gt 1 && "$2" != --* ]]; then rec="$2"; shift; else rec="out/qgc-$scenario"; fi ;;
    --no-video) video=off ;;
    --tiles-port) tiles_port="$2"; shift ;;
    *) extra+=("$1") ;;
  esac
  shift
done
NOISE="${NOISE:-field}"; SEED="${SEED:-0}"; SPEED="${SPEED:-1}"
[[ -x "$PY" ]] || { echo "no simulator environment at $PY: run sim/setup.sh at the repository root" >&2; exit 1; }
LEAN_NUM_THREADS=1 lake build leanfc >/dev/null || { echo "lake build failed" >&2; exit 1; }
tmp="$(mktemp -d "${TMPDIR:-/tmp}/leanfc.XXXXXX")"
child=""; tpid=""
cleanup() {
  trap - EXIT INT TERM
  if [[ -n "$child" ]] && kill -0 "$child" 2>/dev/null; then    # the session writes its records, then ends
    kill -TERM "$child" 2>/dev/null || true
    while kill -0 "$child" 2>/dev/null; do wait "$child" 2>/dev/null || true; done
  fi
  [[ -n "$tpid" ]] && kill "$tpid" 2>/dev/null || true
  rm -rf "$tmp"
}
trap cleanup EXIT
trap 'cleanup; exit 130' INT
trap 'cleanup; exit 143' TERM
if [[ -n "$rec" ]]; then out="$rec"; else out="$tmp/session"; fi
mkdir -p "$out"
params=(--params params/x500.params --params params/ground.params)
orig=(); [[ -n "${ORIGIN:-}" ]] && orig=(--origin $ORIGIN)
wind=(); [[ -n "${WIND:-}" ]] && wind=(--wind $WIND)
if [[ "$video" == on ]]; then
  camout=(); [[ -n "$rec" ]] && camout=(--out "$out")
  if ! "$REPO/sim/cameras.sh" "$scenario" --parent $$ --udp-port "$udp_port" --video-port "$video_port" \
      --pose-port "$pose_port" ${camout[@]+"${camout[@]}"}; then
    echo "no video (see above): the session runs without cameras" >&2; video=off
  fi
fi
if [[ -n "$tiles_port" ]]; then
  tlog=/dev/null; [[ -n "$rec" ]] && tlog="$out/tiles.log"
  "$PY" -B sim/flights/tile_server.py --port "$tiles_port" "${params[@]}" ${orig[@]+"${orig[@]}"} --log "$tlog" >/dev/null 2>&1 &
  tpid=$!
  echo "Map tiles: http://127.0.0.1:$tiles_port/{z}/{x}/{y}.png"
fi
pp=0; [[ "$video" == on ]] && pp="$pose_port"
echo "Records: ${rec:-none (--record [DIR] keeps them)}."
if [[ "$scenario" == single ]]; then
  recargs=(--out none); [[ -n "$rec" ]] && recargs=(--mav-log "$out/vehicle.log" --out "$out/flight.csv")
  echo "leanfc: one X500 on the gorge floor, MAVLink system 1 -> 127.0.0.1:$udp_port, noise $NOISE, seed $SEED, speed $SPEED."
  echo "Mission onboard: Start Mission works with no upload (same items: plans/gorge.plan). Ctrl-C ends the session."
  "$PY" -B sim/flights/gorge_session.py ${wind[@]+"${wind[@]}"} --pose-port "$pp" --session-out "$out" \
    "${params[@]}" ${orig[@]+"${orig[@]}"} --noise "$NOISE" --seed "$SEED" --ground --mav --mav-port "$udp_port" \
    --realtime "$SPEED" --trace-vehicle --seconds 7200 "${recargs[@]}" ${extra[@]+"${extra[@]}"} &
else
  poses=(); [[ "$video" == on ]] && poses=(--pose-ports "$pose_port" "$((pose_port + 2))")
  recargs=(--no-record); [[ -n "$rec" ]] && recargs=()
  echo "leanfc: two X500s ($scenario) on the gorge floor, MAVLink systems 1 and 2 -> 127.0.0.1:$udp_port, noise $NOISE, seed $SEED, speed $SPEED."
  echo "Missions onboard: Select All, Arm, Start (Multi-Vehicle panel) works with no upload (same items: plans/formation-$scenario-v1.plan, -v2.plan). Ctrl-C ends the session."
  "$PY" -B sim/flights/formation.py --session --plan "$scenario" ${wind[@]+"${wind[@]}"} ${poses[@]+"${poses[@]}"} \
    --mav-port "$udp_port" ${orig[@]+"${orig[@]}"} --noise "$NOISE" --seed "$SEED" --realtime "$SPEED" --seconds 7200 \
    --out "$out" ${recargs[@]+"${recargs[@]}"} ${extra[@]+"${extra[@]}"} &
fi
child=$!
set +e
status=0
while kill -0 "$child" 2>/dev/null; do wait "$child"; done
wait "$child" 2>/dev/null; status=$?
child=""
exit "$status"
