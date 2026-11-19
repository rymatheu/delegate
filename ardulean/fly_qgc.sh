#!/usr/bin/env bash
# Fly ArduLean in the gorge in real time for QGroundControl (MAVLink on UDP 14550), with live video from each
# vehicle's camera. Ctrl-C (or SIGTERM) ends the session; its record is kept in out/qgc/.
#
#   ./fly_qgc.sh              one X500
#   ./fly_qgc.sh abreast      two X500s side by side (MAVLink systems 1 and 2)
#   ./fly_qgc.sh staggered    two X500s staggered, vehicle 2 flying nose-backward
#
# Options (the others go to the flight program, for example --seed N, --duration S):
#   --udp-port N      QGroundControl's MAVLink port (default 14550, or $MAVLINK_PORT)
#   --video-port N    first video port (default 5600, or $VIDEO_PORT): RGB N, thermal N + 2 (vehicle 2: N + 6)
#   --pose-port N     camera pose port of vehicle 1 (default 14601; vehicle 2: N + 2)
#   --out DIR         the session's folder (default out/qgc/<scenario>-<date>-<time>)
#   --no-video        no cameras
# The mission is uploaded from QGroundControl: ../sim/plans/gorge.plan, or formation-<scenario>-v1.plan to vehicle 1
# and -v2.plan to vehicle 2. The executable is .lake/build/bin/ardulean ($LEAN_VEHICLE_EXE overrides it).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
SIM="$(cd "$HERE/../sim" && pwd)"
cd "$HERE"
PY="${SIM_PYTHON:-$SIM/.venv/bin/python}"
EXE="${LEAN_VEHICLE_EXE:-.lake/build/bin/ardulean}"
if [[ ! -x "$EXE" ]]; then
  echo "fly_qgc.sh: the ArduLean executable $EXE is missing; build it first (README.md, Build)." >&2
  exit 1
fi
if [[ ! -x "$PY" ]] || ! "$PY" -c "import pybullet, gym_pybullet_drones, pymavlink" 2>/dev/null; then
  echo "fly_qgc.sh: the simulator's Python environment ($PY) is missing; run ../sim/setup.sh first." >&2
  exit 1
fi
plan=""
case "${1:-}" in
  abreast|staggered) plan="$1"; shift ;;
  single) shift ;;
esac
video=on; video_port="${VIDEO_PORT:-5600}"; pose_port=14601; udp_port="${MAVLINK_PORT:-14550}"; out=""; cam_extra=()
args=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --no-video) video=off ;;
    --video-port) video_port="$2"; shift ;;
    --pose-port) pose_port="$2"; shift ;;
    --udp-port) udp_port="$2"; shift ;;
    --out) out="$2"; shift ;;
    --noses-forward) cam_extra=(--noses-forward); args+=("$1") ;;
    *) args+=("$1") ;;
  esac
  shift
done
[[ -n "$out" ]] || out="out/qgc/${plan:-single}-$(date +%Y%m%d-%H%M%S)"
mkdir -p "$out"
pose_arg=()
if [[ "$video" == on ]]; then
  # the cameras watch this script's pid, which the flight program keeps (exec below)
  if "$SIM/cameras.sh" "${plan:-single}" --parent $$ --udp-port "$udp_port" --video-port "$video_port" \
       --pose-port "$pose_port" --out "$out" ${cam_extra[@]+"${cam_extra[@]}"}; then
    if [[ -n "$plan" ]]; then pose_arg=(--pose-ports "$pose_port" "$((pose_port + 2))"); else pose_arg=(--pose-port "$pose_port"); fi
  else
    echo "fly_qgc.sh: starting without video."
  fi
fi
if [[ -n "$plan" ]]; then
  echo "Running: two X500s in the gorge, formation '$plan', each flown by its own ArduLean (MAVLink systems 1 and 2), in real time."
  echo "Open QGroundControl (UDP $udp_port). Upload ../sim/plans/formation-$plan-v1.plan to vehicle 1 and -v2.plan to vehicle 2."
  echo "Ctrl-C to stop."
  exec "$PY" sim/fly_gorge_formation.py --udp --plan "$plan" --udp-port "$udp_port" --out "$out" \
    ${pose_arg[@]+"${pose_arg[@]}"} ${args[@]+"${args[@]}"}
else
  echo "Running: one X500 in the gorge, flown by ArduLean, in real time."
  echo "Open QGroundControl (UDP $udp_port). Upload ../sim/plans/gorge.plan."
  echo "Ctrl-C to stop."
  exec "$PY" sim/fly_gorge.py --udp --udp-port "$udp_port" --out "$out" \
    ${pose_arg[@]+"${pose_arg[@]}"} ${args[@]+"${args[@]}"}
fi
