#!/usr/bin/env bash
# Fly ArduLean in the gorge in real time for QGroundControl (MAVLink on UDP 14550), with live video from each
# vehicle's camera. Ctrl-C (or SIGTERM) ends the session.
#
#   ./fly_qgc.sh              one X500
#   ./fly_qgc.sh abreast      two X500s side by side (MAVLink systems 1 and 2)
#   ./fly_qgc.sh staggered    two X500s staggered, vehicle 2 flying nose-backward
#
# Options (the others go to the flight program, for example --seed N, --duration S):
#   --udp-port N      QGroundControl's MAVLink port (default 14550, or $MAVLINK_PORT)
#   --video-port N    first video port (default 5600, or $VIDEO_PORT): RGB N, thermal N + 2 (vehicle 2: N + 6)
#   --pose-port N     camera pose port of vehicle 1 (default 14601; vehicle 2: N + 2)
#   --record [DIR]    keep the session's record (and the cameras' logs) in DIR (default out/qgc-<scenario>);
#   --out DIR         the same. Without either nothing is kept: one temporary directory, removed on every exit.
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
if [[ ! -x "$PY" ]] || ! "$PY" -B -c "import pybullet, gym_pybullet_drones, pymavlink" 2>/dev/null; then
  echo "fly_qgc.sh: the simulator's Python environment ($PY) is missing; run ../sim/setup.sh first." >&2
  exit 1
fi
plan=""
case "${1:-}" in
  abreast|staggered) plan="$1"; shift ;;
  single) shift ;;
esac
video=on; video_port="${VIDEO_PORT:-5600}"; pose_port=14601; udp_port="${MAVLINK_PORT:-14550}"; record=""; cam_extra=()
args=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --no-video) video=off ;;
    --video-port) video_port="$2"; shift ;;
    --pose-port) pose_port="$2"; shift ;;
    --udp-port) udp_port="$2"; shift ;;
    --record) if [[ $# -gt 1 && "$2" != --* ]]; then record="$2"; shift; else record="out/qgc-${plan:-single}"; fi ;;
    --out) record="$2"; shift ;;
    --noses-forward) cam_extra=(--noses-forward); args+=("$1") ;;
    *) args+=("$1") ;;
  esac
  shift
done
tmp="$(mktemp -d "${TMPDIR:-/tmp}/ardulean-qgc.XXXXXX")"
child=""
cleanup() { if [[ -n "$child" ]]; then kill -TERM "$child" 2>/dev/null; wait "$child" 2>/dev/null; sleep 0.5; fi; rm -rf "$tmp"; }
trap cleanup EXIT
trap 'exit 0' INT TERM
cam_out=()
if [[ -n "$record" ]]; then mkdir -p "$record"; out="$record"; cam_out=(--out "$record"); else out="$tmp/run"; mkdir -p "$out"; fi
pose_arg=()
if [[ "$video" == on ]]; then
  # the cameras watch this script's pid, which lives as long as the flight program
  if "$SIM/cameras.sh" "${plan:-single}" --parent $$ --udp-port "$udp_port" --video-port "$video_port" \
       --pose-port "$pose_port" ${cam_out[@]+"${cam_out[@]}"} ${cam_extra[@]+"${cam_extra[@]}"}; then
    if [[ -n "$plan" ]]; then pose_arg=(--pose-ports "$pose_port" "$((pose_port + 2))"); else pose_arg=(--pose-port "$pose_port"); fi
  else
    echo "fly_qgc.sh: starting without video."
  fi
fi
if [[ -n "$plan" ]]; then
  echo "Running: two X500s in the gorge, formation '$plan', each flown by its own ArduLean (MAVLink systems 1 and 2), in real time."
  echo "Open QGroundControl (UDP $udp_port). Upload ../sim/plans/formation-$plan-v1.plan to vehicle 1 and -v2.plan to vehicle 2."
  cmd=("$PY" -B sim/fly_gorge_formation.py --udp --plan "$plan")
else
  echo "Running: one X500 in the gorge, flown by ArduLean, in real time."
  echo "Open QGroundControl (UDP $udp_port). Upload ../sim/plans/gorge.plan."
  cmd=("$PY" -B sim/fly_gorge.py --udp)
fi
echo "Ctrl-C to stop.$([[ -n "$record" ]] && echo " Record: $record/" || true)"
# in the background, so that this script can pass Ctrl-C and SIGTERM on and then remove its temporary directory
"${cmd[@]}" --udp-port "$udp_port" --out "$out" ${pose_arg[@]+"${pose_arg[@]}"} ${args[@]+"${args[@]}"} &
child=$!
set +e
wait "$child"; code=$?
set -e
child=""
exit $code
