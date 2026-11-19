#!/usr/bin/env bash
# Fly the PX4 stack through the gorge from QGroundControl, with live video.
#
#   px4/fly_qgc.sh                 one X500 (px4_full)
#   px4/fly_qgc.sh abreast         two X500s side by side (px4_formation: MAVLink systems 1 and 2)
#   px4/fly_qgc.sh staggered       two X500s staggered, vehicle 2 flying nose-backward
#   options: --udp-port N (default 14550; a bare number as the first argument works too)
#            --video-port N (default 5600) --pose-port N (default 14601) --no-video --seed N
#            --record [DIR]: keep the session's files and its ledger record (default DIR px4/out/SCENARIO);
#            --out DIR: keep the files only; default: nothing kept
#
# The stack: PX4 v1.17.0, unmodified, one harness per module (sensors, EKF2, rate, attitude and
# position control, flight mode manager, land detector, control allocator, commander, navigator,
# MAVLink), served by `harness serve` (monitors on every clause), stepped
# one 400 Hz tick per 2.5 ms of wall clock (slower if the stack cannot keep up: the relay prints the
# ticks behind every simulated second). Simulator sensor noise on (seed N, default 1). The vehicle
# sends its MAVLink stream from the first tick to UDP 127.0.0.1:PORT, where QGroundControl's
# default UDP link listens (as PX4 SITL does); replies come back to the same socket. The vehicle
# binds no fixed port.
#
# Video (sim/cameras.sh of the shared simulator): one MAVLink camera per vehicle, component 100 of
# the vehicle's system id, sending from its own socket to the same ground-station port; forward RGB
# (640 x 480, 10 fps) to UDP N and thermal to N + 2 (two vehicles: both RGB on N, the active
# vehicle's only; thermal N + 2 and N + 6). The relay feeds each camera the vehicle's true pose at
# 100 Hz; the camera never changes the flight. Without the video environment the session runs
# without video.
#
# The mission is uploaded from QGroundControl (Plan view, open the plan, Upload): px4/plans/gorge.plan,
# or px4/plans/formation-PLAN-v1.plan for vehicle 1 and -v2.plan for vehicle 2 (made from the
# simulator's plans by px4/gorge/make_plans.py). Then arm and start the mission (Fly view, "Start
# Mission"); PX4 lands and disarms by itself. Stop with Ctrl-C or SIGTERM (vehicles and cameras end).
#
# Nothing is kept by default: the monitors' log, the truth file and the cameras' work files go to a temporary
# directory (mktemp -d), removed on every exit. With --record [DIR] they stay in DIR (serve.log, truth.csv, the
# cameras' files) and the session's `monitored` record is appended to the node's ledger.
#
# Environment: SIM_DIR, the shared simulator (default: sim/ at the repository root).
set -euo pipefail
PX4_DIR="$(cd "$(dirname "$0")" && pwd)"
HARNESS="$(cd "$PX4_DIR/.." && pwd)"
ROOT="$(cd "$HARNESS/.." && pwd)"
SIM_DIR="${SIM_DIR:-$ROOT/sim}"
SCEN=single
case "${1:-}" in
  abreast|staggered|single) SCEN="$1"; shift ;;
  ''|-*) ;;
  *[!0-9]*) echo "usage: px4/fly_qgc.sh [abreast|staggered] [--udp-port N] [--video-port N] [--pose-port N] [--no-video] [--seed N] [--record [DIR]] [--out DIR]" >&2; exit 2 ;;
  *) set -- --udp-port "$@" ;;
esac
PORT=14550; VIDEO=5600; POSE=14601; NOVIDEO=0; SEED=1; OUT=""; RECORD=0; KEEP=0
while [ $# -gt 0 ]; do
  case "$1" in
    --udp-port) PORT="$2"; shift ;;
    --video-port) VIDEO="$2"; shift ;;
    --pose-port) POSE="$2"; shift ;;
    --no-video) NOVIDEO=1 ;;
    --seed) SEED="$2"; shift ;;
    --out) OUT="$2"; KEEP=1; shift ;;
    --record) RECORD=1; case "${2:-}" in ''|-*) ;; *) OUT="$2"; shift ;; esac ;;
    *) echo "fly_qgc.sh: unknown option $1" >&2; exit 2 ;;
  esac
  shift
done
missing=0
for f in .lake/build/bin/harness build/modules/plant_sim/plant_sim build/modules/px4_sim_in/px4_sim_in \
         build/modules/px4_sensors/px4_sensors build/modules/px4_rate/px4_rate \
         build/modules/px4_alloc/px4_alloc build/modules/px4_ekf2/px4_ekf2 build/modules/px4_att/px4_att \
         build/modules/px4_mavlink/px4_mavlink build/modules/px4_navigator/px4_navigator \
         build/modules/px4_fmm/px4_fmm build/modules/px4_pos/px4_pos build/modules/px4_land/px4_land \
         build/modules/px4_commander/px4_commander build/modules/px4_merge_ack/px4_merge_ack \
         build/modules/px4_sim_out/px4_sim_out; do
  if [ ! -e "$HARNESS/$f" ]; then echo "fly_qgc.sh: $f is missing" >&2; missing=1; fi
done
if [ "$missing" = 1 ]; then
  echo "fly_qgc.sh: build first (README.md, Build); nothing was started" >&2
  exit 1
fi
TMP="$(mktemp -d "${TMPDIR:-/tmp}/px4_fly_qgc.XXXXXX")"
PID=""
cleanup() { [ -n "$PID" ] && kill -TERM "$PID" 2>/dev/null && wait "$PID" 2>/dev/null; rm -rf "$TMP"; }
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
if [ "$RECORD" = 1 ]; then
  OUT="${OUT:-$PX4_DIR/out/$SCEN}"
  export HARNESS_RECORD=1
elif [ "$KEEP" = 1 ]; then
  unset HARNESS_RECORD     # --out DIR alone (as sim/checks/video_check.py passes it): files in DIR, no ledger record
else
  OUT="$TMP"
  unset HARNESS_RECORD
fi
mkdir -p "$OUT"
export HARNESS_SERVE_LOG="${HARNESS_SERVE_LOG:-$OUT/serve.log}"   # a check may name its own
cd "$HARNESS"
if [ "$SCEN" = single ]; then
  PLANS="px4/plans/gorge.plan"
  WHAT="one X500 (px4_full, MAVLink system 1)"
else
  PLANS="px4/plans/formation-$SCEN-v1.plan (vehicle 1), px4/plans/formation-$SCEN-v2.plan (vehicle 2)"
  WHAT="two X500s, formation $SCEN (two px4_full stacks, MAVLink systems 1 and 2)"
fi
POSE_ARG=()
if [ "$NOVIDEO" = 0 ]; then
  if "$SIM_DIR/cameras.sh" "$SCEN" --parent $$ --udp-port "$PORT" --video-port "$VIDEO" --pose-port "$POSE" --out "$OUT"; then
    POSE_ARG=(--pose-port "$POSE")
  else
    echo "fly_qgc.sh: starting without video"
  fi
fi
cat <<MSG
PX4 harness stack through the gorge: $WHAT, PX4 v1.17.0 unmodified, one harness per module,
simulator sensor noise on; MAVLink to UDP 127.0.0.1:$PORT. $( [ "$RECORD" = 1 ] && echo "Recording in $OUT (and the session's ledger record)." || { [ "$KEEP" = 1 ] && echo "Session files in $OUT; no ledger record." || echo "Nothing is recorded (--record keeps the session)."; })
What to do:
  1. Have QGroundControl running (its default UDP link listens on 14550; for another port, give
     --udp-port N). The stack takes about 20 s to boot; each vehicle then appears at its first
     heartbeat, and EKF2 has a GPS origin about 10 s of vehicle time later.
  2. Plan view: open $PLANS, upload (with two vehicles: select each vehicle, open its plan, upload).
  3. Fly view: arm and start the mission ("Start Mission"). PX4 flies the gorge, lands and disarms.
  4. Ctrl-C here (or SIGTERM) stops the vehicles and the cameras.
MSG
if [ "$SCEN" = single ]; then
  python3 -I -B px4/harnesses/px4_full/dev/relay.py --gcs "127.0.0.1:$PORT" --set noise_seed="$SEED" \
    --truth "$OUT/truth.csv" --every 4 ${POSE_ARG[@]+"${POSE_ARG[@]}"} &
else
  F=1; [ "$SCEN" = staggered ] && F=2
  python3 -I -B px4/harnesses/px4_full/dev/relay.py --node px4_formation --gcs "127.0.0.1:$PORT" \
    --set formation=$F --set noise_seed="$SEED" --truth "$OUT/truth.csv" --every 4 ${POSE_ARG[@]+"${POSE_ARG[@]}"} &
fi
PID=$!
RC=0; wait "$PID" || RC=$?
PID=""
exit $RC
