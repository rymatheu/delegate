#!/usr/bin/env bash
# Fly a gorge scenario on the ArduPilot harness stack (real EKF3, sensor noise on) from QGroundControl, with live video.
#
#   ardupilot/fly_qgc.sh [abreast|staggered] [--udp-port 14550] [--video-port 5600] [--pose-port 14601]
#                        [--record [DIR]] [--out DIR] [--no-video]
#   ardupilot/fly_qgc.sh PORT          (one vehicle, MAVLink to PORT; the earlier form)
#
#   (no scenario)  one X500 through the gorge: ap_full_ekf
#   abreast        two X500s side by side: ap_formation, MAVLink systems 1 and 2
#   staggered      two X500s staggered, vehicle 2 rear and nose-backward: ap_formation
#
# Builds nothing (README.md, "Build"). It starts the scenario's node behind `harness serve` (monitors on every clause
# of every instance at every tick), steps it in real time (ardupilot/qgc_bridge.py) and sends each vehicle's MAVLink stream from its own local
# UDP socket to 127.0.0.1:--udp-port, where QGroundControl's default UDP link listens; QGroundControl answers each
# vehicle at the address its stream comes from. The mission is not onboard: upload it in QGroundControl from the plan
# files of sim/plans (one per vehicle). Video: sim/cameras.sh, a separate process (one MAVLink camera per vehicle,
# component 100 of its system; RTP/H.264 from --video-port), fed with each vehicle's true pose from the session; it
# does not change the flight. Stop with Ctrl-C or SIGTERM: the sockets are closed, the cameras end with this process.
# Nothing is kept by default: the monitors' log and the cameras' work files go to a temporary directory (mktemp -d),
# removed on every exit. --record [DIR] (default ardupilot/out/SCENARIO) keeps them in DIR (serve.log, the cameras'
# files) and appends the session's `monitored` record to the node's ledger; --out DIR keeps the files only.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
HARNESS="$(cd "$HERE/.." && pwd)"
SIM="$(cd "$HARNESS/../sim" && pwd)"
scenario=single; udp_port=14550; video_port=5600; pose_port=14601; out=""; record=0; keep=0; video=1
case "${1:-}" in
  abreast|staggered|single) scenario="$1"; shift ;;
  ''|-*) ;;
  *[!0-9]*) echo "usage: ardupilot/fly_qgc.sh [abreast|staggered] [--udp-port P] [--video-port V] [--pose-port X] [--out DIR] [--no-video]" >&2; exit 2 ;;
  *) udp_port="$1"; shift ;;
esac
while [ $# -gt 0 ]; do
  case "$1" in
    --udp-port) udp_port="$2"; shift ;;
    --video-port) video_port="$2"; shift ;;
    --pose-port) pose_port="$2"; shift ;;
    --out) out="$2"; keep=1; shift ;;
    --record) record=1; case "${2:-}" in ''|-*) ;; *) out="$2"; shift ;; esac ;;
    --no-video) video=0 ;;
    *) echo "fly_qgc.sh: unknown option $1" >&2; exit 2 ;;
  esac
  shift
done
missing=0
for f in .lake/build/bin/harness build/modules/supervisor/supervisor build/modules/estimator/estimator \
         build/modules/position/position build/modules/attitude/attitude build/modules/guidance/guidance \
         build/modules/loiter/loiter build/modules/mixer/mixer build/modules/rate_pid/rate_pid \
         build/modules/plant_sim/plant_sim build/modules/plant_formation/plant_formation \
         build/gen/supervisor/py/apm.py; do
  if [ ! -e "$HARNESS/$f" ]; then echo "fly_qgc.sh: $f is missing" >&2; missing=1; fi
done
[ "$missing" = 0 ] || { echo "fly_qgc.sh: build first (README.md, \"Build\"); nothing was started" >&2; exit 1; }
case "$scenario" in
  single) what="one X500 (ap_full_ekf), MAVLink system 1; plan sim/plans/gorge.plan" ;;
  abreast) what="two X500s side by side (ap_formation), systems 1 and 2; plans sim/plans/formation-abreast-v1.plan, -v2.plan" ;;
  staggered) what="two X500s staggered, vehicle 2 rear and nose-backward (ap_formation), systems 1 and 2; plans sim/plans/formation-staggered-v1.plan, -v2.plan" ;;
esac
cat <<MSG
ArduPilot harness stack, gorge scenario $scenario: $what.
Real EKF3, sensor noise on; MAVLink to UDP 127.0.0.1:$udp_port.
What to do:
  1. Have QGroundControl running (its default UDP link listens on 14550).
  2. The vehicle(s) appear by themselves. EKF3 needs about 30 s for a GPS origin (the map then shows the gorge).
  3. Plan view, for each vehicle: open its plan file (above), Upload. Fly view: arm and start the mission
     (Takeoff, then Start Mission; or GUIDED, arm, takeoff, then AUTO). No RC is simulated.
  4. Video: the camera of each vehicle appears in the video widget (two vehicles: the active vehicle's).
  5. Ctrl-C here (or SIGTERM) stops the session.
MSG
TMP="$(mktemp -d "${TMPDIR:-/tmp}/fly_qgc.XXXXXX")"
PID=""
cleanup() { [ -n "$PID" ] && kill -TERM "$PID" 2>/dev/null && wait "$PID" 2>/dev/null; rm -rf "$TMP"; }
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
if [ "$record" = 1 ]; then
  out="${out:-$HERE/out/$scenario}"
  mkdir -p "$out"
  export HARNESS_RECORD=1 HARNESS_SERVE_LOG="$out/serve.log"
  echo "Recording: monitors' log, cameras' files in $out; the session's ledger record when it ends."
elif [ "$keep" = 1 ]; then
  # --out DIR alone (as sim/checks/video_check.py passes it): the session's files in DIR, no ledger record
  mkdir -p "$out"
  unset HARNESS_RECORD
  export HARNESS_SERVE_LOG="$out/serve.log"
  echo "Session files in $out; no ledger record (--record adds it)."
else
  out="$TMP"
  unset HARNESS_RECORD
  export HARNESS_SERVE_LOG="$TMP/serve.log"
  echo "Nothing is recorded (--record keeps the session)."
fi
pose_arg=()
if [ "$video" = 1 ]; then
  if "$SIM/cameras.sh" "$scenario" --parent $$ --udp-port "$udp_port" --video-port "$video_port" \
       --pose-port "$pose_port" --out "$out"; then
    pose_arg=(--pose-port "$pose_port")
  else
    echo "fly_qgc.sh: no video (sim/cameras.sh failed); the session runs without cameras" >&2
  fi
fi
cd "$HARNESS"
python3 -I -B "$HERE/qgc_bridge.py" "$scenario" --udp-port "$udp_port" ${pose_arg[@]+"${pose_arg[@]}"} &
PID=$!
RC=0; wait "$PID" || RC=$?
PID=""
exit $RC
