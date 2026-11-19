#!/usr/bin/env bash
# Start the live cameras of a QGroundControl session, for any flight controller (sim/README.md, "Interface for flight
# controllers"). Returns at once; the cameras run in the background until the process --parent ends (within half a
# second of it, however it ends). One process for all vehicles (sim/world/camera_component.py, in sim/.venv-video):
# per vehicle a MAVLink camera (component 100 of the vehicle's system id) on the session's MAVLink port, with a forward
# RGB stream (640 x 480, 10 fps) and a thermal stream (640 x 512, 8.7 fps), RTP/H.264 to 127.0.0.1.
#
#   sim/cameras.sh SCENARIO --parent PID [--udp-port 14550] [--video-port 5600] [--pose-port 14601] [--out DIR]
#                  [--noses-forward]
#
#   SCENARIO          single (vehicle 1), abreast or staggered (vehicles 1 and 2)
#   --parent PID      the session's process (usually the launcher's $$, kept by exec into the flight program)
#   --udp-port N      the ground station's MAVLink port (QGroundControl's 14550 by default)
#   --video-port N    single: RGB to N, thermal to N + 2. Two vehicles: both RGB streams on N (only the active
#                     vehicle's is sent: QGroundControl stops and starts them when the active vehicle changes),
#                     thermal of vehicle 1 to N + 2, of vehicle 2 to N + 6
#   --pose-port N     where vehicle 1's camera receives its poses (vehicle 2: N + 2); the flight program sends them
#                     with gorgesim.udp_bridge.PoseSender, every 4th 400 Hz tick (100 Hz)
#   --out DIR         optional: write camera.out (console), cameraN.log (MAVLink) and cameraN.json (statistics) there;
#                     without it nothing is written to disk (console to /dev/null, no logs, no statistics)
#   --noses-forward   staggered: vehicle 2's camera is labeled "V2 forward" instead of "V2 rear-view"
# Exit status: 0 cameras started; 2 no video environment (sim/setup.sh) or a pose port is in use (the launcher then
# runs the session without video, or stops). GORGE_VIDEO_PY overrides the video environment's python.
set -euo pipefail
SIM="$(cd "$(dirname "$0")" && pwd)"
VPY="${GORGE_VIDEO_PY:-$SIM/.venv-video/bin/python}"
PY="${SIM_PYTHON:-$SIM/.venv/bin/python}"
scenario="${1:-}"; shift || true
case "$scenario" in single|abreast|staggered) ;; *) echo "cameras.sh: SCENARIO must be single, abreast or staggered" >&2; exit 1 ;; esac
parent=""; udp_port=14550; video_port=5600; pose_port=14601; out=""; label2="V2 forward"
[[ "$scenario" == staggered ]] && label2="V2 rear-view"
while [[ $# -gt 0 ]]; do
  case "$1" in
    --parent) parent="$2"; shift ;;
    --udp-port) udp_port="$2"; shift ;;
    --video-port) video_port="$2"; shift ;;
    --pose-port) pose_port="$2"; shift ;;
    --out) out="$2"; shift ;;
    --noses-forward) label2="V2 forward" ;;
    *) echo "cameras.sh: unknown option $1" >&2; exit 1 ;;
  esac
  shift
done
[[ -n "$parent" ]] || { echo "cameras.sh: --parent PID is required" >&2; exit 1; }
if [[ ! -x "$VPY" ]] || ! "$VPY" -c "import av, numpy" 2>/dev/null; then
  echo "cameras.sh: no video: the video environment $VPY is missing (run sim/setup.sh)." >&2
  exit 2
fi
if [[ "$scenario" == single ]]; then pose_ports="$pose_port"; else pose_ports="$pose_port $((pose_port + 2))"; fi
if ! "$PY" - $pose_ports <<'PYEOF'
import socket, sys
for port in map(int, sys.argv[1:]):
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.bind(("127.0.0.1", port))
    except OSError:
        sys.exit(f"cameras.sh: UDP port {port} (camera poses) is in use, perhaps by another session.")
    finally:
        s.close()
PYEOF
then
  exit 2
fi
if [[ -n "$out" ]]; then
  mkdir -p "$out"; console="$out/camera.out"
  rec1=(--stats "$out/camera1.json" --log "$out/camera1.log")
  rec2=(--stats "$out/camera1.json" "$out/camera2.json" --log "$out/camera1.log" "$out/camera2.log")
else
  console=/dev/null; rec1=(); rec2=()
fi
# utility QoS (macOS taskpolicy; elsewhere nice): the flight program and the vehicles keep the performance cores
if command -v taskpolicy >/dev/null 2>&1; then LOW=(taskpolicy -c utility); else LOW=(nice -n 10); fi
if [[ "$scenario" == single ]]; then
  "${LOW[@]}" "$VPY" "$SIM/world/camera_component.py" --gcs "127.0.0.1:$udp_port" --parent "$parent" \
    --sysid 1 --label Forward --rgb-port "$video_port" --thermal-port "$((video_port + 2))" --pose-port "$pose_port" \
    --seed 0 --rgb-workers 3 ${rec1[@]+"${rec1[@]}"} > "$console" 2>&1 &
  echo "Video: forward RGB on UDP $video_port, thermal on $((video_port + 2)) (the camera starts in a few seconds)."
else
  "${LOW[@]}" "$VPY" "$SIM/world/camera_component.py" --gcs "127.0.0.1:$udp_port" --parent "$parent" \
    --sysid 1 2 --label "V1 forward" "$label2" --rgb-port "$video_port" "$video_port" \
    --thermal-port "$((video_port + 2))" "$((video_port + 6))" --pose-port $pose_ports --seed 0 100 --rgb-gated on off \
    --rgb-workers 2 ${rec2[@]+"${rec2[@]}"} > "$console" 2>&1 &
  echo "Video: the active vehicle's forward RGB on UDP $video_port; thermal of vehicle 1 on $((video_port + 2)), of vehicle 2 on $((video_port + 6)) (the cameras start in a few seconds)."
fi
