#!/usr/bin/env bash
# Fly the whole PX4 stack (px4_full: real EKF2, commander, navigator, MAVLink; simulator sensor
# noise) from QGroundControl.
#
#   px4/harnesses/px4_full/dev/fly_qgc.sh [PORT]     (from anywhere; PORT 14550 by default)
#
# Builds nothing: the executables must be built already. It starts px4_full behind
# `harness serve` (monitors on every clause, verdicts in build/serve/px4_full.log), steps it in
# real time (one 400 Hz tick per 2.5 ms; when the stack cannot keep up, the ticks behind are
# printed every simulated second) and sends the vehicle's MAVLink stream from the first tick to
# UDP 127.0.0.1:PORT, where QGroundControl's default UDP link listens, as PX4 SITL does; the
# ground station's replies come back to the same socket. It binds no fixed port (the vehicle's
# side is an ephemeral local port). Stop with Ctrl-C or SIGTERM: the socket is closed and the
# served harness stopped.
set -euo pipefail
PORT="${1:-14550}"
case "$PORT" in ''|*[!0-9]*) echo "usage: px4/harnesses/px4_full/dev/fly_qgc.sh [PORT]" >&2; exit 2 ;; esac
HARNESS="$(cd "$(dirname "$0")/../../../.." && pwd)"
missing=0
for f in .lake/build/bin/harness build/modules/plant_sim/plant_sim build/modules/px4_sim_in/px4_sim_in \
         build/modules/px4_sensors/px4_sensors build/modules/px4_rate/px4_rate \
         build/modules/px4_alloc/px4_alloc build/modules/px4_ekf2/px4_ekf2 build/modules/px4_att/px4_att \
         build/modules/px4_mavlink/px4_mavlink build/modules/px4_navigator/px4_navigator \
         build/modules/px4_fmm/px4_fmm build/modules/px4_pos/px4_pos build/modules/px4_land/px4_land \
         build/modules/px4_commander/px4_commander build/modules/px4_merge_ack/px4_merge_ack \
         build/modules/px4_sim_out/px4_sim_out; do
  if [ ! -e "$HARNESS/$f" ]; then
    echo "fly_qgc.sh: $f is missing" >&2
    missing=1
  fi
done
if [ "$missing" = 1 ]; then
  echo "fly_qgc.sh: build first (px4/build.sh, px4/plain_build.sh, lake build); nothing was started" >&2
  exit 1
fi
cat <<MSG
PX4 harness stack: px4_full (PX4 v1.17.0 sensors, EKF2, controllers, flight mode manager, land
detector, commander, navigator, MAVLink; simulator sensor noise on), sending MAVLink to
UDP 127.0.0.1:$PORT.
What to do:
  1. Have QGroundControl running (its default UDP link listens on 14550; for a link on another
     port, give that port as the argument).
  2. The vehicle appears by itself at the first heartbeat. EKF2 has a GPS origin about 10.5 s of
     vehicle time after the start (QGroundControl then shows it in the gorge).
  3. Plan view: a takeoff, waypoints (stay inside the gorge: 10 m east at 2 m is a wall, the floor
     rises to the north beyond about 15 m), a landing; upload; then arm and start the mission. Or
     Fly view: Takeoff, then click a point to go there, then Land. No RC is simulated. PX4 lands,
     detects the landing and disarms by itself.
  4. The stack may run slower than real time: the vehicle's clock then runs slow, and the
     relay prints how far behind it is. Ctrl-C here (or SIGTERM) stops the vehicle and closes the link.
Verdicts of the monitors: build/serve/px4_full.log.
MSG
cd "$HARNESS"
exec python3 -I px4/harnesses/px4_full/dev/relay.py --gcs "127.0.0.1:$PORT"
