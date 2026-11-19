#!/usr/bin/env bash
# The gorge flight with no QGroundControl: a scripted ground station starts the onboard mission from the ground
# (GUIDED, arm, MISSION_START) and watches it to the disarm after landing; then the flight is checked. Ends by itself,
# prints PASS/FAIL per check and `RESULT PASS` or `RESULT FAIL`, exit status 0 on PASS.
#
#   ./fly_gorge.sh [single|abreast|staggered] [--port N] [--speed S] [--seed N] [--noise field|none] [--record [DIR]] ...
#
#   --port N    the scripted ground station's MAVLink UDP port (default 14591 single, 14593 two vehicles)
#   --speed S   0 (default): as fast as the simulation runs; 1: real time
#   --record [DIR]  keep the records (flight.csv or formation.csv, v1.csv, v2.csv, report.txt, ...) in DIR, default
#               out/gorge-SCENARIO (--out DIR is the same). Without it nothing is left on disk: the flight's records live
#               in a temporary directory that is removed at exit.
# Further options: sim/flights/gorge_flight.py (single) and sim/flights/formation_flight.py (two vehicles).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(dirname "$HERE")"
PY="${SIM_PYTHON:-$REPO/sim/.venv/bin/python}"
export PYTHONDONTWRITEBYTECODE=1
cd "$HERE"
scenario=single
case "${1:-}" in single|abreast|staggered) scenario="$1"; shift ;; esac
[[ -x "$PY" ]] || { echo "no simulator environment at $PY: run sim/setup.sh at the repository root" >&2; exit 1; }
LEAN_NUM_THREADS=1 lake build leanfc >/dev/null || { echo "lake build failed" >&2; exit 1; }
if [[ "$scenario" == single ]]; then
  exec "$PY" -B sim/flights/gorge_flight.py "$@"
else
  exec "$PY" -B sim/flights/formation_flight.py --plan "$scenario" "$@"
fi
