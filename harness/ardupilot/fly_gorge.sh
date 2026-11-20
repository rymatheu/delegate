#!/usr/bin/env bash
# A gorge scenario on the ArduPilot harness stack with no ground station: scripted, ends by itself, prints a PASS/FAIL
# summary (monitor verdicts, wall clearance, separation, real-time factor).
#
#   ardupilot/fly_gorge.sh [single|abreast|staggered] [--seed N] [--no-noise] [--record [DIR] | --out DIR]
#
# Nothing is kept by default: the run writes only into a temporary directory (mktemp -d), removed on every exit.
# --record [DIR] (default ardupilot/out/SCENARIO; --out DIR is the same) keeps the record gorge-SCENARIO.csv, the
# summary .json, the ground stations' .log, the monitors' serve.log and the session's ledger record.
# The mission reaches each vehicle through the mission protocol: a scripted ground station per vehicle uploads its
# plan file of sim/plans (ardupilot/fly_gorge.py). Builds nothing (README.md, "Build").
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
# the interpreter: the simulator's Python (sim/setup.sh), never whatever `python3` is first on PATH
PY="${HARNESS_PYTHON:-$HERE/../../sim/.venv/bin/python}"
[ -x "$PY" ] || { echo "$(basename "$0"): no simulator environment at $PY: run sim/setup.sh at the repository root" >&2; exit 1; }
TMP="$(mktemp -d "${TMPDIR:-/tmp}/fly_gorge.XXXXXX")"
PID=""
cleanup() { [ -n "$PID" ] && kill -TERM "$PID" 2>/dev/null && wait "$PID" 2>/dev/null; rm -rf "$TMP"; }
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
cd "$HERE/.."
"$PY" -I -B "$HERE/fly_gorge.py" "$@" --tmp "$TMP" &
PID=$!
RC=0; wait "$PID" || RC=$?
PID=""
exit $RC
