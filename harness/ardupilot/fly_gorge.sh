#!/usr/bin/env bash
# A gorge scenario on the ArduPilot harness stack with no ground station: scripted, ends by itself, prints a PASS/FAIL
# summary and writes ardupilot/out/gorge-SCENARIO.csv (and .json, .log).
#
#   ardupilot/fly_gorge.sh [single|abreast|staggered] [--seed N] [--no-noise]
#
# The mission reaches each vehicle through the mission protocol: a scripted ground station per vehicle uploads its
# plan file of sim/plans (ardupilot/fly_gorge.py). Builds nothing (README.md, "Build").
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
cd "$HERE/.."
exec python3 -I "$HERE/fly_gorge.py" "$@"
