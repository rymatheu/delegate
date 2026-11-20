#!/usr/bin/env bash
# Generate ArduPilot's MAVLink C headers without waf: ardupilot/gen_mavlink.sh
#
# What waf does in ArduPilot's wscript (feature 'mavgen'): pymavlink's mavgen, language C, wire
# protocol 2.0, no validation, on modules/mavlink/message_definitions/v1.0/all.xml, into
# libraries/GCS_MAVLink/include/mavlink/v2.0/ under the build directory. Here the output goes to
# build/gen/mavlink/include/mavlink/v2.0/, which ardupilot/build.sh puts on the include path (so
# GCS_MAVLink.h's "include/mavlink/v2.0/all/version.h" resolves). The generated headers a module
# reads are in its code hash, like every other file the compiler reads. mavgen stamps today's date
# into each version.h (MAVLINK_BUILD_DATE); here it is the pinned commit's date instead, so the
# headers, and the code hashes of the modules that read them, do not change from day to day.
#
# $MAVLINK_ROOT is a checkout of ArduPilot's mavlink repository at the commit $ARDUPILOT_ROOT pins
# for its submodule modules/mavlink (checked below); default deps/mavlink in this project (a clone of ArduPilot/mavlink at that commit, with its pymavlink submodule).
# Nothing is written outside build/gen/mavlink.
set -euo pipefail

HARNESS="$(cd "$(dirname "$0")/.." && pwd)"
# the interpreter: the simulator's Python (sim/setup.sh), never whatever `python3` is first on PATH
PY="${HARNESS_PYTHON:-$HARNESS/../sim/.venv/bin/python}"
[ -x "$PY" ] || { echo "$(basename "$0"): no simulator environment at $PY: run sim/setup.sh at the repository root" >&2; exit 1; }
ARDUPILOT_ROOT="${ARDUPILOT_ROOT:-$HARNESS/deps/ardupilot}"
MAVLINK_ROOT="${MAVLINK_ROOT:-$HARNESS/deps/mavlink}"
OUT="$HARNESS/build/gen/mavlink"

[ -f "$MAVLINK_ROOT/message_definitions/v1.0/all.xml" ] && [ -d "$MAVLINK_ROOT/pymavlink/generator" ] || {
  echo "gen_mavlink.sh: no MAVLink definitions and pymavlink in $MAVLINK_ROOT; set MAVLINK_ROOT" >&2; exit 1; }
PINNED="$(git -C "$ARDUPILOT_ROOT" ls-tree HEAD modules/mavlink | awk '{print $3}')"
HAVE="$(git -C "$MAVLINK_ROOT" rev-parse HEAD)"
[ "$PINNED" = "$HAVE" ] || {
  echo "gen_mavlink.sh: $MAVLINK_ROOT is at $HAVE, ArduPilot pins $PINNED" >&2; exit 1; }

rm -rf "$OUT"
mkdir -p "$OUT/include/mavlink/v2.0"
DATE="$(TZ=UTC git -C "$MAVLINK_ROOT" log -1 --date=format-local:'%a %b %d %Y' --format=%cd HEAD)"
"$PY" -I -c '
import sys, time
sys.path.insert(0, sys.argv[1])
sys.dont_write_bytecode = True
strftime = time.strftime
time.strftime = lambda fmt, *t: sys.argv[4] if fmt == "%a %b %d %Y" else strftime(fmt, *t)
from pymavlink.generator import mavgen
class opts:
    language = "C"
    wire_protocol = "2.0"
    validate = False
    output = sys.argv[2]
sys.exit(0 if mavgen.mavgen(opts(), [sys.argv[3]]) else 1)
' "$MAVLINK_ROOT" "$OUT/include/mavlink/v2.0" "$MAVLINK_ROOT/message_definitions/v1.0/all.xml" "$DATE" > "$OUT/mavgen.log"
echo "$HAVE" > "$OUT/mavlink_commit.txt"
echo "wrote $OUT/include/mavlink/v2.0 (mavlink $HAVE)"
