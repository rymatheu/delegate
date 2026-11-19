#!/usr/bin/env bash
# PX4's MAVLink sources, once: px4/fetch_mavlink.sh
#
# px4_mavlink compiles PX4's src/modules/mavlink against the C headers of PX4's pinned MAVLink
# (the submodule src/modules/mavlink/mavlink of PX4 v1.17.0, commit 33af200d). That submodule is
# not checked out in deps/px4 (read only), so this clones it here, into build/src/mavlink:
#   build/src/mavlink            mavlink/mavlink at 33af200d, with its pymavlink submodule at the
#                                commit that commit pins (px4/modules/px4_mavlink/generate.sh checks
#                                the commit and runs mavgen from it at every build)
#   build/gen/px4_mavlink/pymav/development.py
#                                the Python MAVLink 2 dialect (pymavlink's mavgen, development.xml,
#                                PX4's CONFIG_MAVLINK_DIALECT) that the hand-checked case of
#                                px4_mavlink and the ground-station scripts of px4_full use
# Then px4/build.sh px4_mavlink. Nothing is written outside build/; MAVLINK_URL overrides the source.
set -euo pipefail
HARNESS="$(cd "$(dirname "$0")/.." && pwd)"
COMMIT=33af200d25ec6f0925b49b1ba82bbf1294ea5f72
URL="${MAVLINK_URL:-https://github.com/mavlink/mavlink.git}"
SRC="$HARNESS/build/src/mavlink"
PY="$HARNESS/build/px4venv/bin/python"
[ -x "$PY" ] || { echo "fetch_mavlink.sh: run px4/gen.sh first (it makes build/px4venv)" >&2; exit 1; }
if [ ! -d "$SRC/.git" ]; then
  mkdir -p "$(dirname "$SRC")"
  git clone -q "$URL" "$SRC"
fi
git -C "$SRC" checkout -q "$COMMIT"
git -C "$SRC" submodule update -q --init pymavlink
[ "$(git -C "$SRC" rev-parse HEAD)" = "$COMMIT" ] || { echo "fetch_mavlink.sh: not at $COMMIT" >&2; exit 1; }
OUT="$HARNESS/build/gen/px4_mavlink/pymav"
mkdir -p "$OUT"
"$PY" "$SRC/pymavlink/tools/mavgen.py" --lang Python3 --wire-protocol 2.0 \
  --output "$OUT/development.py" "$SRC/message_definitions/v1.0/development.xml" > /dev/null
echo "mavlink $(git -C "$SRC" rev-parse HEAD), pymavlink $(git -C "$SRC/pymavlink" rev-parse HEAD)"
echo "wrote $OUT/development.py"
