#!/usr/bin/env bash
# Generate, once, what PX4's own build generates and every PX4 module reads, with PX4's own tools
# (never modifying $PX4_ROOT): px4/gen.sh
#
#   build/px4venv/                      the Python packages PX4's generators need (pinned below)
#   build/gen/px4/uORB/topics/*.h       the uORB message headers (Tools/msg/px_generate_uorb_topic_files.py
#                                       --headers over msg/*.msg msg/versioned/*.msg, as msg/CMakeLists.txt)
#   build/gen/px4/topics_src/*.cpp      the uORB metadata sources (the same tool, --sources)
#   build/gen/px4/px4_boardconfig.h     the Kconfig header of the px4_sitl default board
#                                       (python -m defconfig boards/px4/sitl/default.px4board; genconfig),
#                                       as cmake/kconfig.cmake does
#   build/gen/px4/events/events_generated.h   the events header (src/lib/events/CMakeLists.txt)
#   build/gen/px4/source.txt            the PX4 tag and commit these were made from
set -euo pipefail
HARNESS="$(cd "$(dirname "$0")/.." && pwd)"
PX4_ROOT="${PX4_ROOT:-$HARNESS/deps/px4}"
PX4_ROOT="$(cd "$PX4_ROOT" && pwd -P)"
VENV="$HARNESS/build/px4venv"
OUT="$HARNESS/build/gen/px4"

# The environment is made with uv from the same Python 3.12 as the simulator's (sim/setup.sh), never from whatever
# `python3` is first on PATH (an environment made from the macOS system Python can fail to start with
# "Library not loaded: @executable_path/../Python3"). One that does not start or lacks a package is made again.
if ! "$VENV/bin/python" -I -c 'import em, genmsg, yaml, jinja2, kconfiglib' > /dev/null 2>&1; then
  command -v uv > /dev/null 2>&1 || { echo "px4/gen.sh: uv is missing (https://github.com/astral-sh/uv)" >&2; exit 1; }
  rm -rf "$VENV"
  uv venv -q --python 3.12 "$VENV"
  uv pip install -q --python "$VENV/bin/python" "empy==3.3.4" "pyros-genmsg==0.5.8" "pyyaml" "jinja2" "kconfiglib==14.1.0"
fi
PY="$VENV/bin/python"

rm -rf "$OUT"
mkdir -p "$OUT/uORB/topics" "$OUT/topics_src" "$OUT/kconfig"
cd "$PX4_ROOT"
MSGS=(msg/*.msg msg/versioned/*.msg)
"$PY" Tools/msg/px_generate_uorb_topic_files.py --headers -f "${MSGS[@]}" -i msg msg/versioned \
  -o "$OUT/uORB/topics" -e Tools/msg/templates/uorb
"$PY" Tools/msg/px_generate_uorb_topic_files.py --sources -f "${MSGS[@]}" -i msg msg/versioned \
  -o "$OUT/topics_src" -e Tools/msg/templates/uorb
# one translation unit with every topic's metadata (uORBTopics.cpp lists them all)
{
  echo "// written by px4/gen.sh: every generated uORB metadata source, as one unit"
  for f in "$OUT"/topics_src/*.cpp; do echo "#include \"$(basename "$f")\""; done
} > "$OUT/topics_src/all_topics.cpp.in"
mv "$OUT/topics_src/all_topics.cpp.in" "$OUT/topics_all.cpp"
sed -i '' "s#include \"#include \"topics_src/#" "$OUT/topics_all.cpp"

# the events header (src/lib/events/CMakeLists.txt: common.json + enums.json, no source scan);
# needs the submodule src/lib/events/libevents
mkdir -p "$OUT/events"
(cd src/lib/events &&
  "$PY" libevents/scripts/combine.py enums.json libevents/events/common.json \
    --output "$OUT/events/common_with_enums.json" &&
  "$PY" libevents/scripts/generate.py --template libevents/libs/cpp/templates/events_generated.h.jinja \
    --output "$OUT/events" "$OUT/events/common_with_enums.json")

env PYTHON_EXECUTABLE="$PY" KCONFIG_CONFIG="$OUT/kconfig/boardconfig" PLATFORM=posix VENDOR=px4 \
  MODEL=sitl LABEL=default TOOLCHAIN= ARCHITECTURE= ROMFSROOT=px4fmu_common \
  BASE_DEFCONFIG="$OUT/kconfig/boardconfig" \
  sh -c "'$PY' -m defconfig boards/px4/sitl/default.px4board > /dev/null &&
         '$PY' -m genconfig --header-path '$OUT/px4_boardconfig.h' Kconfig"

{
  echo "PX4_ROOT=$PX4_ROOT"
  echo "tag: $(git -C "$PX4_ROOT" describe --tags --exact-match 2>/dev/null || echo none)"
  echo "commit: $(git -C "$PX4_ROOT" rev-parse HEAD)"
  echo "submodule src/lib/events/libevents: $(git -C "$PX4_ROOT/src/lib/events/libevents" rev-parse HEAD)"
  echo "python: $("$PY" --version)"
  uv pip freeze -q --python "$PY" | grep -i -E 'empy|genmsg|kconfiglib|yaml|jinja2'
} > "$OUT/source.txt"
echo "generated $OUT: $(ls "$OUT/uORB/topics" | wc -l | tr -d ' ') topic headers"
cat "$OUT/source.txt"
