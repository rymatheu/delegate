#!/usr/bin/env bash
# Build the module executables of one stack, or of all: tools/build_modules.sh [ardupilot|px4|sim|all]
#
# Needs `lake build` first (each build asks the `harness` CLI for the module's records) and the sources in deps/
# (tools/fetch_deps.sh); the simulator modules need the repository's sim/ set up (sim/setup.sh). Every executable
# goes to build/modules/NAME/NAME with its code hash (build/modules/NAME/code_inputs.txt). About 2.5 min for
# ArduPilot, 4 min for PX4, under a minute for the simulator (measured in a fresh clone).
set -euo pipefail
HARNESS="$(cd "$(dirname "$0")/.." && pwd)"
cd "$HARNESS"
which="${1:-all}"

# Everything the build needs is checked before anything is built; each missing item is named with how to get it.
MISSING=0
miss() { echo "  MISSING  $1" >&2; echo "           fix: $2" >&2; MISSING=1; }
need_cmd() { command -v "$1" > /dev/null 2>&1 || miss "$1 ($2)" "$3"; }
prereqs() {
  need_cmd clang++ "the C++ compiler" "xcode-select --install"
  need_cmd git "fetches PX4's MAVLink sources" "xcode-select --install"
  [ -x .lake/build/bin/harness ] || miss ".lake/build/bin/harness (the harness command)" \
    "LEAN_NUM_THREADS=1 lake build   (in harness/; needs elan, https://github.com/leanprover/elan)"
  [ -x ../sim/.venv/bin/python ] && [ -f ../sim/build/world-cache/gorge_s7.pkl ] || \
    miss "the simulator's Python environment and gorge world (sim/.venv, sim/build/world-cache)" "../sim/setup.sh"
  case "$which" in ardupilot|all)
    [ -d deps/ardupilot/libraries ] && [ -d deps/mavlink/pymavlink ] || \
      miss "the ArduPilot and MAVLink sources (deps/ardupilot, deps/mavlink)" "tools/fetch_deps.sh" ;;
  esac
  case "$which" in px4|all)
    [ -d deps/px4/src ] || miss "the PX4 sources (deps/px4)" "tools/fetch_deps.sh"
    need_cmd uv "makes the PX4 tools' Python environment" "brew install uv   (or https://github.com/astral-sh/uv)"
    need_cmd xz "compresses PX4's parameter and event metadata for px4_mavlink" "brew install xz" ;;
  esac
  if [ "$MISSING" = 1 ]; then
    echo "build_modules.sh: NOTHING WAS BUILT: something the build needs is missing (above). Fix it and run this again." >&2
    exit 1
  fi
}
# A build that stops says so in its last lines, with the step it stopped in.
STEP=""
on_exit() {
  rc=$?
  if [ "$rc" != 0 ] && [ -n "$STEP" ]; then
    echo "" >&2
    echo "build_modules.sh: FAILED in step: $STEP (exit $rc). Its error is in the lines above." >&2
    echo "build_modules.sh: the steps after it were NOT built, so the launchers will report missing files." >&2
  fi
}
trap on_exit EXIT
run() { STEP="$*"; "$@"; }
sim() {
  run sim/modules/plant_sim/build.sh plant_sim
  run sim/modules/plant_sim/build.sh plant_formation
}
ardupilot() {
  run ardupilot/gen_mavlink.sh
  for m in rate_pid mixer position attitude guidance loiter script est_scenario; do run ardupilot/build.sh "$m"; done
  run ardupilot/modules/estimator/build.sh
  run ardupilot/modules/supervisor/build.sh
  run ardupilot/modules/truth_est/build.sh
  run ardupilot/modules/supervisor/dev/gen_pymavlink.sh
  # the module `top`: the compiled top-level harness (ardupilot/Top.lean, built by lake build) behind its launcher
  mkdir -p build/top
  printf '%s\n' '#!/bin/sh' \
    '# launcher: the compiled top-level harness (Top.lean) in serve mode, as a module executable' \
    'exec "$(cd "$(dirname "$0")/../.." && pwd)/.lake/build/bin/top" serve "$@"' > build/top/top_serve
  chmod +x build/top/top_serve
}
px4() {
  run px4/gen.sh
  run px4/fetch_mavlink.sh
  for m in px4_rate px4_alloc px4_sensors px4_ekf2 px4_att px4_pos px4_fmm px4_land px4_commander \
           px4_navigator px4_mavlink px4_merge_ack px4_sim_in px4_sim_out px4_drive_att px4_drive_pos \
           px4_drive_auto px4_drive_cmd px4_drive_nav px4_cmd_window; do run px4/build.sh "$m"; done
}
case "$which" in
  sim|ardupilot|px4|all) ;;
  *) echo "usage: tools/build_modules.sh [ardupilot|px4|sim|all]" >&2; exit 2 ;;
esac
prereqs
case "$which" in
  sim) sim ;;
  ardupilot) ardupilot ;;
  px4) px4 ;;
  all) sim; ardupilot; px4 ;;
esac
STEP=""
echo "build_modules.sh: OK, $which built (every step finished)"
