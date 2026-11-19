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
sim() {
  sim/modules/plant_sim/build.sh plant_sim
  sim/modules/plant_sim/build.sh plant_formation
}
ardupilot() {
  ardupilot/gen_mavlink.sh
  for m in rate_pid mixer position attitude guidance loiter script est_scenario; do ardupilot/build.sh "$m"; done
  ardupilot/modules/estimator/build.sh
  ardupilot/modules/supervisor/build.sh
  ardupilot/modules/truth_est/build.sh
  ardupilot/modules/supervisor/dev/gen_pymavlink.sh
  # the module `top`: the compiled top-level harness (ardupilot/Top.lean, built by lake build) behind its launcher
  mkdir -p build/top
  printf '%s\n' '#!/bin/sh' \
    '# launcher: the compiled top-level harness (Top.lean) in serve mode, as a module executable' \
    'exec "$(cd "$(dirname "$0")/../.." && pwd)/.lake/build/bin/top" serve "$@"' > build/top/top_serve
  chmod +x build/top/top_serve
}
px4() {
  px4/gen.sh
  px4/fetch_mavlink.sh
  for m in px4_rate px4_alloc px4_sensors px4_ekf2 px4_att px4_pos px4_fmm px4_land px4_commander \
           px4_navigator px4_mavlink px4_merge_ack px4_sim_in px4_sim_out px4_drive_att px4_drive_pos \
           px4_drive_auto px4_drive_cmd px4_drive_nav px4_cmd_window; do px4/build.sh "$m"; done
}
case "$which" in
  sim) sim ;;
  ardupilot) ardupilot ;;
  px4) px4 ;;
  all) sim; ardupilot; px4 ;;
  *) echo "usage: tools/build_modules.sh [ardupilot|px4|sim|all]" >&2; exit 2 ;;
esac
echo "build_modules.sh: $which built"
