#!/usr/bin/env bash
# The split of the two generated files into modules (tools/split_modules.py), as it was run.
#
#   ARDUPILOT=/path/to/ardupilot tools/split.sh                 re-split from the current modules
#   ARDUPILOT=... tools/split.sh SRC_DIR DEPS_DIR               split SRC_DIR/{Vehicle_lib,Estimator_lib}.lean with the
#                                                               dependencies DEPS_DIR/<file>.deps.tsv (tools/dump_deps.lean)
#
# Without arguments each file is first rebuilt from its modules (tools/check_split.py --write) and split again with the
# item graph its INDEX.json records, so no .olean of the monolithic files is needed; the result must be the same tree
# (git diff empty). The estimator is split first: the vehicle's modules import the estimator modules they use.
set -euo pipefail
cd "$(dirname "$0")/.."
: "${ARDUPILOT:?set ARDUPILOT to an ArduPilot checkout (for locating the cited source files)}"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
if (($# == 2)); then
  src="$1"; est_deps=(--deps "$2/Estimator_lib.deps.tsv"); veh_deps=(--deps "$2/Vehicle_lib.deps.tsv")
else
  src="$tmp"
  python3 tools/check_split.py ArduLean/Estimator/INDEX.json --write "$tmp/Estimator_lib.lean"
  python3 tools/check_split.py ArduLean/Vehicle/INDEX.json --write "$tmp/Vehicle_lib.lean"
  cp ArduLean/Estimator/INDEX.json "$tmp/Estimator.INDEX.json"; cp ArduLean/Vehicle/INDEX.json "$tmp/Vehicle.INDEX.json"
  est_deps=(--deps-index "$tmp/Estimator.INDEX.json"); veh_deps=(--deps-index "$tmp/Vehicle.INDEX.json")
fi

python3 tools/split_modules.py "$src/Estimator_lib.lean" --namespace Estimator_lib --ardupilot "$ARDUPILOT" --root . \
  --out-dir ArduLean/Estimator --module-prefix ArduLean.Estimator "${est_deps[@]}" \
  --source-name lean/Estimator_lib.lean --title "the estimator translation" \
  --import-map CFloat=ArduLean.Runtime.CFloat --import-map Musl.=ArduLean.Musl. --always-import ArduLean.Runtime.CFloat \
  --generated "^(WPtr|WFun|CText|Output|Outputs|World)\b=World" --generated "^EKF_STATUS_FLAGS=mavlink" \
  --generated "^(EstScheduler|EstUART|EstRecord|est_|EST_|millis|micros|gps_time_week_ms)=World"

python3 tools/split_modules.py "$src/Vehicle_lib.lean" --namespace Vehicle_lib --ardupilot "$ARDUPILOT" --root . \
  --out-dir ArduLean/Vehicle --module-prefix ArduLean.Vehicle "${veh_deps[@]}" \
  --source-name lean/Vehicle_lib.lean --title "the vehicle translation" \
  --import-map CFloat=ArduLean.Runtime.CFloat --import-map ParamMemoryV=ArduLean.Runtime.Memory \
  --import-map GCSMemoryV=ArduLean.Runtime.GcsPort --import-map VehicleMemoryV=ArduLean.Runtime.Boundary \
  --import-map VehicleHal=ArduLean.Runtime.Hal --import-map VehicleBridgeMap=ArduLean.Runtime.BridgeMap \
  --import-map VehicleBridge=ArduLean.Runtime.Bridge --import-map Musl.=ArduLean.Musl. \
  --always-import ArduLean.Runtime.CFloat --foreign-index Estimator_lib=ArduLean/Estimator/INDEX.json \
  --generated "^(addr'|heapBase$|stackBase$|memSize$|image$|initMem$)=Layout" \
  --generated "^(staticConstruct|staticDynamicInit)$=Startup" --generated "^worldOutputs'=World" \
  --generated "^fnptr'=Dispatch" --generated "^vcall'=Dispatch" \
  --top-pass 3 \
  --anchor "Arming=AP_Arming.arm" \
  --anchor-doc "Arming=pre-arm checks and arming (AP_Arming with AP_Arming_Copter's overrides), with the GCS sends and motor output they reach" \
  --anchor "ModeSwitching=Copter.set_mode" \
  --anchor-doc "ModeSwitching=mode changes: Copter::set_mode and the recursive component around it (mode entry, mission command start, failsafe events, RC auxiliary functions), the mission's callbacks, the battery failsafe" \
  --anchor "GcsMessages=GCS_MAVLINK.handle_message" \
  --anchor-doc "GcsMessages=GCS message handling: GCS_MAVLINK::handle_message with GCS_MAVLINK_Copter's overrides, COMMAND_LONG and COMMAND_INT, update_receive; and the vehicle's setup (Copter::init_ardupilot, AP_Vehicle::setup)" \
  --anchor "SchedulerLoop=fnptr'0'at'AP_Scheduler_Task'function" \
  --anchor-doc "SchedulerLoop=the scheduler loop: the task table's functors and their dispatcher, AP_Scheduler::run and loop, AP_Vehicle::loop"
