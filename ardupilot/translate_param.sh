#!/usr/bin/env bash
# Translate ArduPilot's AP_Param over one byte memory (README.md, "Phase 4: AP_Param"): cpp2lean.py --param-memory with
# ardupilot/param/AP_Param.json (the units and AST filters of AP_Param.cpp, AP_ParamT.cpp, StorageManager.cpp,
# AP_HAL/Storage.cpp, AP_Math.cpp and AC_CommandModel.cpp in the reference build, the root table Copter::var_info, the
# entry functions, the HAL boundary), then the harness data (ardupilot/param/gen_param_harness.py: the constructors'
# setup_object_defaults calls, the estimator World's parameter addresses) from the reference's estimation trace.
# Output: ardupilot/out/AP_Param/ (AP_Param_lib.lean, ParamMemory.lean, CFloat.lean, AP_Param_lib.addresses.json,
# estimator_params.json) and lean/ParamHarnessData.lean. Usage: ardupilot/translate_param.sh [OUT_DIR]
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
OUT="${1:-$ROOT/ardupilot/out/AP_Param}"
cd "$ROOT"
python3 cpp2lean.py --param-memory ardupilot/param/AP_Param.json -o "$OUT" --namespace AP_Param_lib
if [ "${PARAM_HARNESS:-1}" = 1 ]; then
  python3 ardupilot/param/gen_param_harness.py sim/out/lockstep-flight/est.txt
fi
