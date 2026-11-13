#!/usr/bin/env bash
# Translate ArduPilot's StorageManager (StorageManager/StorageManager.cpp: the StorageAccess layout
# arithmetic, read_block/write_block over the areas of a storage type, read_byte/uint16/uint32/float
# and their writes, copy_area) to Lean with cpp2lean, from the unmodified sources, with the reference
# compiler flags and the stub headers (README.md, "Phase 2b"), as the library code that the test
# functions of ardupilot/unity_storage.cpp call. The HAL storage is the boundary (--hal-storage
# 16384, HAL_STORAGE_SIZE of the reference board): `hal.storage->read_block/write_block` act on a byte
# array threaded through the functions that reach it, as reference/hal/lockstep.cpp's Storage does.
# AP_SDCARD_STORAGE_ENABLED is 0 here, on both sides of the difftest: the reference build has 1
# (SITL), whose extra code is attach_file/flush_file (the microSD file through AP_Filesystem, on the
# heap) and a `file != nullptr` branch in read_block/write_block that is taken only after attach_file
# (BRD_SD_MISSION or BRD_SD_FENCE non-zero; both default 0): deferred (README.md, "Phase 2b").
# Output: ardupilot/out/StorageManager/. Usage: ardupilot/translate_storage.sh [extra cpp2lean options]
# Environment: AP (ArduPilot tree at commit 802db19de1; default ardupilot/src).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
AP="${AP:-$ROOT/ardupilot/src}"
L="$AP/libraries"
STUBS="$HERE/stubs"
OUT="$HERE/out/StorageManager"

CLANG_ARGS=(-std=gnu++11 -cl-single-precision-constant -fsigned-char -ftrapping-math
  -DCONFIG_HAL_BOARD=HAL_BOARD_SITL -DCONFIG_HAL_BOARD_SUBTYPE=HAL_BOARD_SUBTYPE_NONE
  -DAP_SCRIPTING_CHECKS=1 -DAP_BARO_PROBE_EXTERNAL_I2C_BUSES=1 -DHAL_NAVEKF2_AVAILABLE=1
  -DARDUPILOT_BUILD -DAPM_BUILD_DIRECTORY=APM_BUILD_ArduCopter '-DAP_BUILD_TARGET_NAME="ArduCopter"'
  -DFRAME_CONFIG=MULTICOPTER_FRAME -D__AP_LINE__=__LINE__ -DHAL_WITH_POSTYPE_DOUBLE=1
  -DHAL_WITH_EKF_DOUBLE=1 -DAP_FILTER_ENABLED=0 -DAP_TERRAIN_AVAILABLE=0 -DAP_CUSTOMROTATIONS_ENABLED=0
  -DAP_SDCARD_STORAGE_ENABLED=0
  -include ap_config.h -Wno-inconsistent-missing-override -Wno-gnu-designator -Wno-invalid-offsetof)
CA=()
for a in "${CLANG_ARGS[@]}"; do CA+=("--clang-arg=$a"); done
CHECK=(python3 "$HERE/check_unity.py" "$HERE/unity_storage.cpp" "$L/StorageManager/StorageManager.cpp" -- "${CLANG_ARGS[@]}" -I "$STUBS" -I "$L/AP_Common/missing" -I "$L")
"${CHECK[@]}" > /dev/null || { "${CHECK[@]}" | grep -v "the same"; exit 1; }

cd "$ROOT"
python3 cpp2lean.py "$HERE/unity_storage.cpp" -o "$OUT" --namespace StorageManager_lib --nest \
  --header "$L/StorageManager/StorageManager.h" --header "$L/StorageManager/StorageManager.cpp" \
  --lib-dir "$L/AP_Math" --boundary AP_HAL::HAL,AP_HAL::Storage --drop StorageManager::erase --drop StorageManager::last_io_failed --drop StorageManager::storage_failed \
  --pointer-params --runtime-loops --byte-objects --hal-storage 16384 --general-loops \
  --src-root "$L" -I "$STUBS" -I "$L/AP_Common/missing" -I "$L" "${CA[@]}" "$@"
