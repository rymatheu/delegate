#!/usr/bin/env bash
# Phase 5a slice 2: the vehicle skeleton over the byte memory (README.md "Phase 5: the vehicle skeleton"): AP_Param,
# GCS_MAVLink and AP_Mission as ardupilot/gcs/GCS.json, plus the vehicle from AP_Vehicle::setup and AP_Vehicle::loop,
# translated by cpp2lean.py --param-memory (configuration ardupilot/vehicle/Vehicle.json, key `vehicle`) ->
# ardupilot/out/Vehicle/Vehicle_lib.lean (+ ParamMemory.lean, GCSMemory.lean, VehicleMemory.lean, CFloat.lean,
# Vehicle_lib.addresses.json, Vehicle_lib.survey.txt) and ardupilot/vehicle/bridge_calls.txt.
# Usage: ardupilot/vehicle/translate_vehicle.sh [OUTDIR]
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
OUT="${1:-$ROOT/ardupilot/out/Vehicle}"
cd "$ROOT"
python3 cpp2lean.py --param-memory ardupilot/vehicle/Vehicle.json -o "$OUT" --namespace Vehicle_lib
