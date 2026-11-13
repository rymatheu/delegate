#!/usr/bin/env bash
# Phase 4: GCS_MAVLink over the byte memory of AP_Param (README.md "Phase 4: GCS_MAVLink"): GCS, GCS_MAVLINK (receive
# path, routing, handle_message and the common handlers the recorded sessions reach, the parameter protocol, the
# mission protocol with MissionItemProtocol(_Waypoints) over AP_Mission, update_send with the deferred messages and
# buckets), the generated MAVLink C library as GCS_MAVLink.cpp compiles it, AP_Param, AP_Mission, StorageManager,
# ByteBuffer/ObjectBuffer, translated by cpp2lean.py --param-memory from the reference build's units (configuration
# ardupilot/gcs/GCS.json) -> ardupilot/out/GCS/GCS_lib.lean (+ ParamMemory.lean, GCSMemory.lean, CFloat.lean,
# GCS_lib.addresses.json).
# Usage: ardupilot/gcs/translate_gcs.sh [OUTDIR]
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
OUT="${1:-$ROOT/ardupilot/out/GCS}"
cd "$ROOT"
python3 cpp2lean.py --param-memory ardupilot/gcs/GCS.json -o "$OUT" --namespace GCS_lib
