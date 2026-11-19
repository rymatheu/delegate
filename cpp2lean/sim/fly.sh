#!/usr/bin/env bash
# Fly the three missions with both vehicles (fresh runs, the same initial conditions) and compare
# them tick by tick: sim/out/{lean,ref}-{hover,course-1ms,figure8}/, sim/out/compare-<mission>.csv,
# sim/RESULTS.md (sim/compare_flights.py). The vehicles must be built (ardupilot/vehicle/build.sh).
# Usage: sim/fly.sh [MISSION...]   (default: hover course-1ms figure8)
# Every mission flies with the tuned gains of params/copter-cf2x-tuned.txt on top of the base file;
# UNTUNED=1 flies ArduPilot's default gains instead.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
PY="$HERE/.venv/bin/python"
LEAN="$ROOT/lean/.lake/build/bin/copter_lean"
REF="$ROOT/build/vehicle/copter_ref"
P="$HERE/params"
TUNED=(--params "$P/copter-cf2x-tuned.txt"); [ "${UNTUNED:-0}" = 1 ] && TUNED=()
for m in ${*:-hover course-1ms figure8}; do
  case "$m" in
    hover) args=(--params "$P/copter-cf2x.txt" --params "$P/copter-hover.txt" ${TUNED[@]+"${TUNED[@]}"} --duration 10 --hold 99) ;;
    course-1ms) args=(--params "$P/copter-cf2x.txt" --params "$P/copter-course-speed.txt" ${TUNED[@]+"${TUNED[@]}"} --duration 60) ;;
    figure8) args=(--params "$P/copter-cf2x.txt" ${TUNED[@]+"${TUNED[@]}"} --duration 30) ;;
    *) echo "unknown mission $m" >&2; exit 2 ;;
  esac
  for v in lean ref; do
    bin="$LEAN"; [ "$v" = ref ] && bin="$REF"
    rm -rf "$HERE/out/$v-$m"
    "$PY" "$HERE/run_copter.py" --backend bin --bin "$bin" "${args[@]}" --out "$HERE/out/$v-$m" > "$HERE/out/$v-$m.log" 2>&1 || true
    tail -n +2 "$HERE/out/$v-$m.log" | head -3
  done
done
"$PY" "$HERE/compare_flights.py" ${*:-hover course-1ms figure8}
