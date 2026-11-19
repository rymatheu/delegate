#!/usr/bin/env bash
# Fly ArduLean through the gorge with no ground station: a scripted MAVLink ground station uploads the mission, arms,
# takes off and flies AUTO until the vehicle disarms. Ends by itself and prints PASS or FAIL.
#
#   ./fly_gorge.sh [single|abreast|staggered] [--record [DIR]] [other options of sim/fly_gorge.py or sim/fly_gorge_formation.py]
#
# By default nothing is kept: the run works in one temporary directory, removed on every exit. --record [DIR] (or
# --out DIR) keeps the record in DIR (default out/<scenario>): track.csv at 100 Hz, flight.json, summary.txt, the
# lock-step inputs.txt and outputs.txt; two vehicles: v1/, v2/ and formation.csv. The executable is
# .lake/build/bin/ardulean ($LEAN_VEHICLE_EXE overrides it).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
SIM="$(cd "$HERE/../sim" && pwd)"
cd "$HERE"
PY="${SIM_PYTHON:-$SIM/.venv/bin/python}"
EXE="${LEAN_VEHICLE_EXE:-.lake/build/bin/ardulean}"
[[ -x "$EXE" ]] || { echo "fly_gorge.sh: the ArduLean executable $EXE is missing; build it first (README.md, Build)." >&2; exit 1; }
[[ -x "$PY" ]] || { echo "fly_gorge.sh: $PY is missing; run ../sim/setup.sh first." >&2; exit 1; }
scenario=single
case "${1:-}" in single|abreast|staggered) scenario="$1"; shift ;; esac
record=""; args=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --record) if [[ $# -gt 1 && "$2" != --* ]]; then record="$2"; shift; else record="out/$scenario"; fi ;;
    --out) record="$2"; shift ;;
    *) args+=("$1") ;;
  esac
  shift
done
tmp="$(mktemp -d "${TMPDIR:-/tmp}/ardulean-gorge.XXXXXX")"
child=""
cleanup() { if [[ -n "$child" ]]; then kill -TERM "$child" 2>/dev/null; wait "$child" 2>/dev/null; sleep 0.5; fi; rm -rf "$tmp"; }
trap cleanup EXIT
trap 'exit 130' INT TERM
if [[ -n "$record" ]]; then mkdir -p "$record"; out="$record"; else out="$tmp/run"; mkdir -p "$out"; fi
if [[ "$scenario" == single ]]; then
  cmd=("$PY" -B sim/fly_gorge.py --out "$out")
else
  cmd=("$PY" -B sim/fly_gorge_formation.py --plan "$scenario" --out "$out")
fi
"${cmd[@]}" ${args[@]+"${args[@]}"} > "$out/console.txt" 2>&1 &
child=$!
set +e
wait "$child"; code=$?
set -e
child=""
"$PY" -B - "$scenario" "$out" "$code" "$record" <<'PYEOF'
import json, sys
from pathlib import Path
scenario, out, code, record = sys.argv[1], Path(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
ok, lines = code == 0, []
try:
    if scenario == "single":
        f = json.loads((out / "flight.json").read_text())
        m = f["metrics"]
        ok = ok and m.get("completed", False)
        lines.append(f"single: end '{f['end']}', mission completed {m.get('completed')}, clearance min "
                     f"{m.get('clearance_min_in_air_m', float('nan')):.2f} m, distance to route max "
                     f"{m.get('route_distance_in_air_max_m', float('nan')):.2f} m, {f['simulated_s']:.1f} s simulated in {f['wall_s']:.1f} s")
    else:
        f = json.loads((out / "formation.json").read_text())
        ok = ok and all(f["completed"])
        p = f["pair"]
        lines.append(f"{scenario}: end '{f['end']}', completed {f['completed']}, centre distance min airborne "
                     f"{p.get('dist_min_airborne_m', float('nan')):.2f} m, {f['simulated_s']:.1f} s simulated in {f['wall_s']:.1f} s")
except (OSError, KeyError, ValueError) as e:
    ok = False
    lines.append(f"{scenario}: no result ({e!r})")
    try:
        lines += (out / "console.txt").read_text().splitlines()[-15:]
    except OSError:
        pass
lines.append(f"record: {record}/ (track.csv)" if record else "record: none (--record [DIR] keeps one)")
lines.append("PASS" if ok else "FAIL")
print("\n".join(lines))
sys.exit(0 if ok else 1)
PYEOF
