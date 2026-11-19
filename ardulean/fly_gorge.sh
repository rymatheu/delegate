#!/usr/bin/env bash
# Fly ArduLean through the gorge with no ground station: a scripted MAVLink ground station uploads the mission, arms,
# takes off and flies AUTO until the vehicle disarms. Ends by itself, prints PASS or FAIL, writes the record under out/.
#
#   ./fly_gorge.sh [single|abreast|staggered] [--out DIR] [other options of sim/fly_gorge.py or sim/fly_gorge_formation.py]
#
# Record: out/gorge/<scenario>/ (track.csv at 100 Hz, flight.json, summary.txt, inputs.txt and outputs.txt of the
# lock-step vehicle; two vehicles: v1/, v2/ and formation.csv). The executable is .lake/build/bin/ardulean
# ($LEAN_VEHICLE_EXE overrides it).
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
out="out/gorge/$scenario"; args=()
while [[ $# -gt 0 ]]; do
  case "$1" in --out) out="$2"; shift ;; *) args+=("$1") ;; esac
  shift
done
mkdir -p "$out"
set +e
if [[ "$scenario" == single ]]; then
  "$PY" sim/fly_gorge.py --out "$out" ${args[@]+"${args[@]}"} > "$out/console.txt" 2>&1
else
  "$PY" sim/fly_gorge_formation.py --plan "$scenario" --out "$out" ${args[@]+"${args[@]}"} > "$out/console.txt" 2>&1
fi
code=$?
set -e
"$PY" - "$scenario" "$out" "$code" <<'PYEOF'
import json, sys
from pathlib import Path
scenario, out, code = sys.argv[1], Path(sys.argv[2]), int(sys.argv[3])
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
    lines.append(f"{scenario}: no result ({e!r}); see {out}/console.txt")
lines.append(f"record: {out}/ (track.csv)")
lines.append("PASS" if ok else "FAIL")
print("\n".join(lines))
sys.exit(0 if ok else 1)
PYEOF
