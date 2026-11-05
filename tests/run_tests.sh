#!/usr/bin/env bash
# cpp2lean tests: golden output, rejections, determinism, warning-free Lean build, differential test.
# Usage: tests/run_tests.sh            (from anywhere; exit 0 iff every check passes)
#        tests/run_tests.sh --update   (rewrite the golden and expected files from the current output)
set -uo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
cd "$HERE"
TMP="$(mktemp -d "${TMPDIR:-/tmp}/cpp2lean-tests.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
fail=0
ok()   { echo "ok    $*"; }
bad()  { echo "FAIL  $*"; fail=1; }

# The namespace and translator options of an example: examples/<name>.json ("namespace",
# "cpp2lean"), else the default namespace and no options.
example_args() {
  python3 - "$1" <<'PY'
import json, os, sys
sys.path.insert(0, ".")
import cpp2lean
src = sys.argv[1]
cfg = os.path.splitext(src)[0] + ".json"
c = json.load(open(cfg)) if os.path.exists(cfg) else {}
print(" ".join(["--namespace", c.get("namespace") or cpp2lean.default_namespace(src)] + c.get("cpp2lean", [])))
PY
}

# 1. Golden output: each example translates to exactly the committed Lean.
for src in $(ls examples/*.cpp | grep -v '_driver\.cpp$'); do
  args=$(example_args "$src")
  ns=$(echo "$args" | awk '{print $2}')
  if ! python3 cpp2lean.py "$src" -o "$TMP/a" $args; then bad "translate $src"; continue; fi
  python3 cpp2lean.py "$src" -o "$TMP/b" $args
  if cmp -s "$TMP/a/$ns.lean" "$TMP/b/$ns.lean"; then ok "deterministic: $src"; else bad "two runs on $src differ"; fi
  if [ "${1:-}" = "--update" ]; then cp "$TMP/a/$ns.lean" "tests/golden/$ns.lean"; fi
  if diff -u "tests/golden/$ns.lean" "$TMP/a/$ns.lean"; then ok "golden: $src -> tests/golden/$ns.lean"
  else bad "golden: $src differs from tests/golden/$ns.lean (diff above)"; fi
  if grep -nE '\bsorry\b|^axiom|partial def' "$TMP/a/$ns.lean"; then bad "sorry/axiom/partial in $ns.lean"; fi
done
if [ "${1:-}" = "--update" ]; then cp "$TMP/a/CppLibm.lean" tests/golden/CppLibm.lean; fi
if diff -u tests/golden/CppLibm.lean "$TMP/a/CppLibm.lean"; then ok "golden: CppLibm.lean"; else bad "golden: CppLibm.lean"; fi

# 2. Rejections: exit status 2, the expected messages, and exactly the lines marked expect-reject.
for src in tests/reject_*.cpp; do
  exp="${src%.cpp}.expected"
  opts=$(sed -n '1s|^// cpp2lean-options: ||p' "$src")
  python3 cpp2lean.py "$src" -o "$TMP/r" $opts > "$TMP/r.out" 2>&1
  st=$?
  if [ $st -eq 2 ]; then ok "exit status 2: $src"; else bad "exit status $st (want 2): $src"; fi
  if [ "${1:-}" = "--update" ]; then cp "$TMP/r.out" "$exp"; fi
  if diff -u "$exp" "$TMP/r.out"; then ok "messages: $src = $exp"; else bad "messages: $src (diff above)"; fi
  want=$(grep -n '// expect-reject$' "$src" | cut -d: -f1 | sort -n | tr '\n' ' ')
  got=$(sed -E 's/^[^:]+:([0-9]+):.*/\1/' "$TMP/r.out" | sort -n | tr '\n' ' ')
  if [ "$want" = "$got" ]; then ok "rejected lines $got= marked lines: $src"; else bad "rejected lines [$got] != marked lines [$want]: $src"; fi
done

# 3. ArduPilot (if the tree is there): the AC_PID family, AP_Math, AP_Motors, AC_AttitudeControl(_Multi),
#    AC_PosControl, AC_WPNav and the AHRS view derivation translate to exactly the committed Lean (the
#    scripts other than AC_PID's first check their unity files with ardupilot/check_unity.py), and the
#    library code the last four carry is the code of the AP_Math, AC_PID and AC_PosControl translations
#    (ardupilot/check_shared.py; each translation's own boundary calls, `Output`, are not library code).
AP="${AP:-$PWD/ardupilot/src}"
if [ -d "$AP/libraries/AC_PID" ]; then
  for t in AC_PID:ac_pid:AC_PID_lib AP_Math:ap_math:AP_Math_lib AP_Motors:ap_motors:AP_Motors_lib \
           AC_Attitude:ac_attitude:AC_Attitude_lib AC_PosControl:ac_poscontrol:AC_PosControl_lib \
           AC_WPNav:ac_wpnav:AC_WPNav_lib AHRS_View:ahrs_view:AHRS_View_lib; do
    d="${t%%:*}"; rest="${t#*:}"; script="${rest%%:*}"; ns="${rest#*:}"
    if "ardupilot/translate_$script.sh" > "$TMP/ap.out" 2>&1; then
      if [ "${1:-}" = "--update" ]; then mkdir -p tests/golden/ardupilot; cp "ardupilot/out/$d/$ns.lean" "tests/golden/ardupilot/$ns.lean"; fi
      if diff -u "tests/golden/ardupilot/$ns.lean" "ardupilot/out/$d/$ns.lean"; then ok "golden: ArduPilot $d -> tests/golden/ardupilot/$ns.lean"
      else bad "golden: ArduPilot $d (diff above)"; fi
      if grep -nE '\bsorry\b|^axiom|partial def' "ardupilot/out/$d/$ns.lean"; then bad "sorry/axiom/partial in $ns.lean"; fi
    else cat "$TMP/ap.out"; bad "ardupilot/translate_$script.sh"; fi
  done
  for xy in AC_Attitude/AC_Attitude_lib:AP_Math/AP_Math_lib AC_Attitude/AC_Attitude_lib:AC_PID/AC_PID_lib \
            AC_PosControl/AC_PosControl_lib:AP_Math/AP_Math_lib AC_PosControl/AC_PosControl_lib:AC_PID/AC_PID_lib \
            AC_WPNav/AC_WPNav_lib:AP_Math/AP_Math_lib AC_WPNav/AC_WPNav_lib:AC_PosControl/AC_PosControl_lib \
            AHRS_View/AHRS_View_lib:AP_Math/AP_Math_lib; do
    x="${xy%%:*}"; y="${xy#*:}"
    if python3 ardupilot/check_shared.py "ardupilot/out/$x.lean" "ardupilot/out/$y.lean" --rename Vector2_double=Vector2p --skip Output,Outputs > "$TMP/sh.out"; then
      ok "shared library code: $(tail -1 "$TMP/sh.out")"
    else cat "$TMP/sh.out"; bad "shared library code: $x vs $y"; fi
  done
  AP_TARGETS="ardupilot/AC_PID ardupilot/AP_Math ardupilot/AP_Motors ardupilot/AC_Attitude ardupilot/AC_PosControl ardupilot/AC_WPNav ardupilot/AHRS_View"
else
  echo "skip  ArduPilot tree not found at $AP"
  AP_TARGETS=""
fi

# 4. The Lean package builds from clean with no warnings, and the differential test passes.
rm -rf lean/.lake
python3 difftest.py $(ls examples/*.cpp | grep -v '_driver\.cpp$' | sed 's|examples/||; s|\.cpp$||') $AP_TARGETS > "$TMP/difftest.out" 2>&1
st=$?
cat "$TMP/difftest.out"
if [ $st -eq 0 ]; then ok "difftest: 0 differing lines"; else bad "difftest (exit $st)"; fi
if grep -q "warning" "$TMP/difftest.out"; then bad "warnings in the Lean build"; else ok "Lean build without warnings"; fi

# 5. The per-tick composition of the AP_Motors, AC_Attitude and AC_PosControl translations against the
#    oracle's recorded flight (if the oracle's output is there): 500 ticks, every value bit for bit.
if [ -n "$AP_TARGETS" ] && [ -f ardupilot/data/oracle-nosincos.txt ] && [ -f ardupilot/data/inputs.txt ]; then
  if ardupilot/compose/compose.sh 500 > "$TMP/compose.out" 2>&1; then
    grep -E "^composition" "$TMP/compose.out" | sed 's/^/      /'
    ok "composition: 500 ticks equal to the oracle"
  else cat "$TMP/compose.out"; bad "composition (ardupilot/compose/compose.sh)"; fi
  if grep -q "warning" "$TMP/compose.out"; then bad "warnings in the composition build"; fi
else
  echo "skip  composition (no recorded flight at ardupilot/data)"
fi

# 6. The two vehicles (sim/PROTOCOL.md): build copter_ref (ArduPilot's classes compiled unmodified) and
#    copter_lean (the translations), then replay the recorded flight through both: every value of every
#    tick bit-identical, the same parameters (ardupilot/vehicle/replay.sh). Flights are not part of the
#    suite (sim/README.md, sim/fly.sh).
if [ -n "$AP_TARGETS" ] && [ -f ardupilot/data/inputs.txt ]; then
  if ardupilot/vehicle/build.sh > "$TMP/vehicle.out" 2>&1; then
    ok "vehicles built: build/vehicle/copter_ref, lean/.lake/build/bin/copter_lean"
    if grep -q "warning" "$TMP/vehicle.out"; then grep "warning" "$TMP/vehicle.out" | head; bad "warnings in the vehicle build"; fi
    if ardupilot/vehicle/replay.sh > "$TMP/replay.out" 2>&1; then
      sed 's/^/      /' "$TMP/replay.out"
      ok "replay: copter_lean and copter_ref bit-identical on the recorded flight"
    else cat "$TMP/replay.out"; bad "replay (ardupilot/vehicle/replay.sh)"; fi
  else cat "$TMP/vehicle.out"; bad "vehicle build (ardupilot/vehicle/build.sh)"; fi
else
  echo "skip  vehicles (no ArduPilot tree or recorded flight)"
fi

if [ $fail -eq 0 ]; then echo "all tests passed"; else echo "some tests FAILED"; fi
exit $fail
