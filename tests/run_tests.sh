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
if [ "${1:-}" = "--update" ]; then cp "$TMP/a/CFloat.lean" tests/golden/CFloat.lean; fi
if diff -u tests/golden/CFloat.lean "$TMP/a/CFloat.lean"; then ok "golden: CFloat.lean (= support/CFloat.lean)"; else bad "golden: CFloat.lean"; fi
if [ "${1:-}" = "--update" ]; then cp support/CString.lean tests/golden/CString.lean; fi
if diff -u tests/golden/CString.lean support/CString.lean; then ok "golden: CString.lean (= support/CString.lean)"; else bad "golden: CString.lean"; fi

# 1b. The C library: musl's sources translate to exactly the committed Lean (libm/translate_libm.sh,
#     which checks each unity file with ardupilot/check_unity.py), with no sorry/axiom/partial.
if libm/translate_libm.sh > "$TMP/libm.out" 2>&1; then
  if [ "${1:-}" = "--update" ]; then rm -rf tests/golden/libm; mkdir -p tests/golden/libm; cp -R libm/out/Musl libm/out/Musl.lean tests/golden/libm/; rm -f tests/golden/libm/Musl/*.json; fi
  for f in libm/out/Musl.lean libm/out/Musl/*.lean; do
    g="tests/golden/libm/${f#libm/out/}"
    if diff -u "$g" "$f"; then ok "golden: $f -> $g"; else bad "golden: $f (diff above)"; fi
    if grep -nE '\bsorry\b|^axiom|partial def' "$f"; then bad "sorry/axiom/partial in $f"; fi
  done
else cat "$TMP/libm.out"; bad "libm/translate_libm.sh"; fi

# 2. Rejections: exit status 2, the expected messages, and exactly the lines marked expect-reject.
for src in tests/reject_*.cpp tests/reject_*.c; do
  exp="${src%.*}.expected"
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

# 3. ArduPilot (if the tree is there): the AC_PID family, AP_Math, the controllers as one World
#    (Copter: AP_MotorsMatrix, AC_AttitudeControl_Multi, AC_PosControl, AC_WPNav, AC_Loiter, AC_Circle),
#    the AHRS view derivation and the phase 2 libraries translate to exactly the committed Lean (the
#    scripts other than AC_PID's first check their unity files with ardupilot/check_unity.py), and the
#    library code the World and the view carry is the code of the AP_Math and AC_PID translations
#    (ardupilot/check_shared.py; the World's boundary calls, `Output`, and `World` are its own).
AP="${AP:-$PWD/ardupilot/src}"
if [ -d "$AP/libraries/AC_PID" ]; then
  for t in AC_PID:ac_pid:AC_PID_lib AP_Math:ap_math:AP_Math_lib Copter:copter:Copter_lib AHRS_View:ahrs_view:AHRS_View_lib \
           LowPassFilter2p:lowpassfilter2p:LowPassFilter2p_lib AC_CommandModel:ac_commandmodel:AC_CommandModel_lib \
           AP_Declination:ap_declination:AP_Declination_lib AP_Common:ap_common:AP_Common_lib \
           Text:text:Text_lib StorageManager:storage:StorageManager_lib AP_InternalError:internalerror:AP_InternalError_lib \
           AP_RTC:rtc:AP_RTC_lib EKF_Buffer:ekf_buffer:EKF_Buffer_lib EKFGSF:ekfgsf:EKFGSF_lib EstScheduler:est_scheduler:EstScheduler_lib \
           EKF3:ekf3:EKF3_lib Sensors:sensors:Sensors_lib NavEKF_Source:navekf_source:NavEKF_Source_lib \
           Estimation:estimation:Estimation_lib AHRS:ahrs:AHRS_lib Estimator:estimator:Estimator_lib Mavlink:mavlink:Mavlink_lib Mission:mission:Mission_lib; do
    d="${t%%:*}"; rest="${t#*:}"; script="${rest%%:*}"; ns="${rest#*:}"
    case "$d" in EKF_Buffer|EKFGSF|EstScheduler|EKF3|Sensors|NavEKF_Source|Estimation|AHRS|Estimator|Mavlink|Mission) [ -d build/reference/ap/build/sitl ] || continue ;; esac   # real headers: the reference build
    if "ardupilot/translate_$script.sh" > "$TMP/ap.out" 2>&1; then
      if [ "${1:-}" = "--update" ]; then mkdir -p tests/golden/ardupilot; cp "ardupilot/out/$d/$ns.lean" "tests/golden/ardupilot/$ns.lean"; fi
      if diff -u "tests/golden/ardupilot/$ns.lean" "ardupilot/out/$d/$ns.lean"; then ok "golden: ArduPilot $d -> tests/golden/ardupilot/$ns.lean"
      else bad "golden: ArduPilot $d (diff above)"; fi
      if grep -nE '\bsorry\b|^axiom|partial def' "ardupilot/out/$d/$ns.lean"; then bad "sorry/axiom/partial in $ns.lean"; fi
    else cat "$TMP/ap.out"; bad "ardupilot/translate_$script.sh"; fi
  done
  for xy in Copter/Copter_lib:AP_Math/AP_Math_lib Copter/Copter_lib:AC_PID/AC_PID_lib AHRS_View/AHRS_View_lib:AP_Math/AP_Math_lib; do
    x="${xy%%:*}"; y="${xy#*:}"
    if python3 ardupilot/check_shared.py "ardupilot/out/$x.lean" "ardupilot/out/$y.lean" --rename Vector2_double=Vector2p --skip Output,Outputs,World > "$TMP/sh.out"; then
      ok "shared library code: $(tail -1 "$TMP/sh.out")"
    else cat "$TMP/sh.out"; bad "shared library code: $x vs $y"; fi
  done
  AP_TARGETS="ardupilot/AC_PID ardupilot/AP_Math ardupilot/Copter ardupilot/AHRS_View"
  AP_TARGETS="$AP_TARGETS ardupilot/LowPassFilter2p ardupilot/AC_CommandModel ardupilot/AP_Declination ardupilot/AP_Common"   # phase 2
  AP_TARGETS="$AP_TARGETS ardupilot/Text ardupilot/StorageManager ardupilot/AP_InternalError"   # phase 2b (AP_RTC: golden only)
  if [ -d build/reference/ap/build/sitl ]; then
    AP_TARGETS="$AP_TARGETS ardupilot/EKF_Buffer ardupilot/EKFGSF"   # Phase 3 EKF data structures (real headers: the reference build)
    AP_TARGETS="$AP_TARGETS ardupilot/EKF3"   # Phase 3 AP_DAL and NavEKF3 (its own harness, ardupilot/ekf3_difftest.py)
    AP_TARGETS="$AP_TARGETS ardupilot/Sensors"   # Phase 3 sensor front ends (the World with the stand-ins and the scheduler)
    AP_TARGETS="$AP_TARGETS ardupilot/NavEKF_Source"   # Phase 3 AP_NavEKF_Source (EKF3's source selection)
    AP_TARGETS="$AP_TARGETS ardupilot/Estimation"   # Phase 3 the estimator World (front ends, AP_DAL, NavEKF3 with its sources)
    AP_TARGETS="$AP_TARGETS ardupilot/AHRS"   # Phase 3 AP_AHRS with its DCM and EKF3 backends (its own harness, ardupilot/ahrs_difftest.py)
    AP_TARGETS="$AP_TARGETS ardupilot/Mavlink"   # Phase 4 the MAVLink C library (its translation script also checks the record layouts against clang's)
    AP_TARGETS="$AP_TARGETS ardupilot/Mission"   # Phase 4 AP_Mission (storage, conversions; its translation script checks the record layouts too)
  fi
else
  echo "skip  ArduPilot tree not found at $AP"
  AP_TARGETS=""
fi

# 3b. AP_Param over one byte memory (README.md, "Phase 4: AP_Param"; needs the reference build): translates to exactly
#     the committed Lean (`partial def` is expected here: AP_Param's group walks are recursive), deterministically, with
#     the runtime equal to support/ParamMemory.lean.
if [ -d build/reference/ap/build/sitl ] && [ -f sim/out/lockstep-flight/est.txt ]; then
  if ardupilot/translate_param.sh > "$TMP/pm.out" 2>&1 && PARAM_HARNESS=0 PYTHONHASHSEED=7 ardupilot/translate_param.sh "$TMP/pm2" > /dev/null 2>&1; then
    if [ "${1:-}" = "--update" ]; then cp ardupilot/out/AP_Param/AP_Param_lib.lean tests/golden/ardupilot/AP_Param_lib.lean; cp lean/ParamHarnessData.lean tests/golden/ardupilot/ParamHarnessData.lean; fi
    if diff -u tests/golden/ardupilot/AP_Param_lib.lean ardupilot/out/AP_Param/AP_Param_lib.lean; then ok "golden: ArduPilot AP_Param -> tests/golden/ardupilot/AP_Param_lib.lean"
    else bad "golden: ArduPilot AP_Param (diff above)"; fi
    if diff -u tests/golden/ardupilot/ParamHarnessData.lean lean/ParamHarnessData.lean; then ok "golden: AP_Param harness data -> tests/golden/ardupilot/ParamHarnessData.lean"
    else bad "golden: AP_Param harness data (diff above)"; fi
    if cmp -s "$TMP/pm2/AP_Param_lib.lean" ardupilot/out/AP_Param/AP_Param_lib.lean; then ok "deterministic: AP_Param"; else bad "two runs of translate_param.sh differ"; fi
    if cmp -s support/ParamMemory.lean ardupilot/out/AP_Param/ParamMemory.lean; then ok "ParamMemory.lean = support/ParamMemory.lean"; else bad "ParamMemory.lean"; fi
    if grep -nE '\bsorry\b|^axiom' ardupilot/out/AP_Param/AP_Param_lib.lean; then bad "sorry/axiom in AP_Param_lib.lean"; fi
  else cat "$TMP/pm.out"; bad "ardupilot/translate_param.sh"; fi
fi

# 3c. GCS_MAVLink over the byte memory (README.md, "Phase 4: GCS_MAVLink"; needs the reference build): translates to
#     exactly the committed Lean, deterministically, with the runtimes equal to support/.
if [ -d build/reference/ap/build/sitl ]; then
  if ardupilot/gcs/translate_gcs.sh > "$TMP/gcs.out" 2>&1 && PYTHONHASHSEED=7 ardupilot/gcs/translate_gcs.sh "$TMP/gcs2" > /dev/null 2>&1; then
    if [ "${1:-}" = "--update" ]; then cp ardupilot/out/GCS/GCS_lib.lean tests/golden/ardupilot/GCS_lib.lean; fi
    if diff -u tests/golden/ardupilot/GCS_lib.lean ardupilot/out/GCS/GCS_lib.lean > /dev/null; then ok "golden: ArduPilot GCS_MAVLink -> tests/golden/ardupilot/GCS_lib.lean"
    else bad "golden: ArduPilot GCS_MAVLink (diff tests/golden/ardupilot/GCS_lib.lean ardupilot/out/GCS/GCS_lib.lean)"; fi
    if cmp -s "$TMP/gcs2/GCS_lib.lean" ardupilot/out/GCS/GCS_lib.lean; then ok "deterministic: GCS_MAVLink"; else bad "two runs of translate_gcs.sh differ"; fi
    if cmp -s support/GCSMemory.lean ardupilot/out/GCS/GCSMemory.lean && cmp -s support/ParamMemory.lean ardupilot/out/GCS/ParamMemory.lean; then ok "GCSMemory.lean, ParamMemory.lean = support/"; else bad "GCS runtimes"; fi
    if grep -nE '\bsorry\b|^axiom' ardupilot/out/GCS/GCS_lib.lean; then bad "sorry/axiom in GCS_lib.lean"; fi
  else cat "$TMP/gcs.out"; bad "ardupilot/gcs/translate_gcs.sh"; fi
fi

# 4. The Lean package builds from clean with no warnings (its own build: the dependencies FloatLib and
#    Mathlib in lean/.lake/packages are kept), and the differential test passes.
rm -rf lean/.lake/build
python3 difftest.py $(ls examples/*.cpp | grep -v '_driver\.cpp$' | sed 's|examples/||; s|\.cpp$||') $AP_TARGETS > "$TMP/difftest.out" 2>&1
st=$?
cat "$TMP/difftest.out"
if [ $st -eq 0 ]; then ok "difftest: 0 differing lines"; else bad "difftest (exit $st)"; fi
if grep -q "warning" "$TMP/difftest.out"; then bad "warnings in the Lean build"; else ok "Lean build without warnings"; fi

# 5. The per-tick composition of the World's motors, attitude and position controllers against the
#    oracle's recorded flight (if the oracle's output is there): 500 ticks. The oracle was recorded with
#    the platform's libm, the composition runs musl's functions (README.md, "The C library"): the
#    actuators are bit-identical on the 500 ticks, the other values from tick 491 on differ in the
#    last bit; the check requires the actuators.
if [ -n "$AP_TARGETS" ] && [ -f ardupilot/data/oracle-nosincos.txt ] && [ -f ardupilot/data/inputs.txt ]; then
  ardupilot/compose/compose.sh 500 > "$TMP/compose.out" 2>&1
  if grep -qE "^composition: 500 ticks; actuators bit-identical to the oracle on 500 of 500 ticks" "$TMP/compose.out"; then
    grep -E "^composition|first difference" "$TMP/compose.out" | sed 's/^/      /'
    ok "composition: 500 ticks, actuators equal to the oracle (recorded with the platform's libm)"
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

# 7. The estimator World with AP_AHRS (ardupilot/out/Estimator, translated in 3.) replayed on both recorded flights
#    against the reference's estimation trace (README.md "Phase 3: AP_AHRS in the estimator World, the full estimation
#    replay"): every AP_AHRS, EKF3, front-end and vehicle-side key of every step bit-identical (about 15 s per flight
#    after the Lean build). Needs the reference vehicle (python3 reference/build.py), whose `--est` trace the replay
#    writes into build/est/ when it is missing or older than copter_ref.
if [ -n "$AP_TARGETS" ] && [ -x build/reference/copter_ref ] && [ -f ardupilot/out/Estimator/Estimator_lib.lean ] && \
   [ -f sim/out/lockstep-flight/inputs.txt ] && [ -f sim/out/lockstep-flight-noisy/inputs.txt ]; then
  cp ardupilot/out/Estimator/Estimator_lib.lean lean/Estimator_lib.lean
  nb=""
  for F in lockstep-flight lockstep-flight-noisy; do
    if python3 ardupilot/estimation_replay.py "sim/out/$F" $nb > "$TMP/er.out" 2>&1; then
      head -2 "$TMP/er.out" | sed 's/^/      /'
      ok "estimation replay $F: every compared value bit-identical (Lean build without warnings)"
    else cat "$TMP/er.out"; bad "estimation replay $F (ardupilot/estimation_replay.py)"; fi
    nb="--no-build"
  done
else
  echo "skip  estimation replay (no reference vehicle build/reference/copter_ref, Estimator translation or recorded flights)"
fi

# 8. The mission round trip of the recorded flight against the reference (README.md "Phase 4: AP_Mission"): the flight's
#    uplink parsed by the translated MAVLink library, the mission stored and read back by the translated AP_Mission;
#    the items equal to those the reference sent, the mission storage equal to the reference's (the trace replayed).
if [ -n "$AP_TARGETS" ] && [ -x build/reference/copter_ref ] && [ -f ardupilot/out/Mission/Mission_lib.lean ] && \
   [ -f sim/out/lockstep-flight/inputs.txt ]; then
  cp ardupilot/out/Mission/Mission_lib.lean lean/Mission_lib.lean
  if (cd lean && LEAN_NUM_THREADS=1 lake build mission_roundtrip > "$TMP/mrt_build.out" 2>&1) && \
     python3 ardupilot/mission_roundtrip.py sim/out/lockstep-flight > "$TMP/mrt.out" 2>&1; then
    grep -E "^items|^storage" "$TMP/mrt.out" | sed 's/^/      /'
    ok "mission round trip lockstep-flight: items and mission storage equal to the reference's"
  else cat "$TMP/mrt_build.out" "$TMP/mrt.out" 2>/dev/null | tail -30; bad "mission round trip (ardupilot/mission_roundtrip.py)"; fi
else
  echo "skip  mission round trip (no reference vehicle, Mission translation or recorded flight)"
fi
# 9. AP_Param (README.md, "Phase 4: AP_Param"): the vehicle's AP_Param boot sequence to load_all and the enumeration
#    before and after it, translated (lean/.lake/build/bin/param_dump) against the reference (copter_ref --param-dump), on
#    the two recorded storage images and blank storage: identical dumps; and the per-function differential test
#    (ardupilot/param_difftest.py: random images and command scripts, 0 differing lines).
if [ -x build/reference/copter_ref ] && [ -f ardupilot/out/AP_Param/AP_Param_lib.lean ] && [ -f sim/out/lockstep-flight/storage_in.bin ]; then
  cp ardupilot/out/AP_Param/AP_Param_lib.lean ardupilot/out/AP_Param/ParamMemory.lean lean/
  if (cd lean && lake build param_dump > "$TMP/pd.out" 2>&1) && ! grep -q "warning" "$TMP/pd.out"; then
    head -c 16384 /dev/zero > "$TMP/blank.bin"
    for img in sim/out/lockstep-flight/storage_in.bin sim/out/lockstep-qgc/harness/storage_in.bin "$TMP/blank.bin"; do
      [ -f "$img" ] || continue
      build/reference/copter_ref --storage "$img" --param-dump "$TMP/pd_ref.txt" < /dev/null 2> /dev/null
      lean/.lake/build/bin/param_dump "$img" "$TMP/pd_lean.txt" 2> /dev/null
      if cmp -s "$TMP/pd_ref.txt" "$TMP/pd_lean.txt"; then ok "AP_Param dump $img: identical ($(grep '^# count ' "$TMP/pd_ref.txt" | tr '\n' ' '))"
      else diff "$TMP/pd_ref.txt" "$TMP/pd_lean.txt" | head; bad "AP_Param dump $img"; fi
    done
    if python3 ardupilot/param_difftest.py --cases 66 > "$TMP/pdt.out" 2>&1; then ok "$(tail -1 "$TMP/pdt.out")"
    else cat "$TMP/pdt.out"; bad "ardupilot/param_difftest.py"; fi
  else cat "$TMP/pd.out"; bad "lake build param_dump (warnings or errors)"; fi
else
  echo "skip  AP_Param dump (no reference vehicle or AP_Param translation)"
fi

if [ $fail -eq 0 ]; then echo "all tests passed"; else echo "some tests FAILED"; fi
exit $fail
