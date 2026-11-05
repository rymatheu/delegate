#!/usr/bin/env bash
# Replay check of the two vehicles (no simulator): both binaries on the recorded flight
# (ardupilot/data/inputs.txt, 8431 ticks) with the parameter files of that flight
# (sim/params/copter-cf2x.txt, whose waypoint list is the recorded flight's figure-eight mission, and
# sim/params/copter-course-speed.txt), with --exact --trace --bits: the 22 values of every tick must be
# bit-identical between copter_lean and copter_ref, and the two must print the same parameters. Then
# both are related to the recorded reference output ardupilot/data/oracle-nosincos.txt, whose
# navigator targets came from the recording, not from AC_WPNav (informational).
# Usage: ardupilot/vehicle/replay.sh   (after ardupilot/vehicle/build.sh)
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
LEAN="$ROOT/lean/.lake/build/bin/copter_lean"
REF="$ROOT/build/vehicle/copter_ref"
B="$ROOT/build/vehicle"
mkdir -p "$B"
P=(--params "$ROOT/sim/params/copter-cf2x.txt" --params "$ROOT/sim/params/copter-course-speed.txt")
"$LEAN" "${P[@]}" --print-params > "$B/params-lean.txt"
"$REF" "${P[@]}" --print-params > "$B/params-ref.txt"
"$LEAN" "${P[@]}" --exact --trace --bits < "$ROOT/ardupilot/data/inputs.txt" > "$B/replay-lean.txt"
"$REF" "${P[@]}" --exact --trace --bits < "$ROOT/ardupilot/data/inputs.txt" > "$B/replay-ref.txt"
python3 - "$B" "$ROOT/ardupilot/data/oracle-nosincos.txt" <<'PY'
import sys
b, orc = sys.argv[1], sys.argv[2]
names = ["m1", "m2", "m3", "m4", "pos_n", "pos_e", "pos_d", "vel_n", "vel_e", "vel_d", "acc_n", "acc_e", "acc_d",
         "thr_n", "thr_e", "thr_d", "roll_t", "pitch_t", "yaw_t", "p_t", "q_t", "r_t"]
pl, pr = open(b + "/params-lean.txt").read(), open(b + "/params-ref.txt").read()
print("parameters: %d lines each, %s" % (len(pr.splitlines()), "identical" if pl == pr else "DIFFERENT"))
def load(p):
    return [(l.split("|")[0].split(), l.split("|")[1].split()) for l in open(p).read().splitlines()]
L, R, O = load(b + "/replay-lean.txt"), load(b + "/replay-ref.txt"), load(orc)
n = len(R)
same = sum(1 for k in range(n) if k < len(L) and L[k][1] == R[k][1])
text = sum(1 for k in range(n) if k < len(L) and L[k][0] == R[k][0])
print("replay: %d and %d ticks; all 22 values bit-identical between copter_lean and copter_ref on %d of %d ticks (exact decimals equal on %d)"
      % (len(L), n, same, n, text))
bad = [k for k in range(n) if k >= len(L) or L[k][1] != R[k][1]]
if bad:
    k = bad[0]
    print("  first difference at tick %d: %s" % (k + 1, ", ".join("%s Lean %s C++ %s" % (names[j], L[k][1][j], R[k][1][j]) for j in range(22) if L[k][1][j] != R[k][1][j])))
oa = sum(1 for k in range(n) if R[k][1][:4] == O[k][1][:4])
ob = sum(1 for k in range(n) if R[k][1] == O[k][1])
first = {nm: next((k + 1 for k in range(n) if R[k][1][j] != O[k][1][j]), None) for j, nm in enumerate(names)}
print("relation to oracle-nosincos.txt (navigator targets from the recording): actuators equal on %d of %d ticks, all 22 values on %d; "
      "first difference: navigator targets (pos_n %s, vel_n %s, acc_n %s), actuators (m1 %s), attitude targets (roll_t %s)"
      % (oa, n, ob, first["pos_n"], first["vel_n"], first["acc_n"], first["m1"], first["roll_t"]))
for k in (0, 999, 3999, 6617, n - 1):
    print("  tick %d: position target AC_WPNav %s, recording %s" % (k + 1, " ".join("%.4f" % float(x) for x in R[k][0][4:7]),
                                                                  " ".join("%.4f" % float(x) for x in O[k][0][4:7])))
sys.exit(0 if same == n and len(L) == n and pl == pr else 1)
PY
