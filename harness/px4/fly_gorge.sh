#!/usr/bin/env bash
# The PX4 stack through the gorge with no ground station to watch: scripted, ends by itself.
#
#   px4/fly_gorge.sh [single|abreast|staggered] [--port P] [--seed N] [--out DIR] [--real-time]
#   px4/fly_gorge.sh single --plan plans/formation-staggered-v2.plan --sysid 2
#                    (another plan, from px4/; the vehicle as MAVLink system 2: parameter MAV_SYS_ID)
#
# single: one X500 (px4_full: PX4 v1.17.0 sensors, EKF2, controllers, flight mode manager, land
# detector, commander, navigator, MAVLink; simulator sensor noise, seed N, default 1), flown as
# QGroundControl would fly it: px4/gorge/gcs.py listens on UDP 127.0.0.1:P (default 14570) like
# QGroundControl, the vehicle (px4/harnesses/px4_full/dev/relay.py, `harness serve px4_full` in real
# time) sends to it; the ground station downloads the parameters, uploads px4/plans/gorge.plan with
# the mission protocol, arms, starts the mission, and PX4 flies it, lands and disarms by itself.
# The relay stops 2 s (vehicle time) after the disarm. The stack is stepped as fast as it goes
# (the vehicle's clock is the simulator's; --real-time paces it at one tick per 2.5 ms, as
# fly_qgc.sh does); the summary gives the ticks per second reached.
# abreast, staggered: two X500s in one gorge (px4_formation: plant_formation and two px4_full stacks
# as instances v1 and v2, stepped concurrently, MAVLink systems 1 and 2, each its own UDP socket to
# the one ground-station port), each with its plan px4/plans/formation-SCENARIO-v1.plan, -v2.plan,
# armed and started together; the formation's clauses min_separation (1.5 m) and wall_clearance
# (0.5 m) are monitored at every tick. Truth per vehicle: truth-v1.csv, truth-v2.csv.
#
# Output in DIR (default px4/out/gorge-SCENARIO-seedN): truth.csv (the simulator's pose and PX4's
# state, 100 Hz), vN.gpi.csv (each vehicle's GLOBAL_POSITION_INT), gcs.log, relay.log, serve.log
# (the monitors' verdicts), metrics.json (wall clearance, heading, separation), summary.txt. Last line: PASS or FAIL.
#
# Environment: SIM_DIR, the simulator's folder (default: sim/ at the repository root);
# SIM_PYTHON, its Python (default: SIM_DIR/.venv/bin/python, made by sim/setup.sh).
set -uo pipefail
PX4_DIR="$(cd "$(dirname "$0")" && pwd)"
HARNESS="$(cd "$PX4_DIR/.." && pwd)"
ROOT="$(cd "$HARNESS/.." && pwd)"
SCEN=single
case "${1:-}" in single|abreast|staggered) SCEN="$1"; shift ;; esac
PORT="${MAV_PORT:-14570}"; SEED=1; OUT=""; PLAN=plans/gorge.plan; SYSID=1; PACE=(--fast)
while [ $# -gt 0 ]; do
  case "$1" in
    --port) PORT="$2"; shift ;;
    --seed) SEED="$2"; shift ;;
    --out) OUT="$2"; shift ;;
    --plan) PLAN="$2"; shift ;;
    --sysid) SYSID="$2"; shift ;;
    --real-time) PACE=() ;;
    *) echo "usage: px4/fly_gorge.sh [single|abreast|staggered] [--port P] [--seed N] [--out DIR] [--real-time]" >&2; exit 2 ;;
  esac
  shift
done
SIM_DIR="${SIM_DIR:-$ROOT/sim}"
SIM_PYTHON="${SIM_PYTHON:-$SIM_DIR/.venv/bin/python}"
OUT="${OUT:-$PX4_DIR/out/gorge-$SCEN-seed$SEED}"
case "$PORT" in 14550|14560) echo "fly_gorge.sh: not on $PORT (the ground station's)" >&2; exit 2 ;; esac
if lsof -nP -iUDP:"$PORT" > /dev/null 2>&1; then echo "fly_gorge.sh: UDP $PORT is in use; give --port P" >&2; exit 1; fi
for f in .lake/build/bin/harness build/modules/plant_sim/plant_sim build/modules/plant_formation/plant_formation \
         build/modules/px4_mavlink/px4_mavlink \
         build/modules/px4_navigator/px4_navigator build/px4venv/bin/python; do
  [ -e "$HARNESS/$f" ] || { echo "fly_gorge.sh: $f is missing; build first (README.md, Build)" >&2; exit 1; }
done
mkdir -p "$OUT"
cd "$HARNESS"
if [ "$SCEN" = single ]; then
  NODE=px4_full
  VEH=(--vehicle "$SYSID=$PX4_DIR/$PLAN")
  REL=(--set MAV_SYS_ID="$SYSID")
  TRUTHS=("$OUT/truth.csv")
  echo "fly_gorge.sh: one X500 through the gorge on px4_full, plan px4/$PLAN, seed $SEED; output $OUT"
else
  NODE=px4_formation
  F=1; [ "$SCEN" = staggered ] && F=2
  VEH=(--vehicle "1=$PX4_DIR/plans/formation-$SCEN-v1.plan" --vehicle "2=$PX4_DIR/plans/formation-$SCEN-v2.plan")
  REL=(--node px4_formation --set formation=$F)
  TRUTHS=("$OUT/truth-v1.csv" "$OUT/truth-v2.csv")
  echo "fly_gorge.sh: two X500s, formation $SCEN, on px4_formation (two px4_full stacks, MAVLink systems 1 and 2)," \
       "plans px4/plans/formation-$SCEN-v1.plan and -v2.plan, seed $SEED; output $OUT"
fi
build/px4venv/bin/python -I px4/gorge/gcs.py --port "$PORT" "${VEH[@]}" --log "$OUT" > "$OUT/gcs.log" 2>&1 &
GCS=$!
python3 -I px4/harnesses/px4_full/dev/relay.py --gcs "127.0.0.1:$PORT" --set noise_seed="$SEED" "${REL[@]}" \
  --truth "$OUT/truth.csv" --every 4 --exit-on-disarm 2 ${PACE[@]+"${PACE[@]}"} > "$OUT/relay.log" 2>&1 &
RELAY=$!
trap 'kill -TERM $GCS $RELAY 2>/dev/null; wait $GCS $RELAY 2>/dev/null' INT TERM
wait $GCS; RC=$?
# the relay ends by itself after the disarm; if the flight failed, stop it
for _ in $(seq 1 30); do kill -0 $RELAY 2>/dev/null || break; sleep 1; done
kill -TERM $RELAY 2>/dev/null; wait $RELAY 2>/dev/null
trap - INT TERM
cp "build/serve/$NODE.log" "$OUT/serve.log"
"$SIM_PYTHON" -B "$PX4_DIR/gorge/metrics.py" --sim "$SIM_DIR" "${TRUTHS[@]}" --json "$OUT/metrics.json" \
  > "$OUT/metrics.log" 2>&1 || RC=1
python3 -I "$PX4_DIR/gorge/summary.py" "$OUT" $RC | tee "$OUT/summary.txt"
grep -q "^RESULT PASS" "$OUT/summary.txt"
