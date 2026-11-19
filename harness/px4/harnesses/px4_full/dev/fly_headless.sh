#!/usr/bin/env bash
# A headless flight of px4_full: px4/harnesses/px4_full/dev/fly_headless.sh (mission|commands) SEED
# Starts relay.py listening on UDP 127.0.0.1:$PORT (default 14570; refuses if the port is taken) with noise seed
# SEED, flies gcs_flight.py against it, stops the relay, compares the vehicle's reported
# positions with the simulator's truth. Nothing is kept by default (a temporary directory, removed at the end);
# RECORD=1 keeps the logs in build/logs/full_<mode>_<seed>.* and appends the session's ledger record.
set -uo pipefail
MODE="${1:?usage: fly_headless.sh (mission|commands) SEED}"; SEED="${2:?usage: fly_headless.sh MODE SEED}"
HARNESS="$(cd "$(dirname "$0")/../../../.." && pwd)"
cd "$HARNESS"
PORT="${PORT:-14570}"   # the MAVLink port (environment PORT)
if lsof -nP -iUDP:$PORT > /dev/null 2>&1; then echo "fly_headless.sh: UDP $PORT is in use" >&2; exit 1; fi
TMP="$(mktemp -d "${TMPDIR:-/tmp}/fly_headless.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
if [ "${RECORD:-0}" = 1 ]; then
  mkdir -p build/logs; B=build/logs/full_${MODE}_${SEED}; export HARNESS_RECORD=1
else
  B="$TMP/full_${MODE}_${SEED}"; unset HARNESS_RECORD
fi
export HARNESS_SERVE_LOG="$B.serve.log"
PX4_SHIM_LOG=1 python3 -I -B px4/harnesses/px4_full/dev/relay.py --port $PORT --set noise_seed=$SEED --truth $B.truth.csv \
  > $B.relay.log 2>&1 &
RELAY=$!
build/px4venv/bin/python -I -B px4/harnesses/px4_full/dev/gcs_flight.py $MODE --port $PORT --log $B.gpi.csv \
  > $B.gcs.log 2>&1
RC=$?
kill -TERM $RELAY; wait $RELAY
build/px4venv/bin/python -I -B px4/harnesses/px4_full/dev/gcs_flight.py compare --log $B.gpi.csv \
  --truth $B.truth.csv >> $B.gcs.log 2>&1 || RC=1
python3 -I -B px4/harnesses/px4_full/dev/truth_summary.py $B.truth.csv > $B.summary.txt
grep -E "PASS|FAIL" $B.gcs.log; cat $B.summary.txt; tail -1 $B.relay.log; grep -v "violations: none" $B.serve.log
lsof -nP -iUDP:$PORT > /dev/null 2>&1 && echo "fly_headless.sh: UDP $PORT still open" >&2
exit $RC
