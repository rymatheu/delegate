#!/usr/bin/env bash
# Check that a fresh clone of this repository builds, flies and matches its committed evidence.
#
#   harness/tools/check_fresh_clone.sh [--keep]
#
# Clones the repository's current HEAD (`git clone` from the local repository this script is in) into a temporary
# directory (under $TMPDIR, default /tmp), then runs there exactly the README's build steps:
#   (with a `python3` that only fails first on PATH: no step may use the PATH one)
#   tools/fetch_deps.sh  (ARDUPILOT_SRC, PX4_SRC, MAVLINK_SRC are honored: set them to reuse local clones)
#   ../sim/setup.sh
#   LEAN_NUM_THREADS=1 lake build
#   tools/build_modules.sh sim, ardupilot, px4
# then `./fly_gorge.sh single` on each stack (nothing recorded; PX4's ground-station port is $MAV_PORT, default
# 14570), compares every module's code hash with the hashes its committed ledger names, and reports
# `harness status` for ap_full_ekf, ap_formation, px4_full and px4_formation (no stale clause allowed).
# Prints one PASS/FAIL line per step and a last line PASS or FAIL. The temporary directory is removed at the end
# unless --keep (then its path is printed). Nothing is written into this repository. About 15 min.
set -uo pipefail
KEEP=0
for a in "$@"; do
  case "$a" in
    --keep) KEEP=1 ;;
    *) echo "usage: tools/check_fresh_clone.sh [--keep]" >&2; exit 2 ;;
  esac
done
ROOT="$(cd "$(dirname "$0")/../.." && pwd -P)"
HEAD="$(git -C "$ROOT" rev-parse HEAD)" || { echo "check_fresh_clone: $ROOT is not a git repository" >&2; exit 2; }
WORK="$(mktemp -d "${TMPDIR:-/tmp}/check_fresh_clone.XXXXXX")"
CLONE="$WORK/repo"
LOGS="$WORK/logs"
mkdir -p "$LOGS"
cleanup() {
  if [ "$KEEP" = 1 ]; then echo "kept: $WORK"; else rm -rf "$WORK"; fi
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

FAILED=0
# step NAME COMMAND...: run COMMAND (output to logs/NAME.log), print one PASS/FAIL line with the time
step() {
  local name="$1"; shift
  local t0=$SECONDS rc=0
  "$@" > "$LOGS/$name.log" 2>&1 || rc=$?
  if [ "$rc" = 0 ]; then
    printf 'PASS  %-28s %4d s\n' "$name" $((SECONDS - t0))
  else
    printf 'FAIL  %-28s %4d s  (exit %s; last lines of its log:)\n' "$name" $((SECONDS - t0)) "$rc"
    tail -n 15 "$LOGS/$name.log" | sed 's/^/        /'
    FAILED=1
  fi
  return "$rc"
}

abort() { echo FAIL; exit 1; }
echo "fresh clone of HEAD ${HEAD:0:12} in $WORK"
step clone bash -c 'git clone -q "$0" "$1" && git -C "$1" checkout -q --detach "$2"' "$ROOT" "$CLONE" "$HEAD" || abort
H="$CLONE/harness"
# No step may depend on the `python3` (or `python`) that happens to be first on PATH: every script uses the
# environments this repository makes (sim/.venv, build/px4venv). Here a stand-in that only fails is put first on PATH.
mkdir -p "$WORK/no-python"
for n in python3 python; do
  printf '#!/bin/sh\necho "check_fresh_clone: the PATH %s was called: $*" >&2\nexit 97\n' "$n" > "$WORK/no-python/$n"
  chmod +x "$WORK/no-python/$n"
done
export PATH="$WORK/no-python:$PATH"
HB="$H/.lake/build/bin/harness"
cd "$H" || abort

step fetch_deps tools/fetch_deps.sh || abort
step sim_setup ../sim/setup.sh || abort
step lake_build env LEAN_NUM_THREADS=1 lake build || abort
step build_modules_sim tools/build_modules.sh sim
step build_modules_ardupilot tools/build_modules.sh ardupilot
step build_modules_px4 tools/build_modules.sh px4
step fly_gorge_ardupilot_single bash -c 'cd ardupilot && ./fly_gorge.sh single'   # exit 0 iff its summary is PASS
step fly_gorge_px4_single bash -c 'cd px4 && ./fly_gorge.sh single'

# every module's code hash, as its executable reports it, against the code hashes its committed ledger names
hashes() {
  local bad=0 n=0 kind name stack
  while read -r name stack kind _; do
    [ "$kind" = module ] || continue
    n=$((n + 1))
    local got ledger
    got="$("$HB" status "$name" 2>&1 | grep -m1 -oE 'code hash [0-9a-f]{64}' | awk '{print $3}')"
    ledger="$stack/modules/$name/evidence/ledger.json"
    if [ -z "$got" ]; then
      echo "  $name: no code hash (not built?)"; bad=1
    elif [ ! -f "$ledger" ]; then
      echo "  $name: no ledger $ledger"; bad=1
    elif "$CLONE/sim/.venv/bin/python" -I -c 'import json,sys; sys.exit(0 if sys.argv[2] in {r.get("code_hash") for r in json.load(open(sys.argv[1]))["records"]} else 1)' \
         "$ledger" "$got"; then
      echo "  $name: ${got:0:16} equals its ledger's"
    else
      echo "  $name: ${got:0:16} is not a code hash of $ledger"; bad=1
    fi
  done < <("$HB" list | tail -n +2)
  echo "  $n modules"
  return "$bad"
}
step module_code_hashes hashes
grep -v 'equals its ledger' "$LOGS/module_code_hashes.log" | sed 's/^/    /'
echo "    $(grep -c 'equals its ledger' "$LOGS/module_code_hashes.log") module code hashes equal their ledger's"

# harness status of the four flight systems: no stale clause (nor a failed one)
status_of() {
  "$HB" status "$1" > "$LOGS/status_$1.txt" 2>&1 || return 1
  local stale failed
  stale="$(grep -cw stale "$LOGS/status_$1.txt")"
  failed="$(grep -cwE 'failed|undischarged' "$LOGS/status_$1.txt")"
  echo "status $1: $(grep -cw backed "$LOGS/status_$1.txt") lines backed, $stale stale, $failed failed or undischarged"
  [ "$stale" = 0 ] && [ "$failed" = 0 ]
}
for node in ap_full_ekf ap_formation px4_full px4_formation; do
  step "status_$node" status_of "$node"
  sed 's/^/    /' "$LOGS/status_$node.log"
done

if [ "$FAILED" = 0 ]; then echo PASS; else echo FAIL; exit 1; fi
