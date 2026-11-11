#!/bin/sh
# The estimator runs of README.md "EKF": both vehicles x both estimators, deterministic and field seeds 0..4,
# and for the X500 field seeds 0..4 without calibration and with a GPS dropout over 10 <= t < 14 s (the last
# 2 s of the last leg, which ends at about 12.2 s, and the first 2 s of the hold). Each flies the vehicle file's
# WAYPOINT square with the heading held (params/yawhold.params), as these tables did before the heading
# followed the path. CSV + JSON in sim/out/ekf/ (the runs made with the navigator before the leg kinds are in
# sim/out/ekf-stopping/), tables by sim/ekf_tables.py. Runs JOBS (default 3) simulations at a time; EST
# (default "fixed ekf") limits the estimators.
cd "$(dirname "$0")/.." || exit 1
PY=${PY:-sim/.venv/bin/python}
OUT=sim/out/ekf
mkdir -p $OUT
{
  for v in x500 cf2x; do
    for e in ${EST:-fixed ekf}; do
      echo "--params params/$v.params --params params/yawhold.params --estimator $e --noise none --out $OUT/$v-$e-det-s0.csv"
      for s in 0 1 2 3 4; do
        echo "--params params/$v.params --params params/yawhold.params --estimator $e --noise field --seed $s --out $OUT/$v-$e-field-s$s.csv"
      done
    done
  done
  for e in ${EST:-fixed ekf}; do
    for s in 0 1 2 3 4; do
      echo "--params params/x500.params --params params/yawhold.params --estimator $e --noise field --seed $s --no-calibration --out $OUT/x500-$e-nocal-s$s.csv"
      echo "--params params/x500.params --params params/yawhold.params --estimator $e --noise field --seed $s --dropout 10 14 --out $OUT/x500-$e-drop-s$s.csv"
    done
  done
} | xargs -P "${JOBS:-3}" -L 1 sh -c "$PY sim/run_leanfc.py --trace-ekf \$0 \"\$@\" | tail -1"
