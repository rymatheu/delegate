#!/bin/sh
# The navigator runs of README.md "Results": each vehicle's default configuration (EKF, heading follows the
# path) flying its WAYPOINT square (params/VEHICLE.params) and its SPLINE square (+ params/VEHICLE-spline.params),
# deterministic and field seeds 0..9, plus the deterministic test missions of sim/missions/ (mixed leg kinds
# with a stop mark; WAYPOINT, SPLINE, SPLINE collinear). CSV + JSON in sim/out/flythrough/, tables by
# sim/nav_tables.py. Runs JOBS (default 4) simulations at a time.
cd "$(dirname "$0")/.." || exit 1
PY=${PY:-/Users/ryan/Research/cpp2lean/sim/.venv/bin/python}
OUT=sim/out/flythrough
mkdir -p $OUT
{
  for v in x500 cf2x; do
    for m in waypoint spline; do
      P="--params params/$v.params"
      [ $m = spline ] && P="$P --params params/$v-spline.params"
      echo "$P --noise none --out $OUT/$v-$m-det.csv"
      for s in 0 1 2 3 4 5 6 7 8 9; do
        echo "$P --noise field --seed $s --out $OUT/$v-$m-field-s$s.csv"
      done
    done
    for m in mixed collinear; do
      echo "--params params/$v.params --params sim/missions/$v-$m.params --noise none --out $OUT/$v-$m-det.csv"
    done
  done
} | xargs -P "${JOBS:-4}" -L 1 sh -c "$PY sim/run_leanfc.py \$0 \"\$@\" | tail -1"
