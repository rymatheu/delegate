#!/bin/sh
# Fly the real leanfc controller from QGroundControl: starts the PyBullet simulation in real time with
# the vehicle resting on the ground, disarmed, and the controller's MAVLink link sending to
# QGroundControl's UDP port 14550. Then open QGroundControl (it connects by itself; see
# sim/mavlink/QGC.md). Ctrl-C stops the simulation and writes sim/out/qgc/flight.csv.
#
#   sh sim/fly_qgc.sh                      # X500, field noise (GPS-like 10 Hz fixes)
#   VEHICLE=cf2x NOISE=none sh sim/fly_qgc.sh
#   sh sim/fly_qgc.sh --origin 46.5576 7.8350 2061    # any extra run_leanfc.py options
cd "$(dirname "$0")/.." || exit 1
VEHICLE=${VEHICLE:-x500}
NOISE=${NOISE:-field}
PY=${PY:-/Users/ryan/Research/cpp2lean/sim/.venv/bin/python}
LEAN_NUM_THREADS=1 lake build leanfc >/dev/null || { echo "lake build failed"; exit 1; }
mkdir -p sim/out/qgc
echo "leanfc: $VEHICLE on the ground at Pikes Peak (params/ground.params), noise $NOISE, real time."
echo "Open QGroundControl now; Ctrl-C here ends the simulation."
exec "$PY" sim/run_leanfc.py --params "params/$VEHICLE.params" --params params/ground.params --noise "$NOISE" \
  --ground --mav --realtime 1 --trace-vehicle --seconds 7200 \
  --mav-log sim/out/qgc/vehicle.log --out sim/out/qgc/flight.csv "$@"
