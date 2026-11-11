#!/usr/bin/env python3
"""Run the installed, unmodified QGroundControl against the real leanfc controller in the real-time
simulation and record both sides.

    sim/mavlink/.venv/bin/python sim/mavlink/run_qgc.py --seconds 90 --out sim/mavlink/out/qgc-real1

Starts the simulator harness (`sim/run_leanfc.py --ground --mav --realtime 1`: the X500 resting on the
ground, disarmed, the controller `leanfc` with its MAVLink link sending to 127.0.0.1:14550, every frame
logged), then `/Applications/QGroundControl.app/Contents/MacOS/QGroundControl` as a child process with
console logging of the connect-related categories, waits, terminates both (QGroundControl first, then
the simulation; killed if they do not exit) and writes into --out:

  vehicle.log      every frame received and sent by leanfc (raw: simulated time, direction, ids, name, hex)
  vehicle.txt      the same decoded with pymavlink (one line per message, fields)
  qgc.log          QGroundControl's standard output and error
  summary.txt      per message type: count received from QGroundControl and sent to it
  flight.csv       the simulation (sim/run_leanfc.py's CSV with the vehicle columns)

Nothing in QGroundControl's bundle or settings is touched (it creates its own settings on first run).
"""

import argparse
import collections
import os
import signal
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(HERE, ".gen"))
import apm2  # noqa: E402

QGC = "/Applications/QGroundControl.app/Contents/MacOS/QGroundControl"
CATEGORIES = ",".join([
    "Vehicle.InitialConnectStateMachine", "Vehicle.RequestMessageCoordinator", "Vehicle.MavCommandQueue",
    "Vehicle.FTPManager", "Vehicle.StandardModes", "Vehicle.MultiVehicleManager",
    "FactSystem.ParameterManager", "PlanManager", "ComponentInformation",
    "FirmwarePlugin", "Comms.LinkInterface", "Comms.UDPLink",
    "Utilities.StateMachine", "Vehicle.Vehicle",
])


def decode_log(path, out):
    """Decode leanfc's frame log: each payload is re-framed as MAVLink 2 and parsed by pymavlink."""
    from pymavlink.generator.mavcrc import x25crc
    byname = {v.msgname: (k, v) for k, v in apm2.mavlink_map.items()}
    mav = apm2.MAVLink(None)
    mav.robust_parsing = True
    counts = collections.Counter()
    with open(path) as fh, open(out, "w") as fo:
        for line in fh:
            parts = line.split()
            if len(parts) < 6:
                continue
            t, d, s, c, name, hx = parts[:6]
            try:
                payload = bytes.fromhex(hx)
            except ValueError:  # the last line may be cut when the process is terminated
                continue
            counts[(d, name)] += 1
            txt = name
            if name in byname:
                mid, cls = byname[name]
                hdr = bytes([0xFD, len(payload), 0, 0, 0, int(s), int(c), mid & 0xFF, (mid >> 8) & 0xFF, mid >> 16])
                crc = x25crc(hdr[1:] + payload)
                crc.accumulate(bytes([cls.crc_extra]))
                msgs = mav.parse_buffer(hdr + payload + crc.crc.to_bytes(2, "little")) or []
                if msgs:
                    txt = str(msgs[0])
            fo.write(f"{float(t):9.4f} {d} {s}/{c} {txt}\n")
    return counts


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seconds", type=float, default=90)
    ap.add_argument("--out", default=os.path.join(HERE, "out", "qgc-run"))
    ap.add_argument("--vehicle", default="x500")
    ap.add_argument("--noise", default="field")
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    vlog = os.path.join(a.out, "vehicle.log")
    veh = subprocess.Popen([os.environ.get("LEANFC_PY") or os.path.join(ROOT, "sim", ".venv", "bin", "python"), os.path.join(ROOT, "sim", "run_leanfc.py"),
                            "--params", f"params/{a.vehicle}.params", "--params", "params/ground.params",
                            "--noise", a.noise, "--ground", "--mav", "--realtime", "1", "--trace-vehicle",
                            "--seconds", str(a.seconds + 60), "--mav-log", vlog,
                            "--out", os.path.join(a.out, "flight.csv")],
                           cwd=ROOT, stdout=open(os.path.join(a.out, "vehicle.err"), "w"), stderr=subprocess.STDOUT)
    time.sleep(3.0)
    qlog = open(os.path.join(a.out, "qgc.log"), "w")
    qgc = subprocess.Popen([QGC, f"--logging:{CATEGORIES}", "--log-output"], stdout=qlog,
                           stderr=subprocess.STDOUT, start_new_session=True)
    t0 = time.time()
    try:
        while time.time() - t0 < a.seconds:
            if qgc.poll() is not None or veh.poll() is not None:
                break
            time.sleep(0.5)
    finally:
        for p, name in ((qgc, "QGroundControl"), (veh, "simulation (run_leanfc.py + leanfc)")):
            if p.poll() is None:
                p.terminate()
                try:
                    p.wait(10)
                except subprocess.TimeoutExpired:
                    p.kill()
                    p.wait()
            print(f"{name} exit status {p.returncode}")
    counts = decode_log(vlog, os.path.join(a.out, "vehicle.txt"))
    with open(os.path.join(a.out, "summary.txt"), "w") as fo:
        for (d, name), n in sorted(counts.items()):
            fo.write(f"{d} {name} {n}\n")
    print(open(os.path.join(a.out, "summary.txt")).read())


if __name__ == "__main__":
    main()
