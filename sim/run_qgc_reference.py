#!/usr/bin/env python3
"""One QGroundControl session against the reference vehicle, observed through QGroundControl's log only.

    build/reference/venv/bin/python sim/run_qgc_reference.py --seconds 120 --out sim/out/lockstep-qgc

Starts sim/fly_reference.py --udp (the reference vehicle resting on the ground in gym-pybullet-drones, in
real time, SERIAL0 bridged to UDP 127.0.0.1:14550), then the installed, unmodified QGroundControl
(/Applications/QGroundControl.app) as a child process with console logging of its connection categories
(the procedure of leanfc's sim/mavlink/run_qgc.py), waits, terminates QGroundControl first and then the
harness, and summarizes from qgc.log whether QGroundControl connected, downloaded the parameters and
completed its initial connection sequence. QGroundControl's GUI and settings are not touched. The harness
records the session (inputs.txt, outputs.txt), so it can be replayed through the vehicle afterwards.

(Phase 5d) The translated whole vehicle in place of the reference:

    build/reference/venv/bin/python sim/run_qgc_reference.py --vehicle lean --seconds 120 --out sim/out/lockstep-qgc-lean

runs fly_reference.py --udp with `--bin sim/lean_vehicle.py` (lean/.lake/build/bin/vehicle_replay in live mode; its own
output, task and storage files in OUT/lean). The vehicle must keep up with real time (2.5 ms per 400 Hz step; README.md
"Phase 5d summary" has the measured step times); a slower step delays the following ones, it drops nothing.
`--gcs scripted` starts no QGroundControl: sim/udp_gcs_check.py (pymavlink, the same UDP port) connects for a few
seconds instead (heartbeat, PARAM_REQUEST_LIST, the first PARAM_VALUEs) and writes OUT/gcs_check.txt.
"""
import argparse
import os
import re
import signal
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
QGC = "/Applications/QGroundControl.app/Contents/MacOS/QGroundControl"
CATEGORIES = ",".join([
    "Vehicle.InitialConnectStateMachine", "Vehicle.RequestMessageCoordinator", "Vehicle.MavCommandQueue",
    "Vehicle.FTPManager", "Vehicle.StandardModes", "Vehicle.MultiVehicleManager",
    "FactSystem.ParameterManager", "PlanManager", "ComponentInformation",
    "FirmwarePlugin", "Comms.LinkInterface", "Comms.UDPLink",
    "Utilities.StateMachine", "Vehicle.Vehicle",
])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seconds", type=float, default=120)
    ap.add_argument("--out", default=str(HERE / "out" / "lockstep-qgc"))
    ap.add_argument("--storage", default=str(ROOT / "build" / "reference" / "storage-cf2x.bin"))
    ap.add_argument("--vehicle", choices=["reference", "lean"], default="reference",
                    help="reference: build/reference/copter_ref; lean: the translated vehicle through sim/lean_vehicle.py")
    ap.add_argument("--gcs", choices=["qgc", "scripted"], default="qgc",
                    help="qgc: the installed QGroundControl; scripted: sim/udp_gcs_check.py for --seconds (no QGroundControl)")
    a = ap.parse_args()
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    if a.gcs == "qgc" and subprocess.run(["pgrep", "-x", "QGroundControl"], capture_output=True).returncode == 0:
        sys.exit("a QGroundControl process is already running; not starting another")
    cmd = [sys.executable, str(HERE / "fly_reference.py"), "--udp", "--storage", a.storage,
           "--duration", str(a.seconds + 60), "--out", str(out / "harness")]
    env = dict(os.environ)
    if a.vehicle == "lean":
        cmd += ["--bin", str(HERE / "lean_vehicle.py")]
        env["LEAN_VEHICLE_OUT"] = str(out / "lean")
    harness = subprocess.Popen(cmd, cwd=ROOT, stdout=open(out / "harness.out", "w"), stderr=subprocess.STDOUT, env=env)
    time.sleep(4.0)
    if a.gcs == "scripted":
        qlog = open(out / "gcs_check.txt", "w")
        qgc = subprocess.Popen([sys.executable, str(HERE / "udp_gcs_check.py"), "--seconds", str(max(1.0, a.seconds - 1.5))],
                               stdout=qlog, stderr=subprocess.STDOUT, start_new_session=True)
    else:
        qlog = open(out / "qgc.log", "w")
        qgc = subprocess.Popen([QGC, f"--logging:{CATEGORIES}", "--log-output"], stdout=qlog,
                               stderr=subprocess.STDOUT, start_new_session=True)
    t0 = time.time()
    try:
        while time.time() - t0 < a.seconds:
            if qgc.poll() is not None or harness.poll() is not None:
                break
            time.sleep(0.5)
    finally:
        if qgc.poll() is None:
            qgc.terminate()
            try:
                qgc.wait(15)
            except subprocess.TimeoutExpired:
                qgc.kill()
                qgc.wait()
        print(f"{'QGroundControl' if a.gcs == 'qgc' else 'scripted ground station'} exit status {qgc.returncode}")
        if harness.poll() is None:
            harness.send_signal(signal.SIGINT)
            try:
                harness.wait(30)
            except subprocess.TimeoutExpired:
                harness.kill()
                harness.wait()
        print(f"harness exit status {harness.returncode}")
    if a.gcs == "scripted":
        print((out / "gcs_check.txt").read_text(), end="")
        return
    summarize(out)


def summarize(out: Path):
    log = (out / "qgc.log").read_text(errors="replace")
    lines = log.splitlines()

    def first(pat):
        r = re.compile(pat)
        return next((l for l in lines if r.search(l)), None)

    checks = [
        ("vehicle created (connected)", r"MultiVehicleManager.*(_vehicleHeartbeatInfo|Adding new vehicle|new vehicle)"),
        ("FTP parameter download attempted", r"FTPManager"),
        ("parameter download complete", r"(ParameterManager.*(_checkInitialLoadComplete|Initial load complete|parametersReady|All parameters))"),
        ("initial connect complete", r"InitialConnectStateMachine.*(complete|Complete|finished|_stateComplete)"),
        ("mission download", r"PlanManager.*(_handleMissionCount|count)"),
    ]
    res = []
    for name, pat in checks:
        l = first(pat)
        res.append(f"{name}: {'yes' if l else 'not seen'}" + (f"   [{l.strip()[:200]}]" if l else ""))
    (out / "qgc_summary.txt").write_text("\n".join(res) + "\n")
    print("\n".join(res))


if __name__ == "__main__":
    if len(sys.argv) == 3 and sys.argv[1] == "--summarize":
        summarize(Path(sys.argv[2]))
    else:
        main()
