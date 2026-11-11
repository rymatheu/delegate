#!/usr/bin/env python3
"""Run the installed, unmodified QGroundControl 5.1.5 against the gorge session (fly_gorge_qgc.sh: the
real controller, the camera payload with its two video streams, the tile server) and record both sides.

    sim/mavlink/.venv/bin/python sim/world/run_qgc_gorge.py [--seconds 90] [--out sim/world/out/qgc-real]

As sim/mavlink/run_qgc.py: QGroundControl is a child process with console logging of the connect,
camera and video categories; nothing is clicked; it is terminated at the end (killed if it does not
exit within 10 s) and `pgrep` must find no QGroundControl afterwards. Its settings file
(~/.config/qgroundcontrol.com/QGroundControl.ini) is only read, before and after, to report what
QGroundControl wrote by itself. Outputs in --out:

  session/          the session's outputs (flight.csv, vehicle.log, session.json, camera.json, camera.log, ...)
  qgc.log           QGroundControl's standard output and error
  vehicle.txt       the controller's frames decoded; summary.txt the counts per message
  settings.diff     the settings file after vs before
  milestones.txt    the log lines that show camera discovery, stream information, the video source and
                    the receivers (first occurrence of each)

`--home DIR` runs QGroundControl with HOME=DIR, so that it starts as on a fresh installation (its own
settings file under DIR/.config, its first-run prompt behind which the link still comes up) and the
user's settings are not involved at all.

`--formation PLAN` runs the formation session instead (fly_formation_qgc.sh: two vehicles, systems 1 and
2, a camera on each); the vehicle logs are vehicle1.log and vehicle2.log (decoded to vehicle1.txt,
vehicle2.txt, summary1.txt, summary2.txt), and every log line that shows a vehicle or a camera being
added or a receiver starting is in all-vehicles.txt.

It does not start when a QGroundControl process is already running (`pgrep`), or when one of the
session's default ports (UDP 14550, the video ports, the pose ports; TCP 8765) is taken.
"""
import argparse
import difflib
import os
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(ROOT / "sim/mavlink"))
import run_qgc  # noqa: E402

SETTINGS_REL = ".config/qgroundcontrol.com/QGroundControl.ini"
CATEGORIES = run_qgc.CATEGORIES + "," + ",".join([
    "Camera.QGCCameraManager", "Camera.VehicleCameraControl", "Camera.QGCVideoStreamInfo",
    "Video.VideoManager", "Video.GStreamer.GstVideoReceiver", "Video.GStreamer.GstSourceFactory",
    "Video.GStreamer.GStreamer", "Video.GStreamer.DecoderRanks", "Video.GStreamer.QgcQVideoSink",
    "Video.GStreamer.QGCQVideoSinkController", "Settings.VideoSettings",
])
MILESTONES = [
    "Heartbeat from", "Camera information received", "Creating MavlinkCameraControlInterface", "Adding real camera",
    "Received VIDEO_STREAM_INFORMATION", "Create stream handler", "All stream handlers done", "Configure stream",
    "New Video URI", "New Video Source", "Starting udp", "Started udp", "Streaming started", "Decoding started",
    "Decodebin3 selected codec", "streaming changed, active: yes", "decoding changed, active: yes", "resized",
    "Stream timeout", "Video decoder timeout", "Received VIDEO_STREAM_STATUS", "Received CAMERA_SETTINGS",
    "Received STORAGE_INFORMATION", "Received CAMERA_CAPTURE_STATUS", "Initial load complete",
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seconds", type=float, default=90)
    ap.add_argument("--out", default=str(HERE / "out" / "qgc-real"))
    ap.add_argument("--home", default=None, help="HOME for QGroundControl (a fresh settings directory)")
    ap.add_argument("--formation", choices=("abreast", "staggered"), default=None, help="the formation session instead")
    a = ap.parse_args()
    running = subprocess.run(["pgrep", "-lf", "QGroundControl"], capture_output=True, text=True).stdout.strip()
    if running:
        sys.exit(f"a QGroundControl process is running; not starting another:\n{running}")
    import socket
    busy = []
    for port, kind in [(14550, socket.SOCK_DGRAM), (8765, socket.SOCK_STREAM), (5600, socket.SOCK_DGRAM),
                       (5602, socket.SOCK_DGRAM), (5604, socket.SOCK_DGRAM), (5606, socket.SOCK_DGRAM),
                       (14601, socket.SOCK_DGRAM), (14603, socket.SOCK_DGRAM)]:
        so = socket.socket(socket.AF_INET, kind)
        try:
            so.bind(("0.0.0.0" if kind == socket.SOCK_DGRAM else "127.0.0.1", port))
        except OSError:
            busy.append(port)
        finally:
            so.close()
    if busy:
        sys.exit(f"ports in use (another session?): {busy}")
    logs = ["vehicle1.log", "vehicle2.log"] if a.formation else ["vehicle.log"]
    cams = ["camera1.out", "camera2.out"] if a.formation else ["camera.out"]
    home = Path(a.home).resolve() if a.home else Path.home()
    SETTINGS = home / SETTINGS_REL
    out = Path(a.out)
    sess = out / "session"
    sess.mkdir(parents=True, exist_ok=True)
    before = SETTINGS.read_text() if SETTINGS.exists() else ""
    (out / "settings-before.ini").write_text(before)
    env = dict(os.environ, OUT=str(sess), SECONDS_MAX=str(int(a.seconds + 180)), **({"PLAN": a.formation} if a.formation else {}))
    script = "fly_formation_qgc.sh" if a.formation else "fly_gorge_qgc.sh"
    launcher = subprocess.Popen(["sh", str(HERE / script)], cwd=ROOT, env=env, start_new_session=True,
                                stdout=open(out / "launcher.out", "w"), stderr=subprocess.STDOUT)
    t0 = time.time()
    while time.time() - t0 < 120:                         # the world is built and the camera has its workers
        up = [(sess / c).exists() and "camera component" in (sess / c).read_text() for c in cams]
        if all(up) and all((sess / lg).exists() for lg in logs):
            break
        time.sleep(0.5)
    print(f"session up after {time.time() - t0:.1f} s", flush=True)
    qlog = open(out / "qgc.log", "w")
    qenv = dict(os.environ, HOME=str(home)) if a.home else None
    qgc = subprocess.Popen([run_qgc.QGC, f"--logging:{CATEGORIES}", "--log-output"], stdout=qlog,
                           stderr=subprocess.STDOUT, start_new_session=True, env=qenv)
    t1 = time.time()
    try:
        while time.time() - t1 < a.seconds and qgc.poll() is None and launcher.poll() is None:
            time.sleep(0.5)
    finally:
        if qgc.poll() is None:
            qgc.terminate()
            try:
                qgc.wait(10)
            except subprocess.TimeoutExpired:
                qgc.kill()
                qgc.wait()
        print(f"QGroundControl exit status {qgc.returncode}")
        if launcher.poll() is None:
            os.killpg(launcher.pid, signal.SIGINT)           # the simulation writes its CSV, the trap stops the rest
            try:
                launcher.wait(120)
            except subprocess.TimeoutExpired:
                os.killpg(launcher.pid, signal.SIGKILL)
                launcher.wait()
        print(f"session exit status {launcher.returncode}")
    time.sleep(1.0)
    left = subprocess.run(["pgrep", "-lf", "QGroundControl"], capture_output=True, text=True).stdout.strip()
    print("pgrep QGroundControl:", left or "none")
    after = SETTINGS.read_text() if SETTINGS.exists() else ""
    (out / "settings-after.ini").write_text(after)
    diff = "".join(difflib.unified_diff(before.splitlines(True), after.splitlines(True), "before", "after"))
    (out / "settings.diff").write_text(diff)
    print("settings written by QGroundControl during the run:\n" + (diff or "(none)"))
    for k, lg in enumerate(logs, start=1):
        sfx = str(k) if a.formation else ""
        counts = run_qgc.decode_log(str(sess / lg), str(out / f"vehicle{sfx}.txt"))
        with open(out / f"summary{sfx}.txt", "w") as fo:
            for (d, name), n in sorted(counts.items()):
                fo.write(f"{d} {name} {n}\n")
    log = (out / "qgc.log").read_text(errors="replace").splitlines()
    seen, lines = set(), []
    for ln in log:
        for m in MILESTONES:
            if m in ln and m not in seen:
                seen.add(m)
                lines.append(ln)
    (out / "milestones.txt").write_text("\n".join(lines) + "\n")
    if a.formation:
        keys = ("Adding new vehicle link", "Connected to Vehicle", "Heartbeat from", "Camera information received",
                "New Video URI", "Starting", "Initial load complete", "resized", "decoding changed")
        (out / "all-vehicles.txt").write_text("\n".join(ln for ln in log if any(k in ln for k in keys)) + "\n")
    print("\n".join(lines))
    for f in ("session.json", "camera.json", "formation.json", "camera1.json", "camera2.json"):
        if (sess / f).exists():
            shutil.copy(sess / f, out / f)
    sj = sess / ("formation.json" if a.formation else "session.json")
    print(sj.read_text() if sj.exists() else f"no {sj.name}")


if __name__ == "__main__":
    main()
