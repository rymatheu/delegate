#!/usr/bin/env python3
"""A full scripted flight of the gorge session from the ground, video on: the plan file uploaded and
started as QGroundControl 5.1.5 does it, the gorge flown, the landing and the disarm.

    /Users/ryan/Research/cpp2lean/sim/.venv/bin/python sim/world/test_gorge_flight.py [--seed 0] [--noise field] [--wind MEAN GUST]
        [--out sim/world/out/test-flight]

Starts `sh sim/world/fly_gorge_qgc.sh` (real time, its own ports: ground station 14592, tiles 8797,
poses 14602), and is the ground station on 127.0.0.1:14592 with test_services.py's Link (system 255,
component 190, GCS HEARTBEAT at 1 Hz, QGroundControl's command and mode helpers). It also listens on
the video ports 5600 and 5602 (`--video-ports RGB THERMAL` moves the camera's streams and the counting to other ports) and
counts the RTP frames (marker bits) that arrive.

Steps (PASS or FAIL): ready to fly (SYS_STATUS PREARM_CHECK); the plan file (the session's
gorge.plan) uploaded as QGroundControl's PlanManager sends it (home as item 0, then each SimpleItem as
MISSION_ITEM_INT, latitude and longitude * 1e7 rounded, frame and params as in the file),
MISSION_ACK ACCEPTED; Start Mission as GuidedActionsController does from the ground (GUIDED, arm,
MISSION_START); AUTO; liftoff; MISSION_CURRENT and MISSION_ITEM_REACHED in order through the 11
items; touchdown and disarm (landed state ON_GROUND, not armed); no contact with the gorge in the air.
Then, from the session's CSV and records: time from arm to disarm, tracking error (vehicle to the
controller's target, in the air), distance to the planned route (the takeoff column and the chords of
the spline waypoints), clearance to terrain and boulders in the air, the landing point against the
land item, the real-time factor, and the video frames sent and received per stream.
"""
import argparse
import json
import math
import os
import signal
import socket
import subprocess
import sys
import threading
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(ROOT / "sim/mavlink"))
sys.path.insert(0, str(HERE))
import test_services as TS  # noqa: E402
import geo  # noqa: E402



def report(name, ok, detail=""):
    TS.report(name, ok, detail)
    return f"{'PASS' if ok else 'FAIL'}  {name}{'  ' + detail if detail else ''}"


class CameraFilter:
    """The ground station's socket without the camera component's frames (component 100): the camera
    sends to the same port as the controller, as on QGroundControl's link, and test_services.Link takes
    the last sender as the vehicle."""

    def __init__(self, sock):
        self.sock, self.dropped = sock, 0

    def recvfrom(self, n):
        while True:
            data, addr = self.sock.recvfrom(n)
            if len(data) > 6 and data[0] == 0xFD and data[6] == 100:
                self.dropped += 1
                continue
            return data, addr

    def __getattr__(self, name):
        return getattr(self.sock, name)


def count_frames(port, stop, res):
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.bind(("127.0.0.1", port))
    sock.settimeout(0.5)
    n, first, last = 0, None, None
    while not stop.is_set():
        try:
            pkt = sock.recv(65536)
        except socket.timeout:
            continue
        if pkt[1] & 0x80:
            n += 1
            last = time.time()
            first = first or last
    res[port] = dict(frames=n, fps=(n - 1) / (last - first) if n > 1 else 0.0)


def upload(link, plan):
    """PlanManager: MISSION_COUNT, then each requested item as MISSION_ITEM_INT (item 0 is home)."""
    m = plan["mission"]
    home = m["plannedHomePosition"]
    items = [dict(command=16, frame=0, params=[0, 0, 0, 0, home[0], home[1], home[2]])] + m["items"]
    link.flush()
    link.mav.mission_count_send(1, 1, len(items), 0)
    s0, w0 = link.now(), time.time()
    while not link.expired(s0, w0, 15):
        r = link.wait(["MISSION_REQUEST_INT", "MISSION_REQUEST", "MISSION_ACK"], timeout=2.0)
        if r is None:
            return None
        if r.get_type() == "MISSION_ACK":
            return r
        it = items[r.seq]
        p = [float("nan") if v is None else float(v) for v in it["params"]]
        link.mav.mission_item_int_send(1, 1, r.seq, it["frame"], it["command"], 1 if r.seq == 0 else 0, 1,
                                       p[0], p[1], p[2], p[3], int(round(p[4] * 1e7)), int(round(p[5] * 1e7)), p[6], 0)
    return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--noise", default="field")
    ap.add_argument("--wind", nargs=2, default=None)
    ap.add_argument("--port", type=int, default=14592)
    ap.add_argument("--video-ports", type=int, nargs=2, default=[5600, 5602], metavar=("RGB", "THERMAL"),
                    help="the camera's stream ports, where this test counts the frames (default 5600 5602)")
    ap.add_argument("--out", default=str(HERE / "out" / "test-flight"))
    a = ap.parse_args()
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    stop, vres = threading.Event(), {}
    counters = [threading.Thread(target=count_frames, args=(p, stop, vres)) for p in a.video_ports]
    for t in counters:
        t.start()
    link = TS.Link(a.port, 1.0)
    link.sock = CameraFilter(link.sock)
    env = dict(os.environ, OUT=str(out), GCS_PORT=str(a.port), TILES_PORT="8797", POSE_PORT="14602",
               RGB_PORT=str(a.video_ports[0]), THERMAL_PORT=str(a.video_ports[1]),
               NOISE=a.noise, SEED=str(a.seed), SECONDS_MAX="900", **({"WIND": " ".join(a.wind)} if a.wind else {}))
    sess = subprocess.Popen(["sh", str(HERE / "fly_gorge_qgc.sh")], cwd=ROOT, env=env, start_new_session=True,
                            stdout=open(out / "launcher.out", "w"), stderr=subprocess.STDOUT)
    t_arm = t_disarm = None
    lines = []
    try:
        hb = link.wait("HEARTBEAT", timeout=120)               # connect as QGroundControl: its stream requests
        for _ in range(5):                                     # (APMFirmwarePlugin: 7 groups x 5) and intervals
            for sid, hz in [(1, 2), (2, 2), (3, 2), (6, 3), (10, 10), (11, 10), (12, 3)]:
                link.mav.request_data_stream_send(1, 1, sid, hz, 1)
        link.command_long(511, 242, 1000000)
        link.command_long(511, 245, 1000000)
        st = None
        w0 = time.time()
        while time.time() - w0 < 120 and st is None:
            st = link.wait("SYS_STATUS", lambda m: m.onboard_control_sensors_health & 0x10000000, timeout=1.0)
        lines.append(report("ready to fly (SYS_STATUS PREARM_CHECK) on the gorge floor", st is not None,
                            f"{time.time() - w0:.1f} s after the first HEARTBEAT (calibration, estimator settling)"))
        for _ in range(60):                                  # the camera is up (its workers load the world)
            if "camera component" in ((out / "camera.out").read_text() if (out / "camera.out").exists() else ""):
                break
            time.sleep(0.5)
        plan = json.loads((out / "gorge.plan").read_text())
        ack = upload(link, plan)
        lines.append(report(f"plan uploaded ({len(plan['mission']['items'])} items + home): MISSION_ACK ACCEPTED",
                            ack is not None and ack.type == 0, f"{ack}"))
        ok1, _ = link.set_mode_validated(4)
        ok2, _ = link.arm_validated(True)
        t_arm = link.now()
        ack = link.command_long(300, 0, 0)
        hb = link.wait("HEARTBEAT", lambda m: m.custom_mode == 3 and m.get_srcComponent() == 1, 1.3)
        lines.append(report("Start Mission from the ground (GUIDED, arm, MISSION_START): AUTO",
                            ok1 and ok2 and ack is not None and ack.result == 0 and hb is not None))
        reached, currents, states = [], [], []
        s0, w1 = link.now(), time.time()
        while not link.expired(s0, w1, 200):
            m = link.wait(["MISSION_ITEM_REACHED", "MISSION_CURRENT", "HEARTBEAT", "EXTENDED_SYS_STATE"], timeout=1.0)
            if m is None:
                continue
            typ = m.get_type()
            if typ == "MISSION_ITEM_REACHED" and (not reached or reached[-1] != m.seq):
                reached.append(m.seq)
            elif typ == "MISSION_CURRENT" and (not currents or currents[-1] != m.seq):
                currents.append(m.seq)
            elif typ == "EXTENDED_SYS_STATE" and (not states or states[-1] != m.landed_state):
                states.append(m.landed_state)
            elif typ == "HEARTBEAT" and m.get_srcComponent() == 1 and not m.base_mode & 0x80 and reached and t_disarm is None:
                t_disarm = link.now()
                s0, w1 = link.now(), time.time()                 # the events of the same ticks follow: 3 s more
                while not link.expired(s0, w1, 3.0):
                    m = link.wait(["MISSION_ITEM_REACHED", "EXTENDED_SYS_STATE"], timeout=0.5)
                    if m is not None and m.get_type() == "MISSION_ITEM_REACHED" and reached[-1] != m.seq:
                        reached.append(m.seq)
                    elif m is not None and m.get_type() == "EXTENDED_SYS_STATE" and states[-1] != m.landed_state:
                        states.append(m.landed_state)
                break
        n = len(plan["mission"]["items"])
        lines.append(report("landed states in order: ON_GROUND, TAKEOFF, IN_AIR, LANDING, ON_GROUND",
                            states == [1, 3, 2, 4, 1], f"{states}"))
        lines.append(report(f"MISSION_CURRENT 1..{n} and MISSION_ITEM_REACHED 1..{n} in order",
                            reached == list(range(1, n + 1)) and currents[:n] == list(range(1, n + 1)),
                            f"current {currents}, reached {reached}"))
        lines.append(report("landed and disarmed at the end (landed_state ON_GROUND, HEARTBEAT not armed)",
                            t_disarm is not None and states[-1:] == [1],
                            f"arm to disarm {t_disarm - t_arm:.1f} s" if t_disarm else "not disarmed"))
        link.sleep(3.0)
        lines.append(report("the camera component's frames arrived on the same ground-station port", link.sock.dropped > 0,
                            f"{link.sock.dropped} datagrams from component 100"))
    finally:
        link.running = False
        os.killpg(sess.pid, signal.SIGINT)
        try:
            sess.wait(120)
        except subprocess.TimeoutExpired:
            os.killpg(sess.pid, signal.SIGKILL)
        stop.set()
        for t in counters:
            t.join(5)

    # --- metrics from the session's records
    d = np.genfromtxt(out / "flight.csv", delimiter=",", names=True)
    sj = json.loads((out / "session.json").read_text())
    cj = json.loads((out / "camera.json").read_text()) if (out / "camera.json").exists() else {}
    t = d["t"]
    pos = np.column_stack([d["p_n"], d["p_e"], d["p_d"]])
    sp = np.column_stack([d["sp_n"], d["sp_e"], d["sp_d"]])
    landed, armed = d["landed"].astype(int), d["armed"].astype(int)
    air = landed == 2
    flying = np.isin(landed, (2, 3, 4))
    trk = np.linalg.norm(pos - sp, axis=1)
    origin = geo.Origin.from_params([ROOT / "params/x500.params", ROOT / "params/ground.params"])
    k_arm = int(np.argmax(armed > 0))
    home_d = pos[k_arm, 2]
    items = plan["mission"]["items"]
    route = []
    for it in items[:-1]:
        nn, ee = origin.ne(it["params"][4], it["params"][5])
        route.append((float(nn), float(ee), home_d - it["params"][6]))
    route = np.array([[route[0][0], route[0][1], home_d]] + route)
    def seg_dist(q):
        best = np.inf
        for p0, p1 in zip(route[:-1], route[1:]):
            v = p1 - p0
            s = np.clip((q - p0) @ v / (v @ v), 0, 1)
            best = min(best, np.linalg.norm(q - (p0 + s * v)))
        return best
    path_err = np.array([seg_dist(q) for q in pos[air][::10]])
    lat_l, lon_l = items[-1]["params"][4], items[-1]["params"][5]
    ln, le = origin.ne(lat_l, lon_l)
    k_end = len(t) - 1 - int(np.argmax(armed[::-1] > 0))
    land_err = math.hypot(pos[k_end, 0] - ln, pos[k_end, 1] - le)
    tilt = lambda k: math.degrees(math.acos(min(1.0, 1 - 2 * (d["q_x"][k] ** 2 + d["q_y"][k] ** 2))))
    lines.append(report("no contact with terrain or boulders in the air (session record, every 4th tick)",
                        sj.get("contacts_in_air") == 0,
                        f"clearance in the air min {sj.get('clearance_min_in_air_m', float('nan')):.2f} m over {sj.get('in_air_s', 0):.1f} s"))
    lines.append(f"      arm to disarm {t[k_end] - t[k_arm]:.1f} s (simulated); tracking error in flight max {trk[flying].max():.3f} m, "
                 f"rms {math.sqrt((trk[flying] ** 2).mean()):.3f} m; distance to the planned route in the air max "
                 f"{path_err.max():.3f} m, rms {math.sqrt((path_err ** 2).mean()):.3f} m")
    tilts = np.degrees(np.arccos(np.clip(1 - 2 * (d["q_x"] ** 2 + d["q_y"] ** 2), -1, 1)))
    motors = np.column_stack([d["m1"], d["m2"], d["m3"], d["m4"]])
    sat = int(np.sum(np.any((motors[flying] >= 0.999) | (motors[flying] <= 0.001), axis=1)))
    rec = np.genfromtxt(out / "session.csv", delimiter=",", names=True)
    k_land = int(np.argmax(landed == 4))
    touch = rec["t"][(rec["t"] >= t[k_land]) & (rec["contacts"] > 0)]
    v_td = float(np.interp(touch[0], t, d["v_d"])) if len(touch) else float("nan")
    gs = np.hypot(d["v_n"], d["v_e"])[air]
    lines.append(f"      in flight: tilt max {tilts[flying].max():.1f} deg, motors {motors[flying].min():.3f}..{motors[flying].max():.3f}, "
                 f"saturated ticks {sat}, ground speed max {gs.max():.2f} m/s; touchdown at {v_td:.2f} m/s down (first contact "
                 f"after LANDING began)")
    lines.append(f"      landing: {land_err:.2f} m from the land item (truth), tilt after disarm {tilt(k_end):.1f} deg, "
                 f"altitude above home at touchdown {home_d - pos[k_end, 2]:.2f} m (the floor rises up the gorge)")
    lines.append(f"      real time: {json.dumps({k: sj[k] for k in ('simulated_s', 'wall_s', 'rtf', 'rtf_1s_min', 'lag_max_s', 'seconds_below_0_98') if k in sj})}")
    for s in cj.get("streams", []):
        rx = vres.get(s["port"], {})
        lines.append(f"      video stream {s['stream_id']} {s['name']} {s['resolution'][0]}x{s['resolution'][1]}: "
                     f"{s['frames_sent']} frames sent at {s['fps_achieved']:.2f} fps (target {s['fps_target']}), "
                     f"{s['slots_dropped']} slots dropped, render {s['render_ms_mean']:.1f} ms mean; received on "
                     f"{s['port']}: {rx.get('frames')} frames, {rx.get('fps', 0):.2f} fps")
    n_ok = sum(ok for _, ok in TS.RESULTS)
    lines.append(f"{n_ok}/{len(TS.RESULTS)} passed")
    print("\n".join(lines[-8:]))
    (out / "report.txt").write_text("\n".join(lines) + "\n")
    return 0 if n_ok == len(TS.RESULTS) else 1


if __name__ == "__main__":
    sys.exit(main())
