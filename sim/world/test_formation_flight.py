#!/usr/bin/env python3
"""A full scripted flight of the formation session: two vehicles, two plans, from the ground to touchdown,
with both camera payloads streaming.

    /Users/ryan/Research/cpp2lean/sim/.venv/bin/python sim/world/test_formation_flight.py --plan abreast|staggered
        [--seed 0] [--noise field] [--wind MEAN GUST] [--skew S] [--out DIR]

Starts `sh sim/world/fly_formation_qgc.sh` (real time) on its own ports, never the defaults (ground station
14593, tiles 8799, poses 14604 and 14606, video 5610/5612 for vehicle 1 and 5614/5616 for vehicle 2); it
checks that each is free before binding. It is the ground station on 127.0.0.1:14593 as QGroundControl
5.1.5 is on one UDP link (sim/mavlink/QGC.md, "The formation session"): system 255, component 190, one
GCS HEARTBEAT per second, and every frame it sends goes to every sender it has heard (both autopilots and
both cameras), so each must act only on what is addressed to it. Per vehicle, as QGroundControl does for
each Vehicle: the stream requests (REQUEST_DATA_STREAM to that system), the plan upload
(formation-PLAN-vK.plan to system K: home as item 0, then each item as MISSION_ITEM_INT), and Start
Mission from the ground (GUIDED, arm, MISSION_START). `--skew S`: vehicle 2's start sequence begins S s
after vehicle 1's (S < 0: before); with 0 both sequences run interleaved, as QGroundControl's
multi-vehicle Start runs one vehicle after the other.

Steps (PASS or FAIL): both vehicles ready to fly; both plans uploaded (MISSION_ACK ACCEPTED, each from
its own system); each Start Mission: AUTO; per vehicle the landed states ON_GROUND, TAKEOFF, IN_AIR,
LANDING, ON_GROUND and MISSION_CURRENT / MISSION_ITEM_REACHED 1..11 in order, landed and disarmed; no
contact between the vehicles; no contact of either with terrain or boulders in the air; the separation
(centre to centre, simulator truth, every tick) never below 1.0 m while either is in the air; each
vehicle's clearance in the air at least 0.8 m; video frames received equal frames sent on all four
streams (within the frames in flight at the end). Then the numbers: separation min / mean / max (both
in the air; on the route: both on spline items 2..10), its deviation from nominal, the start skew
measured from the two controllers' records, tracking, the rear vehicle's heading against its direction
of travel, touchdown, frames, real-time factor.
"""
import argparse
import json
import math
import os
import queue
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
sys.path.insert(0, str(HERE.parent))
import test_services as TS  # noqa: E402
import geo  # noqa: E402
from test_gorge_flight import count_frames, report  # noqa: E402
M = TS.M                                  # pymavlink's generated dialect (sim/mavlink/.gen/apm2.py)

PORTS = dict(GCS_PORT=14593, TILES_PORT=8799, POSE_PORT1=14604, POSE_PORT2=14606,
             RGB_PORT1=5610, THERMAL_PORT1=5612, RGB_PORT2=5614, THERMAL_PORT2=5616)


class Link:
    """One UDP ground-station socket shared by two vehicles: frames go to every sender heard (QGroundControl's
    UDPLink), received messages are queued per system (autopilot, component 1) and counted per component."""

    def __init__(self, port):
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.sock.bind(("127.0.0.1", port))
        self.sock.settimeout(0.2)
        self.peers = {}
        self.mav = M.MAVLink(self, srcSystem=255, srcComponent=190)
        self.mav.robust_parsing = True
        self.parsers = {}
        self.q = {1: queue.Queue(), 2: queue.Queue()}
        self.counts = {}
        self.lock = threading.Lock()
        self.running = True
        threading.Thread(target=self._rx, daemon=True).start()
        threading.Thread(target=self._hb, daemon=True).start()

    def write(self, buf):
        with self.lock:
            for addr in list(self.peers.values()):
                self.sock.sendto(buf, addr)

    def _rx(self):
        while self.running:
            try:
                data, addr = self.sock.recvfrom(65536)
            except socket.timeout:
                continue
            except OSError:
                return
            prs = self.parsers.setdefault(addr, M.MAVLink(None))
            prs.robust_parsing = True
            for m in prs.parse_buffer(data) or []:
                key = (m.get_srcSystem(), m.get_srcComponent())
                with self.lock:
                    self.peers[key] = addr
                self.counts[key] = self.counts.get(key, 0) + 1
                if key[1] == 1 and key[0] in self.q:
                    self.q[key[0]].put(m)

    def _hb(self):
        while self.running:
            if self.peers:
                self.mav.heartbeat_send(6, 8, 192, 0, 4)
            time.sleep(1.0)

    def wait(self, sysid, types, cond=lambda m: True, timeout=2.0):
        types = [types] if isinstance(types, str) else types
        t_end = time.time() + timeout
        while time.time() < t_end:
            try:
                m = self.q[sysid].get(timeout=0.05)
            except queue.Empty:
                continue
            if m.get_type() in types and cond(m):
                return m
        return None

    def command_long(self, sysid, cmd, *prm, timeout=1.5):
        prm = list(prm) + [0] * (7 - len(prm))
        self.mav.command_long_send(sysid, 1, cmd, 0, *prm)
        return self.wait(sysid, "COMMAND_ACK", lambda m: m.command == cmd, timeout)


class Vehicle:
    """What one QGroundControl Vehicle does with its system: stream requests, upload, Start Mission, monitor."""

    def __init__(self, link, sysid):
        self.l, self.id = link, sysid
        self.reached, self.currents, self.states = [], [], []
        self.t_arm = self.t_start = self.t_disarm = None
        self.ok_start = False

    def request_streams(self):
        for _ in range(5):
            for sid, hz in [(1, 2), (2, 2), (3, 2), (6, 3), (10, 10), (11, 10), (12, 3)]:
                self.l.mav.request_data_stream_send(self.id, 1, sid, hz, 1)
        self.l.command_long(self.id, 511, 242, 1000000)
        self.l.command_long(self.id, 511, 245, 1000000)

    def ready(self, timeout=120):
        return self.l.wait(self.id, "SYS_STATUS", lambda m: m.onboard_control_sensors_health & 0x10000000, timeout)

    def upload(self, plan):
        m = plan["mission"]
        home = m["plannedHomePosition"]
        items = [dict(command=16, frame=0, params=[0, 0, 0, 0, home[0], home[1], home[2]])] + m["items"]
        self.l.mav.mission_count_send(self.id, 1, len(items), 0)
        t_end = time.time() + 30
        while time.time() < t_end:
            r = self.l.wait(self.id, ["MISSION_REQUEST_INT", "MISSION_REQUEST", "MISSION_ACK"], timeout=3.0)
            if r is None:
                return None
            if r.get_type() == "MISSION_ACK":
                return r
            it = items[r.seq]
            q = [float("nan") if v is None else float(v) for v in it["params"]]
            self.l.mav.mission_item_int_send(self.id, 1, r.seq, it["frame"], it["command"], 1 if r.seq == 0 else 0, 1,
                                             q[0], q[1], q[2], q[3], int(round(q[4] * 1e7)), int(round(q[5] * 1e7)), q[6], 0)
        return None

    def set_mode(self, mode):
        for _ in range(3):
            self.l.command_long(self.id, 176, 1, mode)
            if self.l.wait(self.id, "HEARTBEAT", lambda m: m.custom_mode == mode, 1.3):
                return True
        return False

    def start_mission(self):
        """APMFirmwarePlugin::startMission from the ground: GUIDED, arm, MISSION_START; then AUTO."""
        ok1 = self.set_mode(4)
        ack = self.l.command_long(self.id, 400, 1)
        self.t_arm = time.time()
        ok2 = ack is not None and ack.result == 0
        ack = self.l.command_long(self.id, 300, 0, 0)
        self.t_start = time.time()
        hb = self.l.wait(self.id, "HEARTBEAT", lambda m: m.custom_mode == 3, 1.3)
        self.ok_start = ok1 and ok2 and ack is not None and ack.result == 0 and hb is not None

    def arm(self):
        """Multi-Vehicle panel Arm (GuidedActionsController actionMVArm): COMPONENT_ARM_DISARM, no mode change."""
        ack = self.l.command_long(self.id, 400, 1)
        self.t_arm = time.time()
        return ack is not None and ack.result == 0

    def mission_start(self):
        """Multi-Vehicle panel Start (actionMVStartMission) for an armed copter on the ground: MISSION_START."""
        ack = self.l.command_long(self.id, 300, 0, 0)
        self.t_start = time.time()
        hb = self.l.wait(self.id, "HEARTBEAT", lambda m: m.custom_mode == 3, 1.3)
        return ack is not None and ack.result == 0 and hb is not None

    def monitor(self, timeout=240):
        t_end = time.time() + timeout
        while time.time() < t_end:
            m = self.l.wait(self.id, ["MISSION_ITEM_REACHED", "MISSION_CURRENT", "HEARTBEAT", "EXTENDED_SYS_STATE"], timeout=1.0)
            if m is None:
                continue
            typ = m.get_type()
            if typ == "MISSION_ITEM_REACHED" and (not self.reached or self.reached[-1] != m.seq):
                self.reached.append(m.seq)
            elif typ == "MISSION_CURRENT" and (not self.currents or self.currents[-1] != m.seq):
                self.currents.append(m.seq)
            elif typ == "EXTENDED_SYS_STATE" and (not self.states or self.states[-1] != m.landed_state):
                self.states.append(m.landed_state)
            elif typ == "HEARTBEAT" and not m.base_mode & 0x80 and self.reached and self.t_disarm is None:
                self.t_disarm = time.time()
                t2 = time.time() + 3.0
                while time.time() < t2:
                    m = self.l.wait(self.id, ["MISSION_ITEM_REACHED", "EXTENDED_SYS_STATE"], timeout=0.5)
                    if m is not None and m.get_type() == "MISSION_ITEM_REACHED" and self.reached[-1] != m.seq:
                        self.reached.append(m.seq)
                    elif m is not None and m.get_type() == "EXTENDED_SYS_STATE" and self.states[-1] != m.landed_state:
                        self.states.append(m.landed_state)
                return


def ports_free():
    bad = []
    for k, port in PORTS.items():
        s = socket.socket(socket.AF_INET, socket.SOCK_STREAM if k == "TILES_PORT" else socket.SOCK_DGRAM)
        try:
            s.bind(("127.0.0.1", port))
        except OSError:
            bad.append(f"{k} {port}")
        finally:
            s.close()
    return bad


def analyze(out, plan_files, lines, vres, plan_name):
    """The numbers from the session's records (formation.csv every tick, vN.csv per vehicle)."""
    import formation as F
    f = np.genfromtxt(out / "formation.csv", delimiter=",", names=True)
    fj = json.loads((out / "formation.json").read_text())
    ds = [np.genfromtxt(out / f"v{v}.csv", delimiter=",", names=True) for v in (1, 2)]
    t = f["t"]
    n = min(len(t), len(ds[0]), len(ds[1]))
    t, ds = t[:n], [d[:n] for d in ds]
    f = f[:n]
    landed = [d["landed"].astype(int) for d in ds]
    item = [d["item"].astype(int) for d in ds]
    flying = [np.isin(x, (2, 3, 4)) for x in landed]
    air = [x == 2 for x in landed]
    either = flying[0] | flying[1]
    both = air[0] & air[1]
    route = both & (item[0] >= 2) & (item[0] <= 10) & (item[1] >= 2) & (item[1] <= 10)
    nominal = fj["nominal_distance"]
    dist = f["dist"]
    res = {}
    lines.append(report("no contact between the two vehicles (every tick)", (f["contact_vv"] > 0).sum() == 0,
                        f"closest distance between the collision bodies {f['gap'].min():.2f} m"))
    cw = [int(((f[f"contact_v{v + 1}"] > 0) & air[v]).sum()) for v in range(2)]
    lines.append(report("no contact with terrain or boulders in the air (either vehicle, every tick)", cw == [0, 0], f"ticks in contact: {cw}"))
    lines.append(report("separation (centre to centre) never below 1.0 m while either vehicle is in the air",
                        dist[either].min() >= 1.0, f"min {dist[either].min():.3f} m at t {t[either][np.argmin(dist[either])]:.2f} s"))
    clr = []
    for v in range(2):
        c = f[f"clear{v + 1}"][air[v]]
        c = c[np.isfinite(c)]
        clr.append(float(c.min()))
    lines.append(report("each vehicle's clearance to terrain and boulders in the air at least 0.8 m (every 4th tick)",
                        min(clr) >= 0.8, f"v1 {clr[0]:.2f} m, v2 {clr[1]:.2f} m"))
    dr = dist[route]
    dev = np.abs(dr - nominal)
    res["separation"] = dict(nominal=nominal, both_air=dict(min=float(dist[both].min()), mean=float(dist[both].mean()), max=float(dist[both].max())),
                             route=dict(min=float(dr.min()), mean=float(dr.mean()), max=float(dr.max()), dev_p95=float(np.percentile(dev, 95)),
                                        dev_max=float(dev.max()), seconds=float(route.sum() / 400)))
    lines.append(f"      separation, nominal {nominal:.3f} m: both in the air min {dist[both].min():.3f} / mean {dist[both].mean():.3f} / max "
                 f"{dist[both].max():.3f} m; on the route (both on items 2..10, {route.sum() / 400:.1f} s) min {dr.min():.3f} / mean "
                 f"{dr.mean():.3f} / max {dr.max():.3f} m, |d - nominal| p95 {np.percentile(dev, 95):.3f} m, max {dev.max():.3f} m")
    # start skew from the records: the tick each vehicle's route (item 2) starts, and its takeoff start (armed, item 1)
    k2 = [int(np.argmax(x >= 2)) for x in item]
    ka = [int(np.argmax(d["armed"] > 0)) for d in ds]
    kl = [int(np.argmax(x == 3)) for x in landed]
    res["skew"] = dict(arm_s=(ka[1] - ka[0]) / 400, takeoff_s=(kl[1] - kl[0]) / 400, route_start_s=(k2[1] - k2[0]) / 400,
                       takeoff_climb_s=[(k2[v] - kl[v]) / 400 for v in range(2)])
    lines.append(f"      start skew (vehicle 2 - vehicle 1, from the controllers' records): arm {res['skew']['arm_s']:+.3f} s, takeoff "
                 f"{res['skew']['takeoff_s']:+.3f} s, route start (item 2) {res['skew']['route_start_s']:+.3f} s; takeoff to route start "
                 f"v1 {res['skew']['takeoff_climb_s'][0]:.2f} s, v2 {res['skew']['takeoff_climb_s'][1]:.2f} s")
    origin = geo.Origin.from_params([ROOT / "params/x500.params", ROOT / "params/ground.params"])
    rec = []
    for v, (d, pf) in enumerate(zip(ds, plan_files)):
        plan = json.loads(pf.read_text())
        pos = np.column_stack([d["p_n"], d["p_e"], d["p_d"]])
        sp = np.column_stack([d["sp_n"], d["sp_e"], d["sp_d"]])
        trk = np.linalg.norm(pos - sp, axis=1)[flying[v]]
        it = plan["mission"]["items"][-1]
        ln, le = origin.ne(it["params"][4], it["params"][5])
        armed = d["armed"].astype(int)
        k_end = len(armed) - 1 - int(np.argmax(armed[::-1] > 0))
        k_land = int(np.argmax(landed[v] == 4))
        touch = np.nonzero((np.arange(n) >= k_land) & (f[f"contact_v{v + 1}"] > 0))[0]
        v_td = float(d["v_d"][touch[0]]) if len(touch) else float("nan")
        he = F.heading_error(d, fj["reverse"][v])
        hr = he[route & np.isfinite(he)]
        ok5 = route & np.isfinite(he) & (he < F.TURN_DONE_DEG)
        k5 = int(np.argmax(ok5)) if ok5.any() else n - 1
        ha = he[route & np.isfinite(he) & (np.arange(n) >= k5)]
        tilts = np.degrees(np.arccos(np.clip(1 - 2 * (d["q_x"] ** 2 + d["q_y"] ** 2), -1, 1)))
        mot = np.column_stack([d["m1"], d["m2"], d["m3"], d["m4"]])
        sat = int(np.sum(np.any((mot[flying[v]] >= 0.999) | (mot[flying[v]] <= 0.001), axis=1)))
        r = dict(track_max=float(trk.max()), track_rms=float(np.sqrt((trk ** 2).mean())), touchdown_v=v_td,
                 land_err=float(math.hypot(pos[k_end, 0] - ln, pos[k_end, 1] - le)), tilt_max=float(tilts[flying[v]].max()), sat=sat,
                 heading_route=dict(max=float(hr.max()), p95=float(np.percentile(hr, 95)), rms=float(np.sqrt((hr ** 2).mean()))),
                 heading_after_turn=dict(from_t=float(d["t"][k5]), from_north=float(d["p_n"][k5]), max=float(ha.max()),
                                         p95=float(np.percentile(ha, 95)), rms=float(np.sqrt((ha ** 2).mean()))),
                 clearance_air=clr[v])
        rec.append(r)
        what = "against" if fj["reverse"][v] else "along"
        lines.append(f"      vehicle {v + 1}: tracking max {r['track_max']:.3f} m, rms {r['track_rms']:.3f} m; heading {what} the direction of "
                     f"travel on the route: max {r['heading_route']['max']:.1f}, p95 {r['heading_route']['p95']:.1f}, rms "
                     f"{r['heading_route']['rms']:.1f} deg (within {F.TURN_DONE_DEG:g} deg from north {r['heading_after_turn']['from_north']:.1f} m; "
                     f"after that max {r['heading_after_turn']['max']:.1f}, p95 {r['heading_after_turn']['p95']:.1f}, rms "
                     f"{r['heading_after_turn']['rms']:.1f} deg); tilt max {r['tilt_max']:.1f} deg, saturated ticks {sat}; touchdown at "
                     f"{v_td:.2f} m/s down, {r['land_err']:.2f} m from its land item")
    res["vehicles"] = rec
    rt = fj.get("realtime", {})
    res["realtime"] = rt
    lines.append(f"      real time: {json.dumps(rt)}")
    frames_ok = True
    res["video"] = []
    for v in (1, 2):
        cj = out / f"camera{v}.json"
        if not cj.exists():
            continue
        for s in json.loads(cj.read_text()).get("streams", []):
            rx = vres.get(s["port"], {})
            ok = rx.get("frames", 0) >= s["frames_sent"] - 3 and s["frames_sent"] > 0
            frames_ok &= ok
            res["video"].append(dict(vehicle=v, stream=s["name"], sent=s["frames_sent"], fps=s["fps_achieved"], received=rx.get("frames"),
                                     rx_fps=rx.get("fps"), dropped=s["slots_dropped"], render_ms=s["render_ms_mean"]))
            lines.append(f"      video vehicle {v} stream {s['stream_id']} {s['name']} {s['resolution'][0]}x{s['resolution'][1]}: "
                         f"{s['frames_sent']} frames sent at {s['fps_achieved']:.2f} fps (target {s['fps_target']}), {s['slots_dropped']} "
                         f"slots dropped, render {s['render_ms_mean']:.1f} ms mean; received on {s['port']}: {rx.get('frames')} frames, "
                         f"{rx.get('fps', 0):.2f} fps")
    if res["video"]:
        lines.append(report("video: frames received equal frames sent on all four streams (within 3 in flight at the end)",
                            frames_ok and len(res["video"]) == 4))
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--plan", choices=("abreast", "staggered"), default="abreast")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--noise", default="field")
    ap.add_argument("--wind", nargs=2, default=None)
    ap.add_argument("--skew", type=float, default=0.0)
    ap.add_argument("--video", default="on")
    ap.add_argument("--start", choices=("single", "mv"), default="single",
                    help="single: each vehicle's Start Mission (GUIDED, arm, MISSION_START), vehicle 2's --skew s after "
                         "vehicle 1's; mv: the Multi-Vehicle panel's Arm (both), 2 s, then its Start (both, in order)")
    ap.add_argument("--rgb", default=None, help="RGB=WxH@FPS for both cameras (default: the launcher's)")
    ap.add_argument("--out", default=None)
    a = ap.parse_args()
    out = Path(a.out or HERE / "out" / "formation" / f"test-{a.plan}-s{a.seed}" / "session")
    out.mkdir(parents=True, exist_ok=True)
    bad = ports_free()
    if bad:
        sys.exit(f"ports in use: {', '.join(bad)}")
    stop, vres = threading.Event(), {}
    vports = [PORTS[k] for k in ("RGB_PORT1", "THERMAL_PORT1", "RGB_PORT2", "THERMAL_PORT2")]
    counters = [threading.Thread(target=count_frames, args=(q, stop, vres)) for q in vports] if a.video == "on" else []
    for th in counters:
        th.start()
    link = Link(PORTS["GCS_PORT"])
    env = dict(os.environ, OUT=str(out), PLAN=a.plan, NOISE=a.noise, SEED=str(a.seed), SECONDS_MAX="900", VIDEO=a.video,
               **{k: str(v) for k, v in PORTS.items()}, **({"WIND": " ".join(a.wind)} if a.wind else {}),
               **({"RGB": a.rgb} if a.rgb else {}))
    sess = subprocess.Popen(["sh", str(HERE / "fly_formation_qgc.sh")], cwd=ROOT, env=env, start_new_session=True,
                            stdout=open(out / "launcher.out", "w"), stderr=subprocess.STDOUT)
    lines = [f"formation test: plan {a.plan}, noise {a.noise}, seed {a.seed}, wind {a.wind}, skew {a.skew} s, start {a.start}"]
    vs = [Vehicle(link, 1), Vehicle(link, 2)]
    plan_files = [out / "plans" / f"formation-{a.plan}-v{v}.plan" for v in (1, 2)]
    try:
        hb = [link.wait(v.id, "HEARTBEAT", timeout=180) for v in vs]
        for v in vs:
            v.request_streams()
        rd = [v.ready() for v in vs]
        lines.append(report("both vehicles ready to fly (SYS_STATUS PREARM_CHECK from systems 1 and 2)",
                            all(h is not None for h in hb) and all(r is not None for r in rd)))
        for _ in range(120):
            outs = [(out / f"camera{v}.out") for v in (1, 2)]
            if a.video != "on" or all(o.exists() and "camera component" in o.read_text() for o in outs):
                break
            time.sleep(0.5)
        acks = [v.upload(json.loads(pf.read_text())) for v, pf in zip(vs, plan_files)]
        lines.append(report("both plans uploaded, each to its own system: MISSION_ACK ACCEPTED from systems 1 and 2",
                            all(x is not None and x.type == 0 and x.get_srcSystem() == v.id for x, v in zip(acks, vs)),
                            f"{[str(x) for x in acks]}"))
        if a.start == "mv":
            armed = [v.arm() for v in vs]
            time.sleep(2.0)
            started = [v.mission_start() for v in vs]
            for v, ok in zip(vs, started):
                v.ok_start = ok
            lines.append(report("Multi-Vehicle Arm (both), then Start (both): armed, AUTO", all(armed) and all(started),
                                f"MISSION_START sent to vehicle 2 {vs[1].t_start - vs[0].t_start:+.3f} s after vehicle 1"))
        else:
            delays = [max(0.0, -a.skew), max(0.0, a.skew)]
            t0 = time.time() + 0.5
            def go(v, d):
                time.sleep(max(0.0, t0 + d - time.time()))
                v.start_mission()
            ths = [threading.Thread(target=go, args=(v, d)) for v, d in zip(vs, delays)]
            for th in ths:
                th.start()
            for th in ths:
                th.join()
            lines.append(report("Start Mission from the ground on both (GUIDED, arm, MISSION_START): AUTO", all(v.ok_start for v in vs),
                                f"MISSION_START sent to vehicle 2 {vs[1].t_start - vs[0].t_start:+.3f} s after vehicle 1"))
        ths = [threading.Thread(target=v.monitor) for v in vs]
        for th in ths:
            th.start()
        for th in ths:
            th.join()
        for v in vs:
            lines.append(report(f"vehicle {v.id}: landed states ON_GROUND, TAKEOFF, IN_AIR, LANDING, ON_GROUND", v.states == [1, 3, 2, 4, 1], f"{v.states}"))
            lines.append(report(f"vehicle {v.id}: MISSION_CURRENT and MISSION_ITEM_REACHED 1..11 in order",
                                v.reached == list(range(1, 12)) and v.currents[:11] == list(range(1, 12)),
                                f"current {v.currents}, reached {v.reached}"))
            lines.append(report(f"vehicle {v.id}: landed and disarmed", v.t_disarm is not None and v.states[-1:] == [1],
                                f"arm to disarm {v.t_disarm - v.t_arm:.1f} s" if v.t_disarm else "not disarmed"))
        time.sleep(2.0)
        lines.append(f"      frames received per sender: { {f'{s}/{c}': n for (s, c), n in sorted(link.counts.items())} }")
    finally:
        link.running = False
        try:
            os.killpg(sess.pid, signal.SIGINT)
            sess.wait(120)
        except (subprocess.TimeoutExpired, ProcessLookupError):
            try:
                os.killpg(sess.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        stop.set()
        for th in counters:
            th.join(5)
    res = analyze(out, plan_files, lines, vres, a.plan)
    res["skew_requested_s"] = a.skew
    res["start_command_skew_s"] = (vs[1].t_start - vs[0].t_start) if vs[0].t_start and vs[1].t_start else None
    n_ok = sum(ok for _, ok in TS.RESULTS)
    lines.append(f"{n_ok}/{len(TS.RESULTS)} passed")
    res["passed"], res["checks"] = n_ok, len(TS.RESULTS)
    print("\n".join(lines))
    (out.parent / "report.txt").write_text("\n".join(lines) + "\n")
    (out.parent / "report.json").write_text(json.dumps(res, indent=1) + "\n")
    return 0 if n_ok == len(TS.RESULTS) else 1


if __name__ == "__main__":
    sys.exit(main())
