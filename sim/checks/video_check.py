#!/usr/bin/env python3
"""Check the live video of a QGroundControl session without QGroundControl, for any flight controller.

    sim/.venv/bin/python sim/checks/video_check.py [single|abreast|staggered] --launcher PATH/fly_qgc.sh
        [--udp-port 14560] [--video-port 5700] [--pose-port 14701] [--seconds 8] [--out DIR] [--mission] [--no-video]
    sim/.venv/bin/python sim/checks/video_check.py [single|abreast|staggered] --attach [--udp-port ...] [--video-port ...]

Starts the stack's launcher (`LAUNCHER [abreast|staggered] --udp-port P --video-port V --pose-port X --out DIR`, the
options every stack's fly_qgc.sh takes; sim/README.md) on test ports (MAVLink to 127.0.0.1:--udp-port, video from
--video-port, camera poses from --pose-port; the defaults stay clear of QGroundControl's 14550 and 5600), or with
--attach checks a session that is already running on those ports (then the end-of-session checks are skipped), and
plays the ground station on the MAVLink port with pymavlink:
(a) each camera's HEARTBEAT (component 100 of the vehicle's system id, type CAMERA), CAMERA_INFORMATION and
    VIDEO_STREAM_INFORMATION (REQUEST_MESSAGE, acknowledged), with the stream URIs, sizes and rates the session
    announces (sim/fly_qgc.sh);
(b) every video port receives RTP that decodes (this script again, in .venv-video with PyAV: its own RFC 6184
    depacketizer and FFmpeg's H.264 decoder, for --seconds) to frames of the announced size at roughly the announced
    rate (at least 70 % of it); with two vehicles also the switch of the shared RGB port: VIDEO_STOP_STREAMING to
    vehicle 1's camera and VIDEO_START_STREAMING to vehicle 2's, after which the port carries vehicle 2's stream only
    (the cameras' RTP packet counts, camera1.json and camera2.json);
(c) the frames are not blank (luma standard deviation above 5 in every tenth decoded frame), and one decoded frame of
    each stream is saved as PNG in --out (rgb-v1.png, thermal-v1.png, ...).
--mission then runs sim/checks/qgc_session_check.py (with the plans of sim/plans/) on the same session (parameter download, mission upload, arm, takeoff,
AUTO past the first spline waypoint) with the video running. Last, the session is ended with SIGTERM and every
process it started (harness, vehicles, cameras, render workers) must be gone; the harness's real-time line is
printed. --no-video runs the session without cameras (for comparing the real-time margin; (a) to (c) are skipped).
Prints `RESULT PASS` (exit 0) or `RESULT FAIL` (exit 1); report.txt in --out.
"""
import argparse
import json
import os
import re
import signal
import socket
import struct
import subprocess
import sys
import threading
import time
import zlib
from pathlib import Path

SIM_DIR = Path(__file__).resolve().parent.parent
RGB = dict(size=(640, 480), fps=10.0)          # the cameras' streams as sim/cameras.sh starts them
THERMAL = dict(size=(640, 512), fps=8.7)


# --- decoder (runs in .venv-video: av, numpy) --------------------------------------------------------

def write_png(path, rgb):
    """Minimal PNG writer (8-bit RGB), so the decoder needs no imaging library."""
    h, w, _ = rgb.shape
    raw = b"".join(b"\0" + rgb[i].tobytes() for i in range(h))

    def chunk(t, d):
        return struct.pack(">I", len(d)) + t + d + struct.pack(">I", zlib.crc32(t + d) & 0xFFFFFFFF)
    Path(path).write_bytes(b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", w, h, 8, 2, 0, 0, 0))
                           + chunk(b"IDAT", zlib.compress(raw, 6)) + chunk(b"IEND", b""))


def decode(port, seconds, png):
    """Receive RTP/H.264 on 127.0.0.1:port for `seconds`, decode from the first keyframe; print a JSON summary."""
    import av
    import numpy as np
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 8 << 20)
    sock.bind(("127.0.0.1", port))
    sock.settimeout(0.2)
    dec = av.CodecContext.create("h264", "r")
    au, fu, started = [], None, False
    r = dict(port=port, packets=0, lost=0, access_units=0, frames=0, errors=0, size=None, times=[], std=[], mean=[],
             png=None, ssrc=set())
    last_seq, saved, t_end = None, None, time.time() + seconds
    while time.time() < t_end:
        try:
            pkt = sock.recv(65536)
        except socket.timeout:
            continue
        if len(pkt) < 13 or pkt[0] >> 6 != 2:
            continue
        r["packets"] += 1
        cc, x = pkt[0] & 0x0F, pkt[0] & 0x10
        marker, seq = pkt[1] & 0x80, struct.unpack("!H", pkt[2:4])[0]
        r["ssrc"].add(struct.unpack("!I", pkt[8:12])[0])
        if last_seq is not None and seq != (last_seq + 1) & 0xFFFF:
            r["lost"] += (seq - last_seq - 1) & 0xFFFF
        last_seq = seq
        off = 12 + 4 * cc
        if x:
            off += 4 + 4 * struct.unpack("!H", pkt[off + 2:off + 4])[0]
        pl = pkt[off:]
        typ = pl[0] & 0x1F
        if typ < 24:
            au.append(pl)
        elif typ == 24:                                 # STAP-A
            o = 1
            while o + 2 <= len(pl):
                n = struct.unpack("!H", pl[o:o + 2])[0]
                au.append(pl[o + 2:o + 2 + n])
                o += 2 + n
        elif typ == 28:                                 # FU-A
            if pl[1] & 0x80:
                fu = bytearray([(pl[0] & 0xE0) | (pl[1] & 0x1F)])
            if fu is not None:
                fu += pl[2:]
                if pl[1] & 0x40:
                    au.append(bytes(fu))
                    fu = None
        if not marker:
            continue
        r["access_units"] += 1
        started = started or any(n[0] & 0x1F == 5 for n in au)
        data = b"".join(b"\x00\x00\x00\x01" + n for n in au)
        au = []
        if not started:
            continue
        try:
            frames = dec.decode(av.Packet(data))
        except av.error.InvalidDataError:
            r["errors"] += 1
            continue
        for f in frames:
            r["frames"] += 1
            r["times"].append(time.time())
            r["size"] = [f.width, f.height]
            if r["frames"] % 10 == 1:
                img = f.to_ndarray(format="rgb24")
                y = img @ np.array([0.299, 0.587, 0.114])
                r["std"].append(float(y.std()))
                r["mean"].append(float(y.mean()))
                saved = img
    sock.close()
    ts = r.pop("times")
    r["span_s"] = ts[-1] - ts[0] if len(ts) > 1 else 0.0
    r["fps"] = (len(ts) - 1) / r["span_s"] if r["span_s"] > 0 else 0.0
    r["ssrc"] = sorted(r["ssrc"])
    if saved is not None:
        write_png(png, saved)
        r["png"] = str(png)
    print(json.dumps(r), flush=True)


# --- the check (runs in .venv: pymavlink) --------------------------------------------------------------

RESULTS = []


def report(lines, name, ok, detail=""):
    RESULTS.append(bool(ok))
    lines.append(f"{'PASS' if ok else 'FAIL'}  {name}" + (f"  ({detail})" if detail else ""))
    print(lines[-1], flush=True)


class Gcs:
    """A ground station on the session's MAVLink port: every message by (system, component), and each source's address."""

    def __init__(self, port):
        from pymavlink.dialects.v20 import ardupilotmega as m
        self.m = m
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.sock.bind(("127.0.0.1", port))
        self.sock.settimeout(0.1)
        self.mav = m.MAVLink(None, srcSystem=255, srcComponent=190)
        self.parsers, self.addr, self.msgs, self.lock, self.running = {}, {}, [], threading.Lock(), True
        threading.Thread(target=self._rx, daemon=True).start()

    def _rx(self):
        while self.running:
            try:
                data, addr = self.sock.recvfrom(65536)
            except socket.timeout:
                continue
            except OSError:
                return
            p = self.parsers.setdefault(addr, self.m.MAVLink(None))
            p.robust_parsing = True
            for msg in p.parse_buffer(data) or []:
                if msg.get_type() == "BAD_DATA":
                    continue
                key = (msg.get_srcSystem(), msg.get_srcComponent())
                with self.lock:
                    self.addr[key] = addr
                    self.msgs.append((time.time(), key, msg))

    def wait(self, key, typ, cond=lambda x: True, after=0.0, timeout=2.0, n=1):
        t_end = time.time() + timeout
        while time.time() < t_end:
            with self.lock:
                got = [x for t, k, x in self.msgs if t >= after and k == key and x.get_type() == typ and cond(x)]
            if len(got) >= n:
                return got
            time.sleep(0.02)
        return got

    def command(self, key, cmd, *p):
        p = list(p) + [0] * (7 - len(p))
        t = time.time()
        self.sock.sendto(self.m.MAVLink_command_long_message(key[0], key[1], cmd, 0, *p).pack(self.mav), self.addr[key])
        return t

    def request(self, key, cmd, *p):
        """COMMAND_LONG to `key`; its COMMAND_ACK result (None: none within 1.2 s, QGroundControl's ack timeout)."""
        t = self.command(key, cmd, *p)
        a = self.wait(key, "COMMAND_ACK", lambda x: x.command == cmd, after=t, timeout=1.2)
        return t, (a[0].result if a else None)

    def close(self):
        self.running = False
        self.sock.close()


def descendants(pid):
    out = subprocess.run(["ps", "-A", "-o", "pid=,ppid=,command="], capture_output=True, text=True).stdout
    procs = {}
    for line in out.splitlines():
        a = line.split(None, 2)
        if len(a) >= 2:
            procs[int(a[0])] = (int(a[1]), a[2] if len(a) > 2 else "")
    found, frontier = {}, [pid]
    while frontier:
        q = frontier.pop()
        for c, (pp, cmd) in procs.items():
            if pp == q and c not in found:
                found[c] = cmd
                frontier.append(c)
    return found


def alive(pids):
    if not pids:
        return {}
    out = subprocess.run(["ps", "-o", "pid=,command=", "-p", ",".join(map(str, pids))], capture_output=True, text=True).stdout
    return {int(l.split(None, 1)[0]): l.split(None, 1)[1] for l in out.splitlines() if l.strip()}


def decode_ports(ports, seconds, out, vpy):
    """{tag: decoder summary} for {tag: port}, all received at once."""
    procs = {tag: subprocess.Popen([vpy, "-B", __file__, "--decode", str(port), str(seconds), str(out / f"{tag}.png")],
                                   stdout=subprocess.PIPE, text=True) for tag, port in ports.items()}
    res = {}
    for tag, p in procs.items():
        o, _ = p.communicate(timeout=seconds + 30)
        try:
            res[tag] = json.loads(o.strip().splitlines()[-1])
        except (ValueError, IndexError):
            res[tag] = None
    return res


def check_stream(lines, tag, r, spec):
    if r is None:
        return report(lines, f"{tag}: decoder ran", False)
    ok_rate = r["fps"] >= 0.7 * spec["fps"] and r["fps"] <= 1.3 * spec["fps"]
    report(lines, f"{tag}: RTP on UDP {r['port']} decodes to {spec['size'][0]}x{spec['size'][1]} frames at about "
           f"{spec['fps']:g} fps", r["frames"] > 0 and r["size"] == list(spec["size"]) and ok_rate and r["errors"] == 0,
           f"{r['packets']} packets, {r['lost']} lost, {r['frames']} frames in {r['span_s']:.1f} s = {r['fps']:.2f} fps, "
           f"size {r['size']}, decode errors {r['errors']}")
    report(lines, f"{tag}: frames not blank (luma std > 5 in every tenth frame)", r["std"] and min(r["std"]) > 5,
           f"luma std min {min(r['std'] or [0]):.1f} max {max(r['std'] or [0]):.1f}, mean {sum(r['mean']) / max(1, len(r['mean'])):.1f}; "
           f"saved {r['png']}")


def camera_checks(g, lines, sid, uris, gated):
    key = (sid, 100)
    hb = g.wait(key, "HEARTBEAT", timeout=120)
    report(lines, f"camera {sid}/100: HEARTBEAT type CAMERA (30), autopilot INVALID (8), state ACTIVE",
           hb and hb[0].type == 30 and hb[0].autopilot == 8 and hb[0].system_status == 4,
           f"from {g.addr.get(key)}" if hb else "none in 120 s")
    if not hb:
        return
    t, res = g.request(key, 512, 259)
    ci = g.wait(key, "CAMERA_INFORMATION", after=t, timeout=1.0)
    report(lines, f"camera {sid}/100: REQUEST_MESSAGE CAMERA_INFORMATION: ACK ACCEPTED, then the message (HAS_VIDEO_STREAM)",
           res == 0 and ci and ci[0].flags & 256,
           f"ack {res}; " + (f"vendor {bytes(ci[0].vendor_name).rstrip(bytes(1)).decode()!r}, model "
                             f"{bytes(ci[0].model_name).rstrip(bytes(1)).decode()!r}, {ci[0].resolution_h}x{ci[0].resolution_v}, "
                             f"flags {ci[0].flags}" if ci else "no message"))
    t, res = g.request(key, 512, 269, 0)
    vs = g.wait(key, "VIDEO_STREAM_INFORMATION", after=t, timeout=1.0, n=2)
    vs = sorted(vs, key=lambda x: x.stream_id)
    ok = res == 0 and len(vs) == 2 and all(v.count == 2 for v in vs)
    detail = [f"ack {res}, {len(vs)} messages"]
    for v, (want_uri, spec, thermal) in zip(vs, uris):
        good = (v.uri == want_uri and v.type == 1 and v.encoding == 1 and (v.resolution_h, v.resolution_v) == spec["size"]
                and abs(v.framerate - spec["fps"]) < 0.01 and bool(v.flags & 2) == thermal and v.flags & 1)
        ok = ok and good
        detail.append(f"stream {v.stream_id} {v.name!r} uri {v.uri} {v.resolution_h}x{v.resolution_v} {v.framerate:g} fps "
                      f"flags {v.flags} type {v.type} encoding {v.encoding}")
    report(lines, f"camera {sid}/100: VIDEO_STREAM_INFORMATION (all streams): RTPUDP, H264, uris {[u for u, _, _ in uris]}",
           ok, "; ".join(detail))


def stream_packets(path):
    try:
        return json.loads(Path(path).read_text())["streams"][0]["rtp_packets"]
    except (OSError, ValueError, KeyError, IndexError):
        return None


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--decode":
        return decode(int(sys.argv[2]), float(sys.argv[3]), sys.argv[4])
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("plan", nargs="?", choices=("single", "one", "abreast", "staggered"), default="single")
    ap.add_argument("--launcher", default=None, help="the stack's fly_qgc.sh (started with the test ports)")
    ap.add_argument("--attach", action="store_true", help="check a session already running on the ports")
    ap.add_argument("--udp-port", type=int, default=14560)
    ap.add_argument("--video-port", type=int, default=5700)
    ap.add_argument("--pose-port", type=int, default=14701)
    ap.add_argument("--seconds", type=float, default=8.0, help="decoding time per stream")
    ap.add_argument("--out", default=None, help="default build/video-check/PLAN (PLAN-novideo with --no-video)")
    ap.add_argument("--mission", action="store_true", help="also run sim/checks/qgc_session_check.py with the video running")
    ap.add_argument("--no-video", action="store_true")
    a = ap.parse_args()
    if a.plan == "one":
        a.plan = "single"
    if bool(a.launcher) == a.attach:
        ap.error("give exactly one of --launcher PATH and --attach")
    out = Path(a.out or SIM_DIR / "build" / "video-check" / (a.plan + ("-novideo" if a.no_video else ""))).resolve()
    out.mkdir(parents=True, exist_ok=True)
    vpy = os.environ.get("GORGE_VIDEO_PY", str(SIM_DIR / ".venv-video" / "bin" / "python"))
    two = a.plan != "single"
    V = a.video_port
    lines = [f"video_check {a.plan}: MAVLink {a.udp_port}, video from {V}, poses from {a.pose_port}, "
             f"{'no video' if a.no_video else 'video'}"]
    sess = None
    if a.launcher:
        launcher = Path(a.launcher).resolve()
        cmd = [str(launcher)] + ([a.plan] if two else []) + [
            "--udp-port", str(a.udp_port), "--video-port", str(V), "--pose-port", str(a.pose_port), "--out", str(out / "session")]
        if a.no_video:
            cmd.append("--no-video")
        slog = open(out / "session.log", "w")
        sess = subprocess.Popen(cmd, stdout=slog, stderr=subprocess.STDOUT, start_new_session=True, cwd=launcher.parent)
        print(f"session pid {sess.pid}: {' '.join(cmd)}", flush=True)
    g = Gcs(a.udp_port)
    try:
        sids = [1, 2] if two else [1]
        for sid in sids:
            hb = g.wait((sid, 1), "HEARTBEAT", timeout=120)
            report(lines, f"vehicle {sid}/1: HEARTBEAT on UDP {a.udp_port}", hb, f"from {g.addr.get((sid, 1))}" if hb else "none")
        if not a.no_video:
            cams = {1: [(f"udp://127.0.0.1:{V}", RGB, False), (f"udp://127.0.0.1:{V + 2}", THERMAL, True)]}
            if two:
                cams[2] = [(f"udp://127.0.0.1:{V}", RGB, False), (f"udp://127.0.0.1:{V + 6}", THERMAL, True)]
            for sid in sids:
                camera_checks(g, lines, sid, cams[sid], two)
            ports = {"rgb-v1": V, "thermal-v1": V + 2}
            if two:
                ports["thermal-v2"] = V + 6
            res = decode_ports(ports, a.seconds, out, vpy)
            for tag, port in ports.items():
                check_stream(lines, tag, res[tag], RGB if tag.startswith("rgb") else THERMAL)
            if two:
                # QGroundControl's switch of the active vehicle: stop vehicle 1's RGB stream, start vehicle 2's
                _, r1 = g.request((1, 100), 2503, 1)
                _, r2 = g.request((2, 100), 2502, 1)
                report(lines, "VIDEO_STOP_STREAMING to camera 1/100 and VIDEO_START_STREAMING to camera 2/100: ACCEPTED",
                       r1 == 0 and r2 == 0, f"acks {r1}, {r2}")
                time.sleep(6.0)                         # the cameras' statistics are rewritten every 5 s
                c1, c2 = stream_packets(out / "session/camera1.json"), stream_packets(out / "session/camera2.json")
                res = decode_ports({"rgb-v2": V}, a.seconds, out, vpy)
                check_stream(lines, "rgb-v2", res["rgb-v2"], RGB)
                time.sleep(max(0.0, 6.0 - a.seconds))
                d1 = (stream_packets(out / "session/camera1.json") or 0) - (c1 or 0)
                d2 = (stream_packets(out / "session/camera2.json") or 0) - (c2 or 0)
                report(lines, f"after the switch only camera 2's RGB stream is sent on UDP {V}", c1 is not None and d1 == 0 and d2 > 0,
                       f"RTP packets sent meanwhile: camera 1 {d1}, camera 2 {d2}")
                g.request((2, 100), 2503, 1)
                g.request((1, 100), 2502, 1)
        g.close()
        if a.mission:
            plans = ([f"1={SIM_DIR}/plans/formation-{a.plan}-v1.plan", f"2={SIM_DIR}/plans/formation-{a.plan}-v2.plan"] if two
                     else [f"1={SIM_DIR}/plans/gorge.plan"])
            mp = subprocess.run([sys.executable, str(SIM_DIR / "checks" / "qgc_session_check.py"), str(a.udp_port), "400", *plans],
                                capture_output=True, text=True, cwd=SIM_DIR)
            (out / "mission.log").write_text(mp.stdout + mp.stderr)
            last = (mp.stdout.strip().splitlines() or [""])[-1]
            report(lines, "sim/checks/qgc_session_check.py on the session" + ("" if a.no_video else " with the video running"),
                   mp.returncode == 0 and "RESULT PASS" in last, last.strip() + f"; log {out / 'mission.log'}")
    finally:
        g.close()
        if sess is not None:
            tree = descendants(sess.pid)
            tree[sess.pid] = "fly_qgc.sh"
            # the cameras run detached (sim/cameras.sh returns at once): find them by the session folder in their
            # command line, with their render workers
            ps = subprocess.run(["ps", "-A", "-o", "pid=,command="], capture_output=True, text=True).stdout
            for line in ps.splitlines():
                pid_s, _, cmd = line.strip().partition(" ")
                if str(out / "session") in cmd and int(pid_s) not in tree:
                    tree[int(pid_s)] = cmd
                    tree.update(descendants(int(pid_s)))
            os.kill(sess.pid, signal.SIGTERM)
            try:
                sess.wait(90)
            except subprocess.TimeoutExpired:
                pass
            time.sleep(2.0)
            left = {p: c for p, c in alive(list(tree)).items() if p in tree}
            report(lines, f"SIGTERM to the session: all {len(tree)} of its processes gone (harness, vehicles, cameras, render "
                   f"workers)", not left, f"exit status {sess.poll()}" + (f"; left: {left}" if left else ""))
            for p in left:
                if p != sess.pid:
                    try:
                        os.kill(p, signal.SIGKILL)       # our own strays only
                    except ProcessLookupError:
                        pass
    for name in ("summary.txt", "log.txt"):
        f = out / "session" / name
        if f.exists():
            rt = [l for l in f.read_text().splitlines() if l.startswith("real time:")]
            if rt:
                m = re.search(r"behind wall time at the end by (-?[\d.]+) s\).*?late (\d+) of (\d+).*?mean ([\d.]+) ms, p50 ([\d.]+), "
                              r"p99 ([\d.]+), max ([\d.]+)", rt[-1])
                lines.append("real-time line: " + rt[-1])
                if m:
                    lines.append(f"margin: step work mean {m.group(4)} ms of 2.5 ms ({float(m.group(4)) / 2.5 * 100:.0f} %), "
                                 f"p99 {m.group(6)} ms; lag at the end {float(m.group(1)) * 1000:.0f} ms; late steps "
                                 f"{m.group(2)} of {m.group(3)}")
                print("\n".join(lines[-2:]), flush=True)
                break
    ok = all(RESULTS)
    lines.append("RESULT " + ("PASS" if ok else "FAIL") + f" ({sum(RESULTS)}/{len(RESULTS)})")
    print(lines[-1], flush=True)
    (out / "report.txt").write_text("\n".join(lines) + "\n")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
