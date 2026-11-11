"""Tests of the simulated camera payload (camera_component.py): QGroundControl 5.1.5's camera discovery
replayed by a scripted ground station, and both RTP streams received by an independent decoder.

    sim/world/.venv-video/bin/python sim/world/test_camera.py [--seconds 20] [--out sim/world/out/test-camera]

Starts camera_component.py (its default stream settings) with its MAVLink link to this script on
127.0.0.1:GCS_PORT and its pose port fed by this script: a synthetic fly-through of the gorge route
(gorge.plan's waypoints, 2 m/s, nose along the route, level) at 100 Hz, each pose stamped with the
wall clock as gorge_session.py stamps it.

Protocol (oracle: pymavlink's dialect generated from the MAVLink XML, sim/mavlink/.gen/apm2.py; each
step is QGroundControl's request with its timeouts: COMMAND_ACK within MavCommandQueue's 1200 ms, the
requested message within RequestMessageCoordinator's 1000 ms; sim/world/QGC-CAMERA.md):
heartbeat; CAMERA_INFORMATION (REQUEST_MESSAGE and the legacy command QGCCameraManager alternates
with); CAMERA_SETTINGS and the CAMERA_FOV_STATUS request that follows it (UNSUPPORTED); all
VIDEO_STREAM_INFORMATION (param2 0) and one by id (legacy); VIDEO_STREAM_STATUS; CAMERA_CAPTURE_STATUS;
STORAGE_INFORMATION; VIDEO_START/STOP_STREAMING; an unknown command; a command for the autopilot
(component 1), which the camera must ignore.

Stream: FFmpeg's own RTP depacketizer and H.264 decoder (PyAV opening an SDP description of each
stream: payload type 96, H264/90000, the port) receive both streams; reported per stream: packets
before the first keyframe, whether decoding starts at the first keyframe, frames decoded, frame rate,
resolution, decode errors, image statistics, and the latency from the pose's wall-clock stamp to the
decoded frame (the SEI user data each access unit carries). A few decoded frames are written as PNG.
"""
import argparse
import json
import os
import socket
import struct
import subprocess
import sys
import threading
import time
import zlib
from pathlib import Path

sys.dont_write_bytecode = True
import av
import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(ROOT / "sim/mavlink/.gen"))
sys.path.insert(0, str(HERE))
import apm2 as M  # noqa: E402
import geo  # noqa: E402
from camera_component import SEI_UUID, SEI_FMT, POSE_FMT  # noqa: E402

PORTS = [5600, 5602]       # the streams' ports (--rgb-port, --thermal-port; the camera's defaults)

RESULTS = []


def report(name, ok, detail=""):
    RESULTS.append((name, bool(ok)))
    line = f"{'PASS' if ok else 'FAIL'}  {name}{'  ' + detail if detail else ''}"
    print(line, flush=True)
    return line


def write_png(path, rgb):
    """Minimal PNG writer (8-bit RGB, no filter), so the test needs no imaging library."""
    h, w, _ = rgb.shape
    raw = b"".join(b"\0" + rgb[i].tobytes() for i in range(h))
    def chunk(t, d):
        return struct.pack(">I", len(d)) + t + d + struct.pack(">I", zlib.crc32(t + d) & 0xFFFFFFFF)
    Path(path).write_bytes(b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", w, h, 8, 2, 0, 0, 0))
                           + chunk(b"IDAT", zlib.compress(raw, 6)) + chunk(b"IEND", b""))


# --- the synthetic pose feed --------------------------------------------------------------------------

def route():
    """The gorge route (ENU) from gorge.plan: items 1..10 at their altitude above home."""
    plan = json.loads((HERE / "gorge.plan").read_text())
    origin = geo.Origin.from_params([ROOT / "params/x500.params", ROOT / "params/ground.params"])
    home_alt = plan["mission"]["plannedHomePosition"][2] - origin.alt_m
    pts = []
    for it in plan["mission"]["items"][:-1]:
        n, e = origin.ne(it["params"][4], it["params"][5])
        pts.append((float(e), float(n), home_alt + it["params"][6]))
    return np.array(pts)


def feed(port, stop, speed=2.0):
    pts = route()
    seg = np.linalg.norm(np.diff(pts, axis=0), axis=1)
    s_cum = np.concatenate([[0], np.cumsum(seg)])
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    t0, k = time.time(), 0
    while not stop.is_set():
        s = (speed * (time.time() - t0)) % s_cum[-1]
        i = min(np.searchsorted(s_cum, s, side="right") - 1, len(seg) - 1)
        f = (s - s_cum[i]) / seg[i]
        pos = pts[i] + f * (pts[i + 1] - pts[i])
        d = pts[i + 1] - pts[i]
        yaw = np.arctan2(d[1], d[0])                     # PyBullet yaw from east, nose along the route
        q = (0.0, 0.0, np.sin(yaw / 2), np.cos(yaw / 2))
        k += 1
        sock.sendto(struct.pack(POSE_FMT.format, k, k / 100, time.time(), *pos, *q), ("127.0.0.1", port))
        time.sleep(0.01)


# --- the scripted ground station ---------------------------------------------------------------------

class Gcs:
    def __init__(self, port):
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.sock.bind(("127.0.0.1", port))
        self.sock.settimeout(0.05)
        self.mav = M.MAVLink(self, srcSystem=255, srcComponent=190)
        self.mav.robust_parsing = True
        self.peer, self.msgs, self.lock = None, [], threading.Lock()
        self.bad = 0
        self.running = True
        threading.Thread(target=self._rx, daemon=True).start()

    def write(self, buf):
        if self.peer:
            self.sock.sendto(buf, self.peer)

    def _rx(self):
        while self.running:
            try:
                data, addr = self.sock.recvfrom(4096)
            except socket.timeout:
                continue
            except OSError:
                return
            self.peer = addr
            for m in self.mav.parse_buffer(data) or []:
                if m.get_type() == "BAD_DATA":
                    self.bad += 1
                    continue
                with self.lock:
                    self.msgs.append((time.time(), m))

    def wait(self, typ, cond=lambda m: True, timeout=1.0, after=None):
        t0 = time.time() if after is None else after
        while time.time() < t0 + timeout:
            with self.lock:
                for t, m in self.msgs:
                    if t >= t0 and m.get_type() == typ and cond(m):
                        return t, m
            time.sleep(0.005)
        return None, None

    def command(self, cmd, *p, comp=100):
        p = list(p) + [0] * (7 - len(p))
        t = time.time()
        self.mav.command_long_send(1, comp, cmd, 0, *p)
        return t


def protocol(g, out_lines):
    log = out_lines.append
    t, hb = g.wait("HEARTBEAT", lambda m: m.get_srcComponent() == 100, timeout=30.0)   # after the workers load the world
    hbs = [m for _, m in g.msgs if m.get_type() == "HEARTBEAT"]
    log(report("heartbeat from 1/100: type CAMERA (30), autopilot INVALID (8), state ACTIVE",
               hb is not None and hb.get_srcSystem() == 1 and hb.type == 30 and hb.autopilot == 8 and hb.system_status == 4,
               f"{hb}" if hb else "none in 30 s"))
    time.sleep(2.2)
    ts = [t for t, m in g.msgs if m.get_type() == "HEARTBEAT"]
    rate = (len(ts) - 1) / (ts[-1] - ts[0]) if len(ts) > 1 else 0
    log(report("heartbeat rate 1 Hz (QGCCameraManager: a camera silent for 5 s is removed)", 0.8 <= rate <= 1.2, f"{rate:.2f} Hz over {len(ts)}"))

    def req(name, cmd, params, msg, cond=lambda m: True, n=1):
        t0 = g.command(cmd, *params)
        ta, ack = g.wait("COMMAND_ACK", lambda m: m.command == cmd and m.get_srcComponent() == 100, timeout=1.2, after=t0)
        got = []
        if ack is not None and ack.result == 0:
            end = time.time() + 1.0
            while time.time() < end and len(got) < n:
                with g.lock:
                    got = [m for t, m in g.msgs if t >= t0 and m.get_type() == msg]
                time.sleep(0.01)
            time.sleep(0.05)
            with g.lock:
                got = [m for t, m in g.msgs if t >= t0 and m.get_type() == msg]
        ok = ack is not None and ack.result == 0 and len(got) == n and all(cond(m) for m in got)
        ack_ms = (ta - t0) * 1000 if ta else None
        log(report(name, ok, f"ack {ack.result if ack else None} in {ack_ms:.1f} ms, {len(got)} x {msg}" if ack else "no ack in 1.2 s"))
        return got

    info = req("CAMERA_INFORMATION by REQUEST_MESSAGE (512, 259): ACK ACCEPTED then the message; flags HAS_VIDEO_STREAM, no definition uri",
               512, (259,), "CAMERA_INFORMATION", lambda m: m.flags & 256 and m.cam_definition_uri == "" and m.resolution_h > 0)
    if info:
        m = info[0]
        log(f"      vendor {bytes(m.vendor_name).rstrip(bytes(1))!r} model {bytes(m.model_name).rstrip(bytes(1))!r} "
            f"{m.resolution_h}x{m.resolution_v} flags {m.flags}")
    req("CAMERA_INFORMATION by MAV_CMD_REQUEST_CAMERA_INFORMATION (521, QGroundControl's alternate retry)", 521, (1,),
        "CAMERA_INFORMATION")
    req("CAMERA_SETTINGS by REQUEST_MESSAGE (512, 260): mode VIDEO (1)", 512, (260,), "CAMERA_SETTINGS", lambda m: m.mode_id == 1)
    req("CAMERA_SETTINGS by MAV_CMD_REQUEST_CAMERA_SETTINGS (522, legacy)", 522, (1,), "CAMERA_SETTINGS")
    t0 = g.command(512, 271)
    _, ack = g.wait("COMMAND_ACK", lambda m: m.command == 512 and m.get_srcComponent() == 100, timeout=1.2, after=t0)
    time.sleep(0.3)
    fov = [m for t, m in g.msgs if t >= t0 and m.get_type() == "CAMERA_FOV_STATUS"]
    log(report("CAMERA_FOV_STATUS request (after CAMERA_SETTINGS): UNSUPPORTED and no message (QGroundControl would store "
               "it as the gimbal settings cameraHFov/cameraVFov)", ack is not None and ack.result == 3 and not fov,
               f"ack {ack.result if ack else None}"))
    vs = req("VIDEO_STREAM_INFORMATION by REQUEST_MESSAGE (512, 269, 0 = all): 2 streams, count 2", 512, (269, 0),
             "VIDEO_STREAM_INFORMATION", lambda m: m.count == 2, n=2)
    if len(vs) == 2:
        a, b = sorted(vs, key=lambda m: m.stream_id)
        log(report(f"stream 1: RTPUDP (1), H264 (1), uri 'udp://127.0.0.1:{PORTS[0]}', not thermal, running; hfov 90",
                   a.stream_id == 1 and a.type == 1 and a.encoding == 1 and a.uri == f"udp://127.0.0.1:{PORTS[0]}" and not a.flags & 2 and a.flags & 1 and a.hfov == 90,
                   f"name {a.name!r} {a.resolution_h}x{a.resolution_v} {a.framerate:g} fps {a.bitrate} bit/s flags {a.flags}"))
        log(report(f"stream 2: RTPUDP (1), H264 (1), uri 'udp://127.0.0.1:{PORTS[1]}', flags THERMAL | RUNNING; hfov 57",
                   b.stream_id == 2 and b.type == 1 and b.encoding == 1 and b.uri == f"udp://127.0.0.1:{PORTS[1]}" and b.flags & 2 and b.flags & 1 and b.hfov == 57,
                   f"name {b.name!r} {b.resolution_h}x{b.resolution_v} {b.framerate:g} fps {b.bitrate} bit/s flags {b.flags}"))
    req("VIDEO_STREAM_INFORMATION by MAV_CMD_REQUEST_VIDEO_STREAM_INFORMATION (2504) for stream 2 only", 2504, (2,),
        "VIDEO_STREAM_INFORMATION", lambda m: m.stream_id == 2)
    req("VIDEO_STREAM_STATUS by REQUEST_MESSAGE (512, 270, stream 1)", 512, (270, 1), "VIDEO_STREAM_STATUS", lambda m: m.stream_id == 1)
    req("VIDEO_STREAM_STATUS by MAV_CMD_REQUEST_VIDEO_STREAM_STATUS (2505, stream 2)", 2505, (2,), "VIDEO_STREAM_STATUS",
        lambda m: m.stream_id == 2 and m.flags & 2)
    req("CAMERA_CAPTURE_STATUS by REQUEST_MESSAGE (512, 262): idle", 512, (262,), "CAMERA_CAPTURE_STATUS",
        lambda m: m.image_status == 0 and m.video_status == 0)
    req("CAMERA_CAPTURE_STATUS by MAV_CMD_REQUEST_CAMERA_CAPTURE_STATUS (527, legacy)", 527, (1,), "CAMERA_CAPTURE_STATUS")
    req("STORAGE_INFORMATION by REQUEST_MESSAGE (512, 261, 0): status NOT_SUPPORTED (3)", 512, (261, 0), "STORAGE_INFORMATION",
        lambda m: m.status == 3)
    req("STORAGE_INFORMATION by MAV_CMD_REQUEST_STORAGE_INFORMATION (525, legacy)", 525, (0, 1), "STORAGE_INFORMATION")
    for cmd, name in ((2502, "VIDEO_START_STREAMING"), (2503, "VIDEO_STOP_STREAMING")):
        t0 = g.command(cmd, 1)
        _, ack = g.wait("COMMAND_ACK", lambda m, c=cmd: m.command == c and m.get_srcComponent() == 100, timeout=1.2, after=t0)
        log(report(f"{name} ({cmd}) stream 1: ACCEPTED", ack is not None and ack.result == 0))
    g.command(2502, 1)
    t0 = g.command(203, 1)                      # DO_DIGICAM_CONTROL: not offered
    _, ack = g.wait("COMMAND_ACK", lambda m: m.command == 203 and m.get_srcComponent() == 100, timeout=1.2, after=t0)
    log(report("unknown command (203): UNSUPPORTED", ack is not None and ack.result == 3))
    t0 = g.command(512, 259, comp=1)
    _, ack = g.wait("COMMAND_ACK", lambda m: m.get_srcComponent() == 100 and m.command == 512, timeout=1.2, after=t0)
    log(report("a REQUEST_MESSAGE for the autopilot (component 1): ignored by the camera", ack is None))
    log(report("every frame from the camera parsed by pymavlink (CRC_EXTRA, lengths)", g.bad == 0, f"{g.bad} bad"))


# --- the independent receiver -------------------------------------------------------------------------

def sei_records(data):
    """(index, pose wall, slot wall, send wall) of our SEI user data in an Annex B packet."""
    out = []
    for part in data.split(b"\x00\x00\x01")[1:]:
        if not part or part[0] & 0x1F != 6:
            continue
        rbsp, zeros = bytearray(), 0
        for b in part[1:]:
            if zeros >= 2 and b == 3:
                zeros = 0
                continue
            rbsp.append(b)
            zeros = zeros + 1 if b == 0 else 0
        if len(rbsp) > 2 + 16 + SEI_FMT.size and rbsp[0] == 5 and bytes(rbsp[2:18]) == SEI_UUID:
            out.append(SEI_FMT.unpack(bytes(rbsp[18:18 + SEI_FMT.size])))
    return out


def receive(port, seconds, out, tag, res):
    sdp = out / f"{tag}.sdp"
    sdp.write_text(f"v=0\no=- 0 0 IN IP4 127.0.0.1\ns={tag}\nc=IN IP4 127.0.0.1\nt=0 0\n"
                   f"m=video {port} RTP/AVP 96\na=rtpmap:96 H264/90000\na=fmtp:96 packetization-mode=1\n")
    r = dict(port=port, packets=0, before_key=0, key_at=None, first_decoded=None, frames=0, errors=0, latency=[], times=[],
             size=None, idx=[], saved=[])
    c = av.open(str(sdp), format="sdp", options={"protocol_whitelist": "file,udp,rtp", "fflags": "nobuffer",
                                                  "reorder_queue_size": "0", "probesize": "32", "analyzeduration": "0"})
    st = c.streams.video[0]
    st.codec_context.flags |= av.codec.context.Flags.low_delay
    t_end = time.time() + seconds
    for pkt in c.demux(st):
        if time.time() > t_end:
            break
        if pkt.size == 0:
            continue
        r["packets"] += 1
        recs = sei_records(bytes(pkt))
        if r["key_at"] is None:
            if pkt.is_keyframe:
                r["key_at"] = recs[0][0] if recs else -1
            else:
                r["before_key"] += 1
        try:
            frames = st.codec_context.decode(pkt)
        except av.error.InvalidDataError:
            r["errors"] += 1 if r["key_at"] is not None else 0
            continue
        for fr in frames:
            now = time.time()
            r["frames"] += 1
            r["times"].append(now)
            r["size"] = (fr.width, fr.height)
            if recs:
                idx, pose_wall, slot_wall, send_wall = recs[0]
                r["idx"].append(idx)
                if r["first_decoded"] is None:
                    r["first_decoded"] = idx
                if pose_wall > 0:
                    r["latency"].append((now - pose_wall, now - slot_wall, now - send_wall))
            if r["frames"] in (5, 40, 80, 120):
                img = fr.to_ndarray(format="rgb24")
                p = out / f"{tag}-frame{r['frames']:03d}.png"
                write_png(p, img)
                r["saved"].append((str(p), float(img.std()), float(img.mean())))
    c.close()
    res[tag] = r


def receive_raw(port, seconds, res, tag):
    """RFC 6184 depacketizer of our own (single NAL unit, FU-A, STAP-A), an access unit handed to FFmpeg's
    H.264 decoder when its marker bit arrives, as GStreamer's rtph264depay does: the latency without
    the one-frame hold of FFmpeg's demuxer parser."""
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.bind(("0.0.0.0", port))
    sock.settimeout(0.5)
    dec = av.CodecContext.create("h264", "r")
    dec.flags |= av.codec.context.Flags.low_delay
    au, fu, lat, frames, lost, last_seq, started = [], None, [], 0, 0, None, False
    t_end = time.time() + seconds
    while time.time() < t_end:
        try:
            pkt = sock.recv(65536)
        except socket.timeout:
            continue
        cc, x = pkt[0] & 0x0F, pkt[0] & 0x10
        marker, seq = pkt[1] & 0x80, struct.unpack("!H", pkt[2:4])[0]
        if last_seq is not None and seq != (last_seq + 1) & 0xFFFF:
            lost += (seq - last_seq - 1) & 0xFFFF
        last_seq = seq
        off = 12 + 4 * cc
        if x:
            off += 4 + 4 * struct.unpack("!H", pkt[off + 2:off + 4])[0]
        pl = pkt[off:]
        typ = pl[0] & 0x1F
        if typ < 24:
            au.append(pl)
        elif typ == 24:
            o = 1
            while o + 2 <= len(pl):
                n = struct.unpack("!H", pl[o:o + 2])[0]
                au.append(pl[o + 2:o + 2 + n]); o += 2 + n
        elif typ == 28:
            if pl[1] & 0x80:
                fu = bytearray([(pl[0] & 0xE0) | (pl[1] & 0x1F)])
            if fu is not None:
                fu += pl[2:]
                if pl[1] & 0x40:
                    au.append(bytes(fu)); fu = None
        if marker:
            data = b"".join(b"\x00\x00\x00\x01" + n for n in au)
            recs = sei_records(data)
            started = started or any(n[0] & 0x1F == 5 for n in au)
            au = []
            if not started:
                continue
            try:
                out = dec.decode(av.Packet(data))
            except av.error.InvalidDataError:
                continue
            now = time.time()
            for _ in out:
                frames += 1
                if recs and recs[0][1] > 0:
                    lat.append((now - recs[0][1], now - recs[0][2], now - recs[0][3]))
    sock.close()
    res[tag + "-raw"] = dict(frames=frames, lost_packets=lost, latency=lat)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--seconds", type=float, default=20.0, help="stream reception time")
    ap.add_argument("--gcs-port", type=int, default=14590)
    ap.add_argument("--pose-port", type=int, default=14611)
    ap.add_argument("--rgb", default=None, help="camera_component --rgb (default: its own)")
    ap.add_argument("--rgb-port", type=int, default=5600, help="the RGB stream's port (camera_component --rgb-port)")
    ap.add_argument("--thermal-port", type=int, default=5602, help="the thermal stream's port (camera_component --thermal-port)")
    ap.add_argument("--rgb-workers", default=None)
    ap.add_argument("--out", default=str(HERE / "out" / "test-camera"))
    a = ap.parse_args()
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    lines = []
    g = Gcs(a.gcs_port)
    stop = threading.Event()
    threading.Thread(target=feed, args=(a.pose_port, stop), daemon=True).start()
    PORTS[:] = [a.rgb_port, a.thermal_port]
    extra = (["--rgb", a.rgb] if a.rgb else []) + (["--rgb-workers", a.rgb_workers] if a.rgb_workers else []) + \
        ["--rgb-port", str(a.rgb_port), "--thermal-port", str(a.thermal_port)]
    cam = subprocess.Popen([sys.executable, str(HERE / "camera_component.py"), "--gcs", f"127.0.0.1:{a.gcs_port}",
                            "--pose-port", str(a.pose_port), "--stats", str(out / "camera.json"), "--log", str(out / "camera.log"), *extra],
                           stdout=open(out / "camera.out", "w"), stderr=subprocess.STDOUT)
    res = {}
    try:
        protocol(g, lines)
        for phase in ((receive, (a.rgb_port, a.seconds, out, "rgb", res), (a.thermal_port, a.seconds, out, "thermal", res)),
                      (receive_raw, (a.rgb_port, a.seconds / 2, res, "rgb"), (a.thermal_port, a.seconds / 2, res, "thermal"))):
            rx = [threading.Thread(target=phase[0], args=args) for args in phase[1:]]
            for t in rx:
                t.start()
            for t in rx:
                t.join(a.seconds + 30)
    finally:
        stop.set()
        cam.send_signal(2)
        try:
            cam.wait(10)
        except subprocess.TimeoutExpired:
            cam.kill()
        g.running = False
    for tag in ("rgb", "thermal"):
        r = res.get(tag)
        if r is None:
            lines.append(report(f"{tag}: stream received", False))
            continue
        span = r["times"][-1] - r["times"][0] if len(r["times"]) > 1 else 0
        fps = (len(r["times"]) - 1) / span if span else 0
        lat = np.array(r["latency"]) * 1000 if r["latency"] else np.zeros((1, 3))
        gaps = np.diff(r["idx"]) if len(r["idx"]) > 1 else np.array([1])
        lines.append(report(f"{tag}: decodable from the first keyframe (first decoded frame is the first keyframe's)",
                            r["key_at"] is not None and r["first_decoded"] == r["key_at"] and r["errors"] == 0,
                            f"{r['before_key']} packets before it, keyframe index {r['key_at']}, first decoded {r['first_decoded']}, "
                            f"decode errors after it {r['errors']}"))
        lines.append(report(f"{tag}: frames decoded at a steady rate", r["frames"] > 0 and fps > 0,
                            f"{r['frames']} frames in {span:.1f} s = {fps:.2f} fps; index gaps max {gaps.max()} (dropped slots); "
                            f"resolution {r['size']}"))
        nontriv = [s for _, s, _ in r["saved"]]
        lines.append(report(f"{tag}: non-trivial images (luma standard deviation > 10 in every saved frame)",
                            nontriv and min(nontriv) > 10, ", ".join(f"{Path(p).name} std {s:.1f} mean {m:.1f}" for p, s, m in r["saved"])))
        lines.append(report(f"{tag}: latency pose -> decoded frame (SEI stamps), FFmpeg RTP demuxer (its H.264 parser holds a "
                            f"frame until the next one starts)", len(r["latency"]) > 0,
                            f"mean {lat[:, 0].mean():.1f} ms, p95 {np.percentile(lat[:, 0], 95):.1f}, max {lat[:, 0].max():.1f}; "
                            f"slot -> decoded mean {lat[:, 1].mean():.1f} ms; socket -> decoded mean {lat[:, 2].mean():.1f} ms"))
        rr = res.get(tag + "-raw", {})
        lr = np.array(rr.get("latency") or [[0, 0, 0]]) * 1000
        lines.append(report(f"{tag}: latency pose -> decoded frame, marker-bit depacketizer + FFmpeg decoder (as rtph264depay)",
                            rr.get("frames", 0) > 0 and rr.get("lost_packets", 1) == 0,
                            f"{rr.get('frames', 0)} frames, {rr.get('lost_packets')} packets lost; mean {lr[:, 0].mean():.1f} ms, "
                            f"p95 {np.percentile(lr[:, 0], 95):.1f}, max {lr[:, 0].max():.1f}; of which pose -> slot "
                            f"{(lr[:, 0] - lr[:, 1]).mean():.1f} ms, slot -> socket (render, encode) {(lr[:, 1] - lr[:, 2]).mean():.1f} ms, "
                            f"socket -> decoded {lr[:, 2].mean():.1f} ms"))
        if rr:
            rr["latency_ms"] = dict(mean=float(lr[:, 0].mean()), p95=float(np.percentile(lr[:, 0], 95)), max=float(lr[:, 0].max()))
            rr.pop("latency")
        r.pop("times"); r.pop("idx")
        r["latency_ms"] = dict(mean=float(lat[:, 0].mean()), p95=float(np.percentile(lat[:, 0], 95)), max=float(lat[:, 0].max()))
        r.pop("latency")
        r["fps"] = fps
    try:
        stats = json.loads((out / "camera.json").read_text())
        for s in stats["streams"]:
            lines.append(f"      camera: stream {s['stream_id']} {s['name']}: {s['frames_sent']} frames sent, achieved "
                         f"{s['fps_achieved']:.2f} fps (target {s['fps_target']}), {s['slots_dropped']} slots dropped, render "
                         f"{s['render_ms_mean']:.1f} ms mean / {s['render_ms_max']:.1f} max, encode {s['encode_ms_mean']:.2f} ms, "
                         f"{(s['bitrate_achieved'] or 0) / 1000:.0f} kbit/s")
        print("\n".join(lines[-2:]))
    except (OSError, ValueError, KeyError, TypeError):
        pass
    n_ok = sum(ok for _, ok in RESULTS)
    lines.append(f"{n_ok}/{len(RESULTS)} passed")
    print(lines[-1])
    (out / "report.txt").write_text("\n".join(lines) + "\n")
    (out / "streams.json").write_text(json.dumps(res, indent=1, default=str) + "\n")
    return 0 if n_ok == len(RESULTS) else 1


if __name__ == "__main__":
    sys.exit(main())
