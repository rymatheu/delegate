"""Simulated camera payload of the gorge session: a MAVLink camera component (system 1, component 100,
MAV_TYPE_CAMERA) with two RTP/H.264 video streams, forward RGB and forward thermal.

    sim/world/.venv-video/bin/python sim/world/camera_component.py [--gcs 127.0.0.1:14550]
        [--pose-port 14601] [--rgb 640x480@15] [--rgb-workers 2] [--thermal 640x512] [--thermal-fps 8.7]
        [--thermal-workers 2] [--thermal-lod 0]
        [--rgb-port 5600] [--thermal-port 5602] [--sysid 1] [--label Forward] [--stats FILE] [--log FILE]

It is simulated hardware, separate from the flight controller: its own UDP socket and MAVLink
sequence, talking to the ground station like a companion camera on the same link. What it answers is
what QGroundControl 5.1.5 asks of a MAVLink camera (sim/world/QGC-CAMERA.md has the sources):

- HEARTBEAT at 1 Hz (type CAMERA, autopilot INVALID, state ACTIVE): QGCCameraManager starts discovery;
- COMMAND_LONG / COMMAND_INT addressed to (1, 100), each acknowledged (COMMAND_ACK to the sender)
  before the message it asks for: REQUEST_MESSAGE (512) and the legacy request commands for
  CAMERA_INFORMATION (521), CAMERA_SETTINGS (522), STORAGE_INFORMATION (525), CAMERA_CAPTURE_STATUS
  (527), VIDEO_STREAM_INFORMATION (2504, stream id, 0 = all), VIDEO_STREAM_STATUS (2505);
  VIDEO_START_STREAMING / VIDEO_STOP_STREAMING (2502, 2503) ACCEPTED (the streams run continuously, unless
  --rgb-gated on|off: then the RGB stream is sent only between a START and a STOP);
  everything else UNSUPPORTED, in particular REQUEST_MESSAGE CAMERA_FOV_STATUS, whose answer would
  make QGroundControl write the gimbal settings cameraHFov and cameraVFov;
- CAMERA_INFORMATION: flags CAMERA_CAP_FLAGS_HAS_VIDEO_STREAM only, no camera definition file (a
  "basic" camera: no parameters, no photo or video capture); CAMERA_SETTINGS mode VIDEO;
  STORAGE_INFORMATION status NOT_SUPPORTED; CAMERA_CAPTURE_STATUS idle;
- VIDEO_STREAM_INFORMATION, count 2: stream 1 "Forward RGB" and stream 2 "Forward thermal" (flags
  RUNNING | THERMAL), type RTPUDP, encoding H264, uri "udp://127.0.0.1:5600" and
  "udp://127.0.0.1:5602" (even RTP ports: receivers that open RTCP on port + 1, as FFmpeg does, can
  take both streams). QGroundControl's VideoManager::_updateAutoStream takes a uri with "udp://" as
  the receiver's URL (a bare port number becomes udp://0.0.0.0:PORT) and switches its main receiver to
  "UDP h.264". The full URL is needed for the receivers to start: in 5.1.5 the URL is set by the
  receiver's videoStreamInfoChanged handler before _videoSourceChanged compares it, so with a bare
  port nothing ever "changes" and _restartAllVideos is never called (observed: URL set, receiver never
  started). With a URL different from "udp://" + the udpUrl setting (default 0.0.0.0:5600),
  _updateSettings then replaces it by the udpUrl one, sees the change and starts both receivers (the
  main one ends on udp://0.0.0.0:5600, the thermal one on udp://127.0.0.1:5602). `--uri-form port`
  announces bare ports instead.

`--sysid N` makes it the camera of vehicle N (component N/100; the formation session runs one per
vehicle), and `--label TEXT` names the streams "TEXT RGB" and "TEXT thermal" (default "Forward").

Video: render workers (camera_render.py, in the simulator's Python with PyBullet) draw each frame from
the latest vehicle pose that gorge_session.py sends (UDP, 100 Hz; before the first one, the start
resting on the floor); frames are taken on a fixed schedule (`fps`), each by the next idle worker
(a slot with no idle worker is dropped and counted). Encoding: libx264 (PyAV's bundled FFmpeg; never
VideoToolbox), preset ultrafast, tune zerolatency (no B-frames, no lookahead: one access unit per
frame), constrained baseline, a keyframe every second with SPS and PPS repeated in band before it
(`repeat-headers`), Annex B. RTP (RFC 6184): payload type 96, 90 kHz clock from the wall clock at the
frame's slot, single NAL unit packets up to 1200 bytes and FU-A fragments above, marker bit on the
last packet of each frame, one SSRC per stream. Each access unit carries one SEI user-data-unregistered
NAL unit (UUID SEI_UUID) with the frame index and the times (time.time) at which the simulation
published the pose, the frame's slot and the hand-over to the socket, for the latency test; decoders
ignore it.
"""
import argparse
import collections
import json
import math
import os
import signal
import socket
import struct
import subprocess
import sys
import threading
import time
import uuid
from fractions import Fraction
from pathlib import Path

sys.dont_write_bytecode = True
import av
import numpy as np

HERE = Path(__file__).resolve().parent
SIM_PY = os.environ.get("LEANFC_PY") or str(Path(__file__).resolve().parents[2] / "sim" / ".venv" / "bin" / "python")
POSE_FMT = struct.Struct("<Idd3d4d")      # gorge_session.POSE_FMT
REQ, REP = struct.Struct("<I3d4dd"), struct.Struct("<Id")  # camera_render.REQ, REP (the pose and its simulated time)
SEI_UUID = uuid.uuid5(uuid.NAMESPACE_URL, "leanfc/sim/world/camera_component").bytes
SEI_FMT = struct.Struct("<Iddd")          # frame index, pose wall time, slot wall time, send wall time
SYSID, COMPID = 1, 100          # SYSID is set from --sysid in main
MODEL = b"gorge forward camera"  # CAMERA_INFORMATION model name (with the system id appended for N > 1)
MTU = 1200

# --- MAVLink 2, the few messages of a camera (layouts and CRC_EXTRA of the MAVLink XML, checked
#     against pymavlink's generated dialect by test_camera.py) ----------------------------------------
MSG = {  # id: (CRC_EXTRA, struct format of the payload in wire order, extensions included)
    0: (50, "<IBBBBB"),                                   # HEARTBEAT
    75: (158, "<4fiifHBBBBB"),                            # COMMAND_INT
    76: (152, "<7fHBBB"),                                 # COMMAND_LONG
    77: (143, "<HBBiBB"),                                 # COMMAND_ACK
    259: (92, "<IIfffIHHH32s32sB140sBB"),                 # CAMERA_INFORMATION
    260: (146, "<IBffB"),                                 # CAMERA_SETTINGS
    261: (179, "<IfffffBBBB32sB"),                        # STORAGE_INFORMATION
    262: (12, "<IfIfBBiB"),                               # CAMERA_CAPTURE_STATUS
    269: (109, "<fIHHHHHBBB32s160sBBH"),                  # VIDEO_STREAM_INFORMATION
    270: (59, "<fIHHHHHBBH"),                             # VIDEO_STREAM_STATUS
}
ACCEPTED, UNSUPPORTED = 0, 3


def crc16(buf, crc=0xFFFF):
    for b in buf:
        t = (b ^ crc) & 0xFF
        t = (t ^ (t << 4)) & 0xFF
        crc = ((crc >> 8) ^ (t << 8) ^ (t << 3) ^ (t >> 4)) & 0xFFFF
    return crc


def parse(data):
    """MAVLink 1 and 2 frames of one datagram with a valid checksum, for the messages in MSG:
    (msgid, sysid, compid, payload padded to its full length)."""
    out, i = [], 0
    while i < len(data):
        if data[i] == 0xFD and i + 10 <= len(data):
            n, flags = data[i + 1], data[i + 2]
            end = i + 10 + n + 2 + (13 if flags & 1 else 0)
            mid = int.from_bytes(data[i + 7:i + 10], "little")
            body, crc_at = data[i + 1:i + 10 + n], i + 10 + n
            sysid, compid, pl = data[i + 5], data[i + 6], data[i + 10:i + 10 + n]
        elif data[i] == 0xFE and i + 6 <= len(data):
            n = data[i + 1]
            end = i + 6 + n + 2
            mid, body, crc_at = data[i + 5], data[i + 1:i + 6 + n], i + 6 + n
            sysid, compid, pl = data[i + 3], data[i + 4], data[i + 6:i + 6 + n]
        else:
            i += 1
            continue
        if end > len(data) or mid not in MSG:
            i = end if end <= len(data) and mid not in MSG else i + 1
            continue
        crc_extra, fmt = MSG[mid]
        if crc16(bytes([crc_extra]), crc16(body)) != int.from_bytes(data[crc_at:crc_at + 2], "little"):
            i += 1
            continue
        out.append((mid, sysid, compid, bytes(pl).ljust(struct.calcsize(fmt), b"\0")[:struct.calcsize(fmt)]))
        i = end
    return out


class Mav:
    """MAVLink 2 sender of component (SYSID, COMPID) on one UDP socket; payloads truncated (MAVLink 2)."""

    def __init__(self, sock, dest, log=None):
        self.sock, self.dest, self.seq, self.log, self.lock = sock, dest, 0, log, threading.Lock()

    def send(self, mid, *fields):
        crc_extra, fmt = MSG[mid]
        pl = struct.pack(fmt, *fields).rstrip(b"\0") or b"\0"
        with self.lock:
            hdr = bytes([0xFD, len(pl), 0, 0, self.seq, SYSID, COMPID]) + mid.to_bytes(3, "little")
            self.seq = (self.seq + 1) & 0xFF
            crc = crc16(bytes([crc_extra]), crc16(hdr[1:] + pl))
            try:
                self.sock.sendto(hdr + pl + crc.to_bytes(2, "little"), self.dest)
            except OSError:
                pass
            if self.log:
                self.log.write(f"{time.time():.4f} > {mid} {pl.hex()}\n")


# --- RTP / H.264 -------------------------------------------------------------------------------------

def nal_units(annexb):
    """NAL units (without start codes) of an Annex B byte stream."""
    out, i, n = [], 0, len(annexb)
    starts = []
    while True:
        j = annexb.find(b"\x00\x00\x01", i)
        if j < 0:
            break
        starts.append(j + 3)
        i = j + 3
    for k, s in enumerate(starts):
        e = starts[k + 1] - 3 if k + 1 < len(starts) else n
        nal = annexb[s:e]
        while nal.endswith(b"\x00") and k + 1 < len(starts):   # the zero of a 4-byte start code
            nal = nal[:-1]
        if nal:
            out.append(nal)
    return out


def sei_nal(payload):
    """SEI NAL unit (type 6) with one user_data_unregistered message (payload type 5)."""
    body = SEI_UUID + payload
    rbsp = bytes([5, len(body)]) + body + b"\x80"
    ebsp, zeros = bytearray(), 0
    for b in rbsp:                                 # emulation prevention
        if zeros >= 2 and b <= 3:
            ebsp.append(3)
            zeros = 0
        ebsp.append(b)
        zeros = zeros + 1 if b == 0 else 0
    return b"\x06" + bytes(ebsp)


class RtpSender:
    def __init__(self, sock, dest, pt=96):
        self.sock, self.dest, self.pt = sock, dest, pt
        self.seq = int.from_bytes(os.urandom(2), "big")
        self.ssrc = int.from_bytes(os.urandom(4), "big")
        self.packets = self.bytes = 0

    def _send(self, payload, ts, marker):
        hdr = struct.pack("!BBHII", 0x80, (0x80 if marker else 0) | self.pt, self.seq, ts & 0xFFFFFFFF, self.ssrc)
        self.seq = (self.seq + 1) & 0xFFFF
        try:
            self.sock.sendto(hdr + payload, self.dest)
        except OSError:
            pass
        self.packets += 1
        self.bytes += len(payload) + 12

    def send_au(self, nals, ts):
        """One access unit: single NAL unit packets, FU-A fragments for NAL units above MTU."""
        for k, nal in enumerate(nals):
            last = k == len(nals) - 1
            if len(nal) <= MTU:
                self._send(nal, ts, last)
                continue
            ind, typ, data = (nal[0] & 0xE0) | 28, nal[0] & 0x1F, nal[1:]
            for o in range(0, len(data), MTU - 2):
                s, e = o == 0, o + MTU - 2 >= len(data)
                self._send(bytes([ind, (0x80 if s else 0) | (0x40 if e else 0) | typ]) + data[o:o + MTU - 2], ts, last and e)


# --- the camera --------------------------------------------------------------------------------------

class Poses:
    """The latest vehicle pose from the simulation (UDP); before the first, the start at rest."""

    def __init__(self, port, start):
        self.latest = (0, 0.0, 0.0, *start, 0.0, 0.0, math.sin(math.pi / 4), math.cos(math.pi / 4))
        self.count = 0
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.sock.bind(("127.0.0.1", port))
        self.sock.settimeout(0.5)
        threading.Thread(target=self._rx, daemon=True).start()

    def _rx(self):
        while True:
            try:
                data, _ = self.sock.recvfrom(256)
            except socket.timeout:
                continue
            except OSError:
                return
            if len(data) == POSE_FMT.size:
                self.latest = POSE_FMT.unpack(data)
                self.count += 1


class Worker:
    def __init__(self, args, nbytes):
        self.p = subprocess.Popen([SIM_PY, "-B", str(HERE / "camera_render.py"), *args], stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        self.nbytes = nbytes

    def wait_ready(self):
        line = self.p.stdout.readline()
        if line != b"RDY\n":
            raise RuntimeError(f"render worker did not start: {line!r}")

    def render(self, idx, pose):
        self.p.stdin.write(REQ.pack(idx, *pose[3:10], pose[1]))
        self.p.stdin.flush()
        hdr = self.p.stdout.read(REP.size)
        img = self.p.stdout.read(self.nbytes)
        if len(hdr) < REP.size or len(img) < self.nbytes:
            raise EOFError("render worker ended")
        return REP.unpack(hdr)[1], img


class Stream:
    def __init__(self, sid, name, w, h, fps, hfov, thermal, port, bitrate, workers, poses, sock):
        self.sid, self.name, self.w, self.h, self.fps, self.hfov = sid, name, w, h, fps, hfov
        self.thermal, self.port, self.bitrate, self.workers, self.poses = thermal, port, bitrate, workers, poses
        self.rtp = RtpSender(sock, ("127.0.0.1", port))
        enc = av.CodecContext.create("libx264", "w")
        enc.width, enc.height, enc.pix_fmt = w, h, "yuv420p"
        enc.time_base, enc.framerate, enc.bit_rate = Fraction(1, 90000), Fraction(fps).limit_denominator(1000), bitrate
        gop = max(1, round(fps))
        enc.options = {"preset": "ultrafast", "tune": "zerolatency", "profile": "baseline",
                       "x264-params": f"keyint={gop}:min-keyint={gop}:scenecut=0:repeat-headers=1:annexb=1"}
        enc.open()
        self.enc = enc
        self.lock, self.cv = threading.Lock(), threading.Condition()
        self.order, self.results = collections.deque(), {}
        self.next_idx, self.next_t, self.running = 0, None, True
        self.sent = self.dropped = 0
        self.on = True                                         # see --rgb-gated
        self.render_ms, self.encode_ms, self.t_first = [], [], None

    def flags(self):
        return 1 | (2 if self.thermal else 0)              # RUNNING, THERMAL

    def start(self):
        for w in self.workers:
            threading.Thread(target=self._work, args=(w,), daemon=True).start()
        threading.Thread(target=self._encode, daemon=True).start()

    def _work(self, w):
        period = 1.0 / self.fps
        while self.running:
            with self.lock:
                now = time.monotonic()
                if self.next_t is None:
                    self.next_t = now
                if self.next_t < now - period:               # behind: the missed slots are dropped
                    miss = int((now - self.next_t) / period)
                    self.next_t += miss * period
                    self.dropped += miss
                t_slot, idx = self.next_t, self.next_idx
                self.next_idx += 1
                self.next_t += period
                self.order.append(idx)
            time.sleep(max(0.0, t_slot - time.monotonic()))
            pose, wall = self.poses.latest, time.time()
            try:
                ms, img = w.render(idx, pose)
            except (EOFError, OSError, ValueError):
                self.running = False
                with self.cv:
                    self.cv.notify_all()
                return
            with self.cv:
                self.results[idx] = (img, pose, wall, ms)
                self.cv.notify_all()

    def _encode(self):
        while self.running:
            with self.cv:
                while self.running and not (self.order and self.order[0] in self.results):
                    self.cv.wait(0.5)
                if not self.running:
                    return
                idx = self.order.popleft()
                img, pose, wall, ms = self.results.pop(idx)
            t0 = time.perf_counter()
            frame = av.VideoFrame.from_ndarray(np.frombuffer(img, np.uint8).reshape(self.h, self.w, 3), format="rgb24")
            frame = frame.reformat(format="yuv420p")
            ts = int(round(wall * 90000)) & 0xFFFFFFFF          # RTP clock: the wall clock at the slot
            frame.pts = self.sent * int(round(90000 / self.fps))  # encoder clock: monotonic
            data = b"".join(bytes(pk) for pk in self.enc.encode(frame))
            nals = nal_units(data)
            first_vcl = next((k for k, n in enumerate(nals) if n[0] & 0x1F in (1, 5)), len(nals))
            nals.insert(first_vcl, sei_nal(SEI_FMT.pack(idx, pose[2], wall, time.time())))
            if self.on:                                         # --rgb-gated: only between START and STOP
                self.rtp.send_au(nals, ts)
            self.encode_ms.append((time.perf_counter() - t0) * 1000)
            self.render_ms.append(ms)
            self.sent += 1
            if self.t_first is None:
                self.t_first = time.monotonic()
            self.t_last = time.monotonic()

    def stats(self):
        el = (self.t_last - self.t_first) if self.sent > 1 else 0.0
        r, e = np.array(self.render_ms[1:] or [0.0]), np.array(self.encode_ms[1:] or [0.0])
        return dict(stream_id=self.sid, name=self.name, resolution=[self.w, self.h], fps_target=self.fps,
                    workers=len(self.workers), port=self.port, frames_sent=self.sent, slots_dropped=self.dropped,
                    fps_achieved=(self.sent - 1) / el if el > 0 else None, render_ms_mean=float(r.mean()),
                    render_ms_max=float(r.max()), encode_ms_mean=float(e.mean()), encode_ms_max=float(e.max()),
                    rtp_packets=self.rtp.packets, rtp_bytes=self.rtp.bytes,
                    bitrate_achieved=8 * self.rtp.bytes / el if el > 0 else None)


class Camera:
    def __init__(self, a, streams, poses):
        self.a, self.streams, self.poses = a, streams, poses
        host, port = a.gcs.rsplit(":", 1)
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.sock.bind(("127.0.0.1", 0))
        self.log = open(a.log, "w", buffering=1) if a.log else None
        self.mav = Mav(self.sock, (host, int(port)), self.log)
        self.t0 = time.monotonic()
        self.requests = collections.Counter()

    def boot_ms(self):
        return int((time.monotonic() - self.t0) * 1000) & 0xFFFFFFFF

    def run(self):
        threading.Thread(target=self._heartbeat, daemon=True).start()
        while True:
            try:
                data, addr = self.sock.recvfrom(4096)
            except OSError:
                return
            for mid, sysid, compid, pl in parse(data):
                if mid == 76:
                    *prm, cmd, ts, tc, _ = struct.unpack(MSG[76][1], pl)
                elif mid == 75:
                    p1, p2, p3, p4, x, y, z, cmd, ts, tc, *_ = struct.unpack(MSG[75][1], pl)
                    prm = [p1, p2, p3, p4, x, y, z]
                else:
                    continue
                if ts == SYSID and tc == COMPID:
                    if self.log:
                        self.log.write(f"{time.time():.4f} < {mid} {sysid}/{compid} cmd {cmd} {[round(v, 3) for v in prm]}\n")
                    self.command(cmd, prm, sysid, compid)

    def _heartbeat(self):
        while True:
            self.mav.send(0, 0, 30, 8, 0, 4, 3)               # CAMERA, AUTOPILOT_INVALID, base 0, ACTIVE, v3
            time.sleep(1.0)

    def ack(self, cmd, result, sysid, compid):
        self.mav.send(77, cmd, result, 0, 0, sysid, compid)

    def command(self, cmd, prm, sysid, compid):
        legacy = {521: 259, 522: 260, 525: 261, 527: 262, 2504: 269, 2505: 270}
        if cmd == 512:
            msg, arg = int(prm[0]), int(prm[1])
        elif cmd in legacy:
            msg, arg = legacy[cmd], int(prm[0]) if cmd in (2504, 2505) else 0
        elif cmd in (2502, 2503):
            self.requests[cmd] += 1
            if self.a.rgb_gated is not None:                   # VIDEO_START/STOP_STREAMING, param1 = stream id (0: all)
                for s in self.streams:
                    if not s.thermal and int(prm[0]) in (0, s.sid):
                        s.on = cmd == 2502
            return self.ack(cmd, ACCEPTED, sysid, compid)
        else:
            self.requests[cmd] += 1
            return self.ack(cmd, UNSUPPORTED, sysid, compid)
        self.requests[(cmd, msg)] += 1
        send = {259: self.info, 260: self.settings, 261: self.storage, 262: self.capture,
                269: lambda: self.streams_info(arg), 270: lambda: self.streams_status(arg)}.get(msg)
        if send is None or (msg in (269, 270) and arg not in (0, *[s.sid for s in self.streams])):
            return self.ack(cmd, UNSUPPORTED, sysid, compid)
        self.ack(cmd, ACCEPTED, sysid, compid)
        send()

    def info(self):
        s = self.streams[0]
        self.mav.send(259, self.boot_ms(), 0, 3.2, 6.4, 4.8, 256, s.w, s.h, 0, b"leanfc sim", MODEL,
                      0, b"", 0, 0)

    def settings(self):
        self.mav.send(260, self.boot_ms(), 1, 0.0, float("nan"), 0)

    def storage(self):
        self.mav.send(261, self.boot_ms(), 0.0, 0.0, 0.0, 0.0, 0.0, 0, 0, 3, 0, b"", 0)

    def capture(self):
        self.mav.send(262, self.boot_ms(), 0.0, 0, 0.0, 0, 0, 0, 0)

    def streams_info(self, sid):
        for s in self.streams:
            if sid in (0, s.sid):
                self.mav.send(269, float(s.fps), int(s.bitrate), s.flags(), s.w, s.h, 0, int(round(s.hfov)), s.sid,
                              len(self.streams), 1, s.name.encode(), self.uri(s).encode(), 1, 0, 0)

    def uri(self, s):
        return str(s.port) if self.a.uri_form == "port" else f"udp://127.0.0.1:{s.port}"

    def streams_status(self, sid):
        for s in self.streams:
            if sid in (0, s.sid):
                self.mav.send(270, float(s.fps), int(s.bitrate), s.flags(), s.w, s.h, 0, int(round(s.hfov)), s.sid, 0, 0)

    def stats(self):
        return dict(streams=[s.stats() for s in self.streams], poses_received=self.poses.count,
                    requests={str(k): v for k, v in self.requests.items()}, uptime_s=time.monotonic() - self.t0)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--gcs", default="127.0.0.1:14550")
    ap.add_argument("--pose-port", type=int, default=14601)
    ap.add_argument("--rgb", default="640x480@10", help="WxH@FPS of the forward RGB stream")
    ap.add_argument("--rgb-workers", type=int, default=3)          # with --thermal-workers 1: 4 render processes
    ap.add_argument("--thermal-fps", type=float, default=8.7)
    ap.add_argument("--thermal", default="640x512", help="WxH of the thermal stream (the core is 640 x 512; 320x256 bins it 2 x 2)")
    ap.add_argument("--thermal-workers", type=int, default=1)
    ap.add_argument("--thermal-lod", type=int, default=2, help="camera_render.py --lod of the thermal workers (2: live level of detail)")
    ap.add_argument("--rgb-lod", type=int, default=2, help="camera_render.py --lod of the RGB workers (2: live level of detail)")
    ap.add_argument("--rgb-port", type=int, default=5600)
    ap.add_argument("--thermal-port", type=int, default=5602)
    ap.add_argument("--rgb-gated", choices=("on", "off"), default=None,
                    help="the RGB stream obeys VIDEO_START_STREAMING / VIDEO_STOP_STREAMING, starting on or off "
                         "(two vehicles' cameras can then share one RGB port: QGroundControl stops the old "
                         "active vehicle's stream and starts the new one's). Default: it runs continuously")
    ap.add_argument("--uri-form", choices=("url", "port"), default="url",
                    help="VIDEO_STREAM_INFORMATION uri: udp://127.0.0.1:PORT (default) or the bare port")
    ap.add_argument("--seed", type=int, default=0, help="thermal noise seed")
    ap.add_argument("--gorge-seed", type=int, default=7)
    ap.add_argument("--start", type=float, nargs=3, default=(0.0, 0.0, 0.0), help="ENU pose before the first one arrives")
    ap.add_argument("--sysid", type=int, default=1, help="MAVLink system id of the vehicle carrying the camera")
    ap.add_argument("--label", default="Forward", help="stream names: LABEL RGB, LABEL thermal")
    ap.add_argument("--stats", default=None, help="JSON statistics, rewritten every 5 s and at the end")
    ap.add_argument("--log", default=None, help="MAVLink log of the camera component")
    a = ap.parse_args()
    global SYSID, MODEL
    SYSID = a.sysid
    MODEL = b"gorge forward camera" if a.sysid == 1 else f"gorge forward camera {a.sysid}".encode()
    size, fps = a.rgb.split("@")
    w, h = map(int, size.split("x"))
    poses = Poses(a.pose_port, a.start)
    gs = ["--gorge-seed", str(a.gorge_seed)]
    rgb_workers = [Worker(["--kind", "rgb", "--width", str(w), "--height", str(h), "--lod", str(a.rgb_lod), *gs], w * h * 3)
                   for _ in range(a.rgb_workers)]
    tw, th = map(int, a.thermal.split("x"))
    th_workers = [Worker(["--kind", "thermal", "--seed", str(a.seed), "--width", str(tw), "--height", str(th),
                          "--lod", str(a.thermal_lod), *gs], tw * th * 3) for _ in range(a.thermal_workers)]
    for wk in rgb_workers + th_workers:
        wk.wait_ready()
    vsock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    streams = [Stream(1, f"{a.label} RGB", w, h, float(fps), 90.0, False, a.rgb_port, int(w * h * float(fps) * 0.33),
                      rgb_workers, poses, vsock),
               Stream(2, f"{a.label} thermal", tw, th, a.thermal_fps, 54.2, True, a.thermal_port, int(tw * th * a.thermal_fps * 0.15),
                      th_workers, poses, vsock)]
    if a.rgb_gated is not None:
        streams[0].on = a.rgb_gated == "on"
        streams[0].rtp.ssrc = 0x4C460000 | a.rgb_port          # one RTP source per port, whichever camera is sending
    cam = Camera(a, streams, poses)
    workers = rgb_workers + th_workers

    def stop(*_):
        for s in streams:
            s.running = False
        if a.stats:
            Path(a.stats).write_text(json.dumps(cam.stats(), indent=1) + "\n")
        for wk in workers:
            wk.p.kill()
        os._exit(0)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)

    def dump():
        while True:
            time.sleep(5.0)
            if a.stats:
                Path(a.stats).write_text(json.dumps(cam.stats(), indent=1) + "\n")
    if a.stats:
        threading.Thread(target=dump, daemon=True).start()
    for s in streams:
        s.start()
    print(f"camera component {SYSID}/100: MAVLink -> {a.gcs}; stream 1 RGB {w}x{h}@{fps} -> udp 127.0.0.1:{a.rgb_port} "
          f"({a.rgb_workers} workers); stream 2 thermal {tw}x{th}@{a.thermal_fps} -> udp 127.0.0.1:{a.thermal_port} "
          f"({a.thermal_workers} workers)", flush=True)
    cam.run()


if __name__ == "__main__":
    main()
