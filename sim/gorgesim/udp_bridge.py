"""Real-time UDP bridge of a lock-step vehicle's SERIAL0 to a ground station (QGroundControl), for the real-time
sessions of the flight programs (for example ardulean/sim/fly_gorge.py --udp).

Each vehicle has its own UDP socket bound to 127.0.0.1 on a free port; its downlink bytes of a step are sent as one
datagram to the ground station (127.0.0.1:PORT, QGroundControl's 14550 by default), and every datagram received on the
socket before a step goes into that step's input line (`up`). QGroundControl answers each vehicle at the address its
datagrams came from, so several vehicles share its one port when each has its own socket and its own MAVLink system id.
`Pacer` holds the loop to the wall clock: step k (0-based) ends no earlier than w0 + (k + 1) x the step period; when a
step is late nothing is dropped, the following steps run without waiting until the loop has caught up.

`PoseSender` publishes a vehicle's true pose for its camera (sim/world/camera_component.py, started by sim/cameras.sh):
one datagram of POSE_FMT to 127.0.0.1:PORT, sent without waiting (lost when nobody listens). It reads only state the
harness already has and changes nothing the vehicle sees, so the lock-step record is the same with and without it.
"""
import socket
import struct
import time

POSE_FMT = struct.Struct("<Idd3d4d")    # sequence, simulated time (s), wall time (time.time), ENU position (m), PyBullet quaternion x, y, z, w


class UdpBridge:
    def __init__(self, port=14550, host="127.0.0.1"):
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.sock.bind((host, 0))
        self.sock.setblocking(False)
        self.gcs_addr = (host, port)
        self.addr = self.sock.getsockname()     # the vehicle's address, as the ground station sees it
        self.sent = self.received = 0

    def send(self, down: bytes):
        """The downlink bytes of one step, as one datagram (nothing when empty)."""
        if down:
            try:
                self.sock.sendto(down, self.gcs_addr)
                self.sent += 1
            except OSError:
                pass                       # no ground station yet: the datagram is lost, as on a radio link

    def receive(self) -> bytes:
        """Every datagram waiting on the socket, concatenated (the next input line's uplink)."""
        chunks = []
        while True:
            try:
                data, _ = self.sock.recvfrom(65536)
            except (BlockingIOError, InterruptedError):
                break
            except OSError:
                break
            chunks.append(data)
        self.received += len(chunks)
        return b"".join(chunks)

    def close(self):
        self.sock.close()


class Pacer:
    """Wall-clock pacing of a loop of fixed steps; records how late the steps end."""

    def __init__(self, step_s: float):
        self.step_s = step_s
        self.w0 = time.perf_counter()
        self.late_max = 0.0
        self.late_steps = 0
        self.lag = 0.0
        self.t_prev = self.w0
        self.work = []                     # per step: wall time from the end of the previous wait to this one (s)

    def wait(self, k: int):
        """Wait until the end of step k (0-based) in wall time."""
        target = self.w0 + (k + 1) * self.step_s
        now = time.perf_counter()
        self.work.append(now - self.t_prev)
        self.lag = now - target
        if self.lag > 0:
            self.late_steps += 1
            self.late_max = max(self.late_max, self.lag)
            self.t_prev = now
            return
        while True:
            now = time.perf_counter()
            if now >= target:
                break
            time.sleep(min(0.002, target - now))
        self.t_prev = now

    def summary(self, steps: int) -> str:
        wall = time.perf_counter() - self.w0
        sim = steps * self.step_s
        w = sorted(self.work) or [0.0]
        q = lambda f: w[min(len(w) - 1, int(f * len(w)))] * 1e3
        return (f"real time: {sim:.2f} s simulated in {wall:.2f} s wall (simulated time behind wall time at the end by "
                f"{wall - sim:.3f} s); steps ending late {self.late_steps} of {steps}, latest by {self.late_max * 1e3:.1f} ms; "
                f"step work (simulator, vehicles, bridge; period {self.step_s * 1e3:g} ms) mean "
                f"{sum(w) / len(w) * 1e3:.3f} ms, p50 {q(0.5):.3f}, p99 {q(0.99):.3f}, max {w[-1] * 1e3:.3f} ms")


class PoseSender:
    """The true pose of one vehicle, for its camera: a datagram per call, never blocking."""

    def __init__(self, port, host="127.0.0.1"):
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.sock.setblocking(False)
        self.addr = (host, port)
        self.seq = self.sent = 0

    def send(self, t_sim: float, pos, quat):
        self.seq += 1
        try:
            self.sock.sendto(POSE_FMT.pack(self.seq, t_sim, time.time(), *pos, *quat), self.addr)
            self.sent += 1
        except OSError:
            pass                       # no camera listening (yet): the pose is lost, the next one follows

    def close(self):
        self.sock.close()
