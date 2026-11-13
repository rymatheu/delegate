#!/usr/bin/env python3
"""(Phase 5d) A scripted ground station on QGroundControl's UDP port, for checking the live launch path of
sim/run_qgc_reference.py without QGroundControl (`--gcs scripted`). Harness code.

Listens on 127.0.0.1:14550 as QGroundControl does (fly_reference.py --udp sends the vehicle's downlink there and takes
the uplink from the datagrams' source), waits for the vehicle's HEARTBEAT, then sends its own HEARTBEAT once a second
and one PARAM_REQUEST_LIST, and reports after --seconds of real time: heartbeats received, the vehicle's mode and
system status, the first STATUSTEXTs, PARAM_VALUEs received (with the vehicle's parameter count). Exit status 0 when a
heartbeat and at least one PARAM_VALUE arrived.

Usage: build/reference/venv/bin/python sim/udp_gcs_check.py [--seconds S] [--port P]
"""
import argparse
import socket
import sys
import time

from pymavlink.dialects.v20 import ardupilotmega as m


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seconds", type=float, default=8.0)
    ap.add_argument("--port", type=int, default=14550)
    a = ap.parse_args()
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.bind(("127.0.0.1", a.port))
    sock.settimeout(0.05)

    class Sink:
        buf = b""

        def write(self, b):
            Sink.buf += b
    mav = m.MAVLink(Sink(), srcSystem=255, srcComponent=190)
    parser = m.MAVLink(None)
    parser.robust_parsing = True
    peer = None
    t0 = time.time()
    t_hb = -1.0
    asked = None
    first_hb = None
    hb = 0
    pv = 0
    count = None
    names = []
    texts = []
    last = None
    while time.time() - t0 < a.seconds:
        try:
            data, addr = sock.recvfrom(65536)
            peer = addr
            for msg in parser.parse_buffer(data) or []:
                typ = msg.get_type()
                if typ == "HEARTBEAT" and msg.get_srcComponent() == 1:
                    hb += 1
                    last = msg
                    if first_hb is None:
                        first_hb = time.time() - t0
                elif typ == "PARAM_VALUE":
                    pv += 1
                    count = msg.param_count
                    if len(names) < 5:
                        names.append("%s=%g" % (msg.param_id, msg.param_value))
                elif typ == "STATUSTEXT" and len(texts) < 6:
                    texts.append(msg.text)
        except socket.timeout:
            pass
        now = time.time() - t0
        if peer is not None and now - t_hb >= 1.0:
            t_hb = now
            mav.heartbeat_send(m.MAV_TYPE_GCS, m.MAV_AUTOPILOT_INVALID, 0, 0, m.MAV_STATE_ACTIVE)
            if first_hb is not None and asked is None:
                mav.param_request_list_send(1, 1)
                asked = now
            sock.sendto(Sink.buf, peer)
            Sink.buf = b""
    print("scripted GCS on udp 127.0.0.1:%d for %.1f s: vehicle at %s" % (a.port, a.seconds, peer))
    print("heartbeats received: %d (first after %s s)%s" % (hb, "%.2f" % first_hb if first_hb is not None else "-",
          "; last: custom_mode %d, system_status %d, base_mode %d" % (last.custom_mode, last.system_status, last.base_mode) if last else ""))
    print("PARAM_REQUEST_LIST sent at %s s; PARAM_VALUE received: %d (vehicle's count %s); first: %s"
          % ("%.2f" % asked if asked is not None else "-", pv, count, ", ".join(names)))
    print("STATUSTEXT: %s" % texts)
    sys.exit(0 if hb and pv else 1)


if __name__ == "__main__":
    main()
