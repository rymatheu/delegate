#!/usr/bin/env python3
"""Coverage of the AP_Motors difftest (after `python3 difftest.py ardupilot/AP_Motors`): for each run,
the calls of output() by spool state, how many in THROTTLE_UNLIMITED ran without any limit flag,
the frames flown, and the boundary calls recorded. Reads build/ and the signatures."""
import json
import os
import struct
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
B = os.path.join(HERE, "..", "build")
sig = json.load(open(os.path.join(HERE, "out", "AP_Motors", "AP_Motors_lib.signatures.json")))
cfg = json.load(open(os.path.join(HERE, "AP_Motors.json")))
c = next(c for c in sig["classes"] if c["cxx"] == "AP_MotorsMatrix")
names = [l["lean"] for l in c["leaves"]]
dec = lambda s: bytes.fromhex(s[2:]).decode() if s[2:] else ""
f32 = lambda t: struct.unpack(">f", bytes.fromhex(t[2:]))[0]
for cc in cfg["classes"]:
    run = cc["run"]
    lines = open(os.path.join(B, "AP_Motors_lib_AP_Motors_lib_AP_MotorsMatrix_%s.cpp.out" % run)).read().splitlines()
    spool, frames, ev = Counter(), Counter(), Counter()
    n = unsat = 0
    acts = set()
    for L in lines[1:]:
        a, b = L.split(" | ", 1)
        toks = b.split()
        d = dict(zip(names, toks))
        ev.update(t for t in toks[len(names):] if t.startswith("e:"))
        if a.split()[1] == "AP_MotorsMatrix.output":
            spool[d["_spool_state"]] += 1
            if d["_spool_state"] == "i:3":
                n += 1
                if not any(d[k] == "b:1" for k in ("limit.roll", "limit.pitch", "limit.yaw", "limit.throttle_upper", "limit.throttle_lower")):
                    unsat += 1
                frames["%s/%s" % (dec(d["_frame_class_string"]), dec(d["_frame_type_string"]))] += 1
                acts.update(d["_actuator[%d]!" % k] for k in range(12))
    print("%s: output() by spool state %s; in THROTTLE_UNLIMITED %d, of which %d without a limit flag; %d distinct actuator values"
          % (run, ", ".join("%s %d" % (["SHUT_DOWN", "GROUND_IDLE", "SPOOLING_UP", "THROTTLE_UNLIMITED", "SPOOLING_DOWN"][int(k[2:])], v)
                            for k, v in sorted(spool.items())), n, unsat, len(acts)))
    print("  frames flown: %s" % ", ".join("%s %d" % kv for kv in sorted(frames.items())))
    print("  boundary calls: %s" % ", ".join("%s %d" % (k[2:], v) for k, v in sorted(ev.items())))
