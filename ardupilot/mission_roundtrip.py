#!/usr/bin/env python3
"""The mission round trip of a recorded flight against the reference (README.md "Phase 4: AP_Mission"): the translated
MAVLink library and AP_Mission (lean/MissionRoundTrip.lean) take the flight's uplink and do what the vehicle does with
the mission, and their results are compared with the reference's.

What the check does (the Lean program, `mission_roundtrip`):
  - boots the mission from the flight's boot image (`storage_in.bin`) with the translated `AP_Mission::init`, MIS_TOTAL
    at its boot value (the value the vehicle sent in the parameter download, PARAM_VALUE "MIS_TOTAL": AP_Param's load is
    not part of this slice);
  - does what AP_AHRS::set_home does to the mission (AP_AHRS.cpp:1787, `AP::mission().write_home_to_storage()`) at every
    step where the reference's home changes (est.txt `home=`), with that home as the `get_home` input;
  - parses the uplink bytes (inputs.txt `up=`) with the translated `mavlink_parse_char` (channel 0) and, for the mission
    messages, does what MissionItemProtocol / MissionItemProtocol_Waypoints do (GCS_MAVLink/MissionItemProtocol.cpp,
    MissionItemProtocol_Waypoints.cpp, not translated: the GCS layer is the coordinator's): MISSION_COUNT `truncate`,
    MISSION_ITEM_INT `mavlink_int_to_mission_cmd` then `replace_cmd` (seq below the count) or `add_cmd` (seq equal to
    it), MISSION_CLEAR_ALL `clear`, MISSION_REQUEST_INT `read_cmd_from_storage` + `mission_cmd_to_mavlink_int` (with
    get_item's `mission_type` and `current`), printing the item;
  - prints the storage image at the end and after the last mission message.

Compared (this script):
  - each item the Lean side answers with, against the payload of the MISSION_ITEM_INT the reference sent (zero-extended
    to 38 bytes), every byte but target_system/target_component (set by the GCS layer from the request);
  - the storage after the last mission message, against the reference's storage after the same input line (the trace
    replayed up to that line: `copter_ref --storage storage_in.bin --storage-out F`): the mission areas, and the whole image;
  - the storage at the end of the flight, against the reference's at the end (the whole trace).

Usage: python3 ardupilot/mission_roundtrip.py [FLIGHT_DIR (default sim/out/lockstep-flight)] [--keep]
"""
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
REF = os.path.join(ROOT, "build", "reference")
VENV_SITE = os.path.join(REF, "venv", "lib", "python3.12", "site-packages")
MISSION_AREAS = [(1536, 2422), (5932, 2132), (10028, 5204)]     # StorageManager's layout for StorageMission (Phase 2b)
MISSION_MSGS = {44, 45, 51, 73, 40, 39}     # MISSION_COUNT, CLEAR_ALL, REQUEST_INT, ITEM_INT, REQUEST, ITEM


def mission_bytes(img):
    return b"".join(img[o:o + n] for o, n in MISSION_AREAS)


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    flight = os.path.join(ROOT, args[0] if args else "sim/out/lockstep-flight")
    sys.path.insert(0, VENV_SITE)
    from pymavlink.dialects.v20 import all as mavall
    with open(os.path.join(flight, "inputs.txt")) as f:
        inputs = f.read().splitlines()
    ups = []                    # (input line index, t, uplink bytes)
    for i, l in enumerate(inputs):
        t = int(l.split()[0][2:])
        for tok in l.split():
            if tok.startswith("up="):
                ups.append((i, t, bytes.fromhex(tok[3:])))
    # the downlink: every message the reference sent, in order
    mav = mavall.MAVLink(None)
    mav.robust_parsing = True
    items, mis_total = [], None
    with open(os.path.join(flight, "outputs.txt")) as f:
        for l in f:
            for tok in l.split():
                if tok.startswith("down="):
                    for m in mav.parse_buffer(bytes.fromhex(tok[5:])) or []:
                        if m.get_type() == "MISSION_ITEM_INT":
                            buf = m.get_msgbuf()
                            items.append(bytes(buf[10:10 + buf[1]]).ljust(38, b"\0"))
                        if m.get_type() == "PARAM_VALUE" and m.param_id == "MIS_TOTAL" and mis_total is None:
                            mis_total = int(m.param_value)
    if mis_total is None:
        sys.exit("mission_roundtrip: no PARAM_VALUE MIS_TOTAL in the downlink")
    # which uplink lines carry mission messages (the last one bounds the storage comparison)
    parser = mavall.MAVLink(None)
    parser.robust_parsing = True
    last_mission_line = None
    for i, t, b in ups:
        for m in parser.parse_buffer(b) or []:
            if m.get_msgId() in MISSION_MSGS:
                last_mission_line = i
    # home changes (est.txt `home=<set>,<locked>,<lat>,<lng>,<alt>,<frame>`)
    homes, prev = [], None
    with open(os.path.join(flight, "est.txt")) as f:
        for l in f:
            if not l.startswith("t="):
                continue
            t = int(l[2:l.index(" ")])
            k = l.index(" home=") + 6
            h = l[k:l.index(" ", k)]
            if h != prev:
                prev = h
                s, _lk, lat, lng, alt, frame = (int(x) for x in h.split(","))
                if s:
                    if frame != 0:
                        sys.exit("mission_roundtrip: home in frame %d (only absolute altitudes are handled)" % frame)
                    homes.append((t, lat, lng, alt))
    tmp = tempfile.mkdtemp(prefix="mission_rt_")
    ev = os.path.join(tmp, "events.txt")
    with open(ev, "w") as f:
        f.write("total %d\n" % mis_total)
        evs = [(t, 0, "home %d %d %d %d" % (t, lat, lng, alt)) for t, lat, lng, alt in homes] + \
              [(t, 1, "up %d %d %s" % (t, i, b.hex())) for i, t, b in ups]
        for _, _, e in sorted(evs, key=lambda x: (x[0], x[1])):
            f.write(e + "\n")
        f.write("mark %d\n" % last_mission_line)
    exe = os.path.join(ROOT, "lean", ".lake", "build", "bin", "mission_roundtrip")
    p = subprocess.run([exe, os.path.join(flight, "storage_in.bin"), ev], stdout=subprocess.PIPE, text=True, check=True)
    out = p.stdout.splitlines()
    lean_items = [bytes.fromhex(l.split()[2]) for l in out if l.startswith("item ")]
    lean_mark = bytes.fromhex(next(l.split()[1] for l in out if l.startswith("storage_mark ")))
    lean_end = bytes.fromhex(next(l.split()[1] for l in out if l.startswith("storage_end ")))
    for l in out:
        if not l.startswith(("item ", "storage_")):
            print("lean: " + l)
    # the reference's storage after the last mission message and at the end
    def ref_storage(nlines):
        so = os.path.join(tmp, "ref_%d.bin" % nlines)
        with open(os.devnull, "w") as dn:
            subprocess.run([os.path.join(REF, "copter_ref"), "--storage", os.path.join(flight, "storage_in.bin"), "--storage-out", so],
                           input="\n".join(inputs[:nlines]) + "\n", stdout=dn, text=True, check=True)
        with open(so, "rb") as f:
            return f.read()
    ref_mark, ref_end = ref_storage(last_mission_line + 1), ref_storage(len(inputs))
    with open(os.path.join(flight, "storage_in.bin"), "rb") as f:
        boot = f.read()
    bad = 0
    # items: every byte but target_system, target_component (32, 33)
    print("items: Lean %d, reference downlink %d" % (len(lean_items), len(items)))
    if len(lean_items) != len(items):
        bad += 1
    for k, (a, b) in enumerate(zip(lean_items, items)):
        diff = [j for j in range(38) if j not in (32, 33) and a[j] != b[j]]
        print("  item %d: %s (command %d, frame %d, x %d, y %d)" % (k, "36 compared bytes equal" if not diff else "bytes %s differ" % diff,
              int.from_bytes(b[30:32], "little"), b[34], int.from_bytes(b[16:20], "little", signed=True),
              int.from_bytes(b[20:24], "little", signed=True)))
        bad += bool(diff)
    def cmp(label, a, b):
        ma, mb = mission_bytes(a), mission_bytes(b)
        dm = sum(1 for x, y in zip(ma, mb) if x != y)
        dw = [j for j in range(len(a)) if a[j] != b[j]]
        changed = sum(1 for x, y in zip(mission_bytes(boot), mb) if x != y)
        print("%s: mission areas %d bytes, %d differ (the reference changed %d of them since boot); whole image %d of %d bytes differ%s" %
              (label, len(ma), dm, changed, len(dw), len(a), (" (offsets %d-%d)" % (dw[0], dw[-1])) if dw else ""))
        return dm, dw
    dm, dw = cmp("storage after the last mission message (input line %d)" % (last_mission_line + 1), lean_mark, ref_mark)
    bad += dm
    if dw:
        outside = [j for j in dw if not any(o <= j < o + n for o, n in MISSION_AREAS)]
        print("  outside the mission areas: %d bytes differ, %d of them where the reference's image differs from the boot image "
              "(AP_Param's saves: `set_and_save` of MIS_TOTAL and the vehicle's own, not modelled here)" %
              (len(outside), sum(1 for j in outside if ref_mark[j] != boot[j])))
    dm2, dw2 = cmp("storage at the end of the flight", lean_end, ref_end)
    bad += dm2
    if dw2:
        # outside the mission areas: what else the flight wrote (AP_Param's saves), not part of this check
        outside = [j for j in dw2 if not any(o <= j < o + n for o, n in MISSION_AREAS)]
        print("  outside the mission areas: %d bytes differ, %d of them where the reference's image differs from the boot image" %
              (len(outside), sum(1 for j in outside if ref_end[j] != boot[j])))
    if "--keep" not in sys.argv:
        for x in os.listdir(tmp):
            os.unlink(os.path.join(tmp, x))
        os.rmdir(tmp)
    print("mission round trip: %s" % ("all equal" if not bad else "%d differences" % bad))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
