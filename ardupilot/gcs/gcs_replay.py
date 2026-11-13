#!/usr/bin/env python3
"""The byte replay of a recorded session on the translated GCS (README.md "Phase 4: GCS_MAVLink").

Usage: ardupilot/gcs/gcs_replay.py SESSION_DIR [EST]   (EST: the session's `copter_ref --est` file, default DIR/est.txt)

Prepares the schedule for lean/.lake/build/bin/gcs_replay from the session's inputs.txt, outputs.txt and est.txt (per
step: time, delay callbacks `dcb`, tasks 28/29 from `tasks=`, the recorded STATUSTEXT frames of the step, the uplink,
home from `home=`), the recorded frames by message id (the boundary frames' bytes) and the vehicle's answers (the
MAV_RESULT of the recorded COMMAND_ACK of DO_SET_MODE, COMPONENT_ARM_DISARM, NAV_TAKEOFF), runs it, and compares each
step's transmit bytes with the recorded `down=`: MAVLink frames in order (a byte not starting a frame is console text,
counted, not compared)."""
import collections, os, struct, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
NAMES = {0: "HEARTBEAT", 1: "SYS_STATUS", 2: "SYSTEM_TIME", 22: "PARAM_VALUE", 24: "GPS_RAW_INT", 27: "RAW_IMU",
         29: "SCALED_PRESSURE", 30: "ATTITUDE", 32: "LOCAL_POSITION_NED", 33: "GLOBAL_POSITION_INT", 36: "SERVO_OUTPUT_RAW",
         39: "MISSION_ITEM", 40: "MISSION_REQUEST", 42: "MISSION_CURRENT", 44: "MISSION_COUNT", 46: "MISSION_ITEM_REACHED",
         47: "MISSION_ACK", 49: "GPS_GLOBAL_ORIGIN", 51: "MISSION_REQUEST_INT", 62: "NAV_CONTROLLER_OUTPUT",
         65: "RC_CHANNELS", 73: "MISSION_ITEM_INT", 74: "VFR_HUD", 77: "COMMAND_ACK", 87: "POSITION_TARGET_GLOBAL_INT",
         111: "TIMESYNC", 125: "POWER_STATUS", 147: "BATTERY_STATUS", 148: "AUTOPILOT_VERSION", 152: "MEMINFO", 163: "AHRS",
         168: "WIND", 178: "AHRS2", 193: "EKF_STATUS_REPORT", 241: "VIBRATION", 242: "HOME_POSITION",
         245: "EXTENDED_SYS_STATE", 253: "STATUSTEXT", 435: "AVAILABLE_MODES", 437: "AVAILABLE_MODES_MONITOR"}


def frames(b):
    """[(offset, bytes, msgid)] and the number of other bytes."""
    out, other, i = [], 0, 0
    while i < len(b):
        if b[i] == 0xfd and i + 10 <= len(b):
            n = 12 + b[i + 1] + (13 if b[i + 2] & 1 else 0)
            out.append((i, b[i:i + n], b[i + 7] | b[i + 8] << 8 | b[i + 9] << 16))
            i += n
        elif b[i] == 0xfe and i + 6 <= len(b):
            n = 8 + b[i + 1]
            out.append((i, b[i:i + n], b[i + 5]))
            i += n
        else:
            other += 1
            i += 1
    return out, other


VEHICLE = 1 << 24


def vehicle_frame(b, mid):
    """A frame the vehicle's code makes the GCS send: PARAM_VALUE with param_index 65535 (AP_Param::notify ->
    GCS::send_parameter_value, after a set_and_save in vehicle code), STATUSTEXT (the vehicle's texts; sent at once by
    GCS::send_statustext until the vehicle is initialised, then by service_statustext)."""
    return (mid == 22 and len(b) >= 10 + 8 and b[10 + 6] == 0xff and b[10 + 7] == 0xff) or mid == 253


def field(line, key):
    for t in line.split():
        if t.startswith(key + "="):
            return t[len(key) + 1:]
    return None


def main():
    d = sys.argv[1]
    est = sys.argv[2] if len(sys.argv) > 2 else os.path.join(d, "est.txt")
    work = os.path.join(ROOT, "build", "gcs", "replay", os.path.basename(os.path.normpath(d)))
    os.makedirs(work, exist_ok=True)
    ins = open(os.path.join(d, "inputs.txt")).read().split("\n")[:-1]
    outs = open(os.path.join(d, "outputs.txt")).read().split("\n")[:-1]
    ests = [l for l in open(est).read().split("\n") if l and not l.startswith("#")]
    assert len(ins) == len(outs) == len(ests), (len(ins), len(outs), len(ests))
    rec = []
    fr = open(os.path.join(work, "frames.txt"), "w")
    answers = []
    cmds = []           # COMMAND_LONG commands in uplink order (the ACKs answer them in order)
    for k, (i, o, e) in enumerate(zip(ins, outs, ests)):
        down = bytes.fromhex(field(o, "down") or "")
        fs, other = frames(down)
        rec.append((fs, other))
        for _, b, mid in fs:
            if vehicle_frame(b, mid):
                mid = VEHICLE       # one queue of the vehicle frames, in order: a PARAM_VALUE of AP_Param's change notification (vehicle code's set_and_save)
            fr.write("%d %s\n" % (mid, struct.pack("<I", k + 1).hex() + b.hex()))     # the step, then the frame
            if mid == 77 and len(b) >= 10 + 3:
                cmd = b[10] | b[11] << 8
                res = b[12]
                key = {176: "set_mode", 400: "arm", 22: "takeoff"}.get(cmd)
                if key:
                    answers.append("%s %d" % (key, res))
    fr.close()
    open(os.path.join(work, "answers.txt"), "w").write("\n".join(answers) + "\n")
    with open(os.path.join(work, "schedule.txt"), "w") as f:
        for k, (i, e) in enumerate(zip(ins, ests)):
            t = field(i, "t")
            dcb = int(field(e, "dcb") or 0) if field(e, "init") == "1" else 0
            tasks = (field(e, "tasks") or "-").split(",")
            r28 = "1" if "28" in tasks else "0"
            s29 = "1" if "29" in tasks else "0"
            tq = 0      # STATUSTEXT: vehicle frames (below)
            vf = [vehicle_frame(b, m) for _, b, m in rec[k][0]]
            pre = 0
            while pre < len(vf) and vf[pre]:
                pre += 1
            post = sum(vf) - pre
            up = field(i, "up") or "-"
            h = (field(e, "home") or "0,0,0,0,0,0").split(",")
            home = "-"
            if h[0] == "1":
                # Location (clang's layout): flag bits at byte 0 (frame 0, ABSOLUTE: none), alt, lat, lng
                assert h[5] == "0"
                home = "00000000" + struct.pack("<iii", int(h[4]), int(h[2]), int(h[3])).hex()
            f.write("%d %s %d %s %s %d %s %s %d %d\n" % (k + 1, t, dcb, r28, s29, tq, up, home, pre, post))
    # the reference's parameters at the step before the first PARAM_REQUEST_LIST/READ is answered (the values non-GCS
    # code set since boot), from reference/hal/est_probe.cpp's CPP2LEAN_PARAM_SNAPSHOT (outputs unchanged)
    first_req = next((k for k, (fs, _) in enumerate(rec) if any(m == 22 and not vehicle_frame(b, m) for _, b, m in fs)), len(rec) - 1)
    # and at the end of boot (the calibrations of init_ardupilot: INS_GYROFFS_*), applied at the next step
    boot_end = next((k for k, e in enumerate(ests) if field(e, "init") == "0"), len(ests) - 1)
    snap = os.path.join(work, "param_snapshot.txt")
    with open(os.path.join(d, "inputs.txt")) as fi, open(os.devnull, "w") as fo, open(snap + ".err", "w") as fe:
        subprocess.run([os.path.join(ROOT, "build", "reference", "copter_ref"), "--storage", os.path.join(d, "storage_in.bin"),
                        "--est", os.devnull], stdin=fi, stdout=fo, stderr=fe,
                       env=dict(os.environ, CPP2LEAN_PARAM_SNAPSHOT=",".join(str(x) for x in [first_req, boot_end] + list(range(boot_end + 400, len(ests), 400)))))
    with open(snap + ".err") as f, open(snap, "w") as g:
        # the GCS's own parameters (MAVn_, MAV_) are not inputs: the translation sets them
        g.write("".join(l for l in f if l.startswith("paramsnap ") and not l.split()[2].startswith("MAV")))
    exe = os.path.join(ROOT, "lean", ".lake", "build", "bin", "gcs_replay")
    t0 = time.time()
    p = subprocess.run([exe, os.path.join(work, "schedule.txt"), os.path.join(work, "frames.txt"), os.path.join(work, "answers.txt"),
                        os.path.join(d, "storage_in.bin"), os.path.join(work, "lean_out.txt"), snap], capture_output=True, text=True)
    sys.stderr.write(p.stderr)
    lean = [l for l in open(os.path.join(work, "lean_out.txt")).read().split("\n") if l]
    head = [l for l in lean if l.startswith("#")]
    body = [l for l in lean if not l.startswith("#")]
    for l in head:
        print(l[:400])
    stats = collections.defaultdict(lambda: [0, 0, 0, 0, 0])   # per type: recorded, translated-equal, boundary-equal, different, missing/extra
    first = None
    nlines_eq = 0
    total_rec_bytes = total_cmp_bytes = 0
    text_rec = 0
    for k, l in enumerate(body):
        parts = l.split(" ")
        tx = bytes.fromhex(parts[1]) if parts[1] != "-" else b""
        bf = set(int(x) for x in parts[2].split(",")) if len(parts) > 2 and parts[2] else set()
        ours, _ = frames(tx)
        recd, other = rec[k]
        text_rec += other
        same_line = True
        for j in range(max(len(ours), len(recd))):
            o = ours[j] if j < len(ours) else None
            r = recd[j] if j < len(recd) else None
            mid = (r or o)[2]
            if r is not None:
                stats[mid][0] += 1
                total_rec_bytes += len(r[1])
            if o is not None and r is not None and o[1] == r[1]:
                stats[mid][2 if o[0] in bf else 1] += 1
                total_cmp_bytes += len(r[1])
            else:
                same_line = False
                if o is not None and r is not None:
                    stats[mid][3] += 1
                else:
                    stats[mid][4] += 1
                if first is None:
                    first = (k + 1, j, o, r, [NAMES.get(x[2], x[2]) for x in ours], [NAMES.get(x[2], x[2]) for x in recd])
        nlines_eq += same_line
    n = len(body)
    print("gcs replay %s: %d steps, %d steps whose frames are all equal" % (d, n, nlines_eq))
    rec_frames = sum(v[0] for v in stats.values())
    eq_t = sum(v[1] for v in stats.values())
    eq_b = sum(v[2] for v in stats.values())
    print("recorded frames %d (%d bytes; + %d console bytes not compared): equal %d (translated %d, boundary %d), different %d, missing or extra %d; equal bytes %d"
          % (rec_frames, total_rec_bytes, text_rec, eq_t + eq_b, eq_t, eq_b, sum(v[3] for v in stats.values()), sum(v[4] for v in stats.values()), total_cmp_bytes))
    for mid, v in sorted(stats.items(), key=lambda x: -x[1][0]):
        print("  %-24s recorded %5d  translated-equal %5d  boundary-equal %5d  different %5d  missing/extra %5d" % (NAMES.get(mid, mid), *v))
    # the parameter download by index (independent of timing): name, value bits, type and count of every PARAM_VALUE
    def params(frs):
        d = {}
        for b in frs:
            pl = b[10:10 + b[1]] + bytes(25)
            idx = pl[6] | pl[7] << 8
            if idx == 0xffff:
                continue
            d.setdefault(idx, (pl[8:24].split(b"\0")[0].decode(errors="replace"), pl[0:4].hex(), pl[24], pl[4] | pl[5] << 8))
        return d
    ours_p = params([f[1] for l in body for f in frames(bytes.fromhex(l.split(" ")[1]) if l.split(" ")[1] != "-" else b"")[0] if f[2] == 22])
    rec_p = params([f[1] for fs, _ in rec for f in fs if f[2] == 22])
    same = sum(1 for i in rec_p if ours_p.get(i) == rec_p[i])
    print("parameter download by index: recorded %d indices (count %s), translation %d (count %s); equal (name, value, type, count) %d" % (
        len(rec_p), sorted(set(v[3] for v in rec_p.values())), len(ours_p), sorted(set(v[3] for v in ours_p.values())), same))
    firstp = next((i for i in sorted(rec_p) if ours_p.get(i) != rec_p[i]), None)
    if firstp is not None:
        print("  first different index %d: recorded %s, translation %s" % (firstp, rec_p[firstp], ours_p.get(firstp)))
    # the storage at the end against the reference's (copter_ref --storage-out on the whole session)
    ref_st = os.path.join(work, "ref_storage.bin")
    with open(os.path.join(d, "inputs.txt")) as fi, open(os.devnull, "w") as fo:
        subprocess.run([os.path.join(ROOT, "build", "reference", "copter_ref"), "--storage", os.path.join(d, "storage_in.bin"),
                        "--storage-out", ref_st], stdin=fi, stdout=fo, stderr=subprocess.DEVNULL)
    a = open(os.path.join(work, "lean_out.txt.storage"), "rb").read()
    b = open(ref_st, "rb").read()
    boot = open(os.path.join(d, "storage_in.bin"), "rb").read()
    MIS = [(1536, 2422), (5932, 2132), (10028, 5204)]      # StorageManager's StorageMission areas (Phase 2b)
    inm = lambda j: any(o <= j < o + n for o, n in MIS)
    dif = [j for j in range(len(b)) if a[j] != b[j]]
    print("storage at the end: mission areas %d bytes, %d differ (the reference changed %d of them); outside them %d bytes differ "
          "(the reference changed %d bytes there since boot); differing offsets outside: %s" % (
              sum(n for _, n in MIS), sum(1 for j in dif if inm(j)), sum(1 for j in range(len(b)) if inm(j) and b[j] != boot[j]),
              sum(1 for j in dif if not inm(j)), sum(1 for j in range(len(b)) if not inm(j) and b[j] != boot[j]),
              [j for j in dif if not inm(j)][:24]))
    if first:
        k, j, o, r, os_, rs = first
        print("first difference: step %d (input line %d), frame %d of the step" % (k, k, j))
        print("  translation's frames: %s" % os_)
        print("  recorded frames:      %s" % rs)
        print("  translation: %s" % (o[1].hex() if o else None))
        print("  recorded:    %s" % (r[1].hex() if r else None))


if __name__ == "__main__":
    main()
