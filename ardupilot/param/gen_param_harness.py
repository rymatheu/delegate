#!/usr/bin/env python3
"""Data of the Lean AP_Param harnesses (README.md, "Phase 4: AP_Param"), generated from the translation's address map
(ardupilot/out/AP_Param/AP_Param_lib.addresses.json) and clang:

  - `ctorDefaults`: the static objects' constructors' calls `AP_Param::setup_object_defaults(this, var_info)`, as
    (object address, table address) pairs: every group of the parameter tree reached from Copter::var_info through
    non-pointer entries (GOBJECT/GGROUP/GOBJECTN, AP_NESTEDGROUPINFO, AP_SUBGROUPINFO, AP_SUBGROUPEXTENSION), in the
    tree's order. Pointer groups (GOBJECTPTR, AP_SUBGROUPPTR, *VARPTR) are null before allocate_motors and are left out.
  - `paramLoader`: the address of `copter.param_loader` (its constructor `AP_Param(var_info)` sets `_var_info`).
  - `estParams`: for every parameter path of the estimator World that the reference's probe prints (`# params`, the
    replay's parameters: reference/hal/est_probe.cpp), its address in the parameter memory and its C++ value type
    (offsets and types by clang: `__builtin_offsetof(Copter, <path>)` / `__builtin_offsetof(NavEKF3, <path>)` and the
    type of `<path>.get()`, evaluated in a generated unit with the flags of ArduCopter/Parameters.cpp's unit and
    -fno-access-control); also written as ardupilot/out/AP_Param/estimator_params.json (the address map of the bridge to
    the estimator World's paths, for Phase 5's dispatch from addresses to World paths).

Usage: ardupilot/param/gen_param_harness.py EST_TRACE   (a `copter_ref --est` trace whose first line is `# params`)
Output: lean/ParamHarnessData.lean, ardupilot/out/AP_Param/estimator_params.json
"""
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, ROOT)
import cpp2lean_mem as M  # noqa: E402
import memir  # noqa: E402

AMAP = os.path.join(ROOT, "ardupilot", "out", "AP_Param", "AP_Param_lib.addresses.json")
# Phase 4 GCS (README.md "Phase 4: GCS_MAVLink"): PARAM_HARNESS_TARGET=gcs writes the same data for the GCS
# translation's memory image (GCS_lib's addresses) into lean/GCSHarnessData.lean, with the GCS objects' offsets
GCS = os.environ.get("PARAM_HARNESS_TARGET") in ("gcs", "vehicle")
if GCS:
    AMAP = os.path.join(ROOT, "ardupilot", "out", "GCS", "GCS_lib.addresses.json")
# Phase 5 (README.md "Phase 5: the estimator bridge"): PARAM_HARNESS_TARGET=vehicle writes the same data for the vehicle
# translation's image (Vehicle_lib's addresses) into lean/VehicleHarnessData.lean, the bridged fields' address map
# ardupilot/out/Vehicle/estimator_params.json (support/gen_param_memory_v.py --bridge) and the estimator objects'
# addresses ardupilot/out/Vehicle/bridge_objects.json (ardupilot/vehicle/gen_bridge.py's accessors)
VEHICLE = os.environ.get("PARAM_HARNESS_TARGET") == "vehicle"
if VEHICLE:
    AMAP = os.path.join(ROOT, "ardupilot", "out", "Vehicle", "Vehicle_lib.addresses.json")
BRIDGE_OBJECTS = ["ahrs", "ins", "gps", "barometer", "compass", "rtc"]   # (Phase 5c) rtc: BRD_RTC_TYPES, BRD_RTC_TZ_MIN
# (Phase 5c) the member path of an estimator object that is not a direct member of Copter (AP_RTC: AP_BoardConfig's `rtc`,
# the BRD_RTC_ subgroup)
BRIDGE_MEMBER = {"rtc": "BoardConfig.rtc"}
# the parameter objects Copter::allocate_motors allocates at run time (system.cpp:357-505): (pointer member of Copter,
# class, table, the var_info pointer member for GOBJECTVARPTR or None)
RUNTIME = [("motors", "AP_MotorsMatrix", "AP_MotorsMulticopter::var_info", "motors_var_info"),
           ("attitude_control", "AC_AttitudeControl_Multi", "AC_AttitudeControl_Multi::var_info", "attitude_control_var_info"),
           ("pos_control", "AC_PosControl", "AC_PosControl::var_info", None),
           ("wp_nav", "AC_WPNav", "AC_WPNav::var_info", None),
           ("loiter_nav", "AC_Loiter", "AC_Loiter::var_info", None),
           ("circle_nav", "AC_Circle", "AC_Circle::var_info", None)]


def subtree(objs, tab0):
    """[(offset within the object, table)] of the object whose table is tab0 and its non-pointer groups."""
    tabs = {o["addr"]: bytes.fromhex(o["bytes"]) for o in objs if o["kind"] == "table"}
    out = []

    def group(off, tab):
        if (off, tab) not in out:
            out.append((off, tab))
        b = tabs[tab]
        for i in range(len(b) // 32):
            e = b[32 * i:32 * i + 32]
            flags, typ = int.from_bytes(e[24:26], "little"), e[27]
            if typ == 0:
                break
            if typ != 6 or flags & 16 or flags & 2:
                continue
            sub = int.from_bytes(e[16:24], "little")
            if sub == 0 or sub not in tabs:
                continue
            group(off + (int.from_bytes(e[8:16], "little", signed=True) if flags & 1 else 0), sub)
    group(0, tab0)
    return out


GCS_EXPRS = [("gcs_obj", ["__builtin_offsetof(Copter, _gcs)"]),
             ("gcs_fields", ["__builtin_offsetof(GCS, _num_gcs)", "__builtin_offsetof(GCS, _chan)",
                             "sizeof(GCS_MAVLINK_Copter)", "__builtin_offsetof(GCS_MAVLINK, _channel_status.current_tx_seq)",
                             "__builtin_offsetof(GCS_MAVLINK, chan)", "sizeof(Location)"]),
             ("mission_obj", ["__builtin_offsetof(Copter, mode_auto.mission)"])]
# the probe's objects (est_probe.cpp: AP::baro() ... are members of copter; NavEKF3 is AP_AHRS_NavEKF3's static EKF3)
# constructors of objects outside the parameter tree that call setup_object_defaults: AP_GPS's `Params
# params[GPS_MAX_INSTANCES]` has 3 elements, each constructed by AP_GPS::Params::Params (AP_GPS_Params.cpp:119-122,
# setup_object_defaults(this, var_info)), and AP_GPS::var_info has entries for the first GPS_MAX_RECEIVERS (2) only
EXTRA_CTORS = [("gps.params[2]", "AP_GPS::Params::var_info")]
ROOTS = {"barometer": ("copter", "Copter", "barometer."), "compass": ("copter", "Copter", "compass."),
         "ins": ("copter", "Copter", "ins."), "gps": ("copter", "Copter", "gps."), "ahrs": ("copter", "Copter", "ahrs."), "rtc": ("copter", "Copter", "BoardConfig.rtc."),
         "EKF3": ("AP_AHRS_NavEKF3::EKF3", "NavEKF3", "")}


def tree(objs, ptr_cells=None):
    ptr_cells = ptr_cells or {}
    tabs = {o["addr"]: bytes.fromhex(o["bytes"]) for o in objs if o["kind"] == "table"}
    root = next(o for o in objs if o["name"] == "Copter::var_info")
    out = []

    def u64(b, o, signed=False):
        return int.from_bytes(b[o:o + 8], "little", signed=signed)

    def group(obj, tab):
        if (obj, tab) not in out:
            out.append((obj, tab))
        b = tabs[tab]
        for i in range(len(b) // 32):
            e = b[32 * i:32 * i + 32]
            flags, typ = int.from_bytes(e[24:26], "little"), e[27]
            if typ == 0:
                break
            if typ != 6 or flags & 16:
                continue
            sub = u64(e, 16)
            if sub == 0 or sub not in tabs:
                continue
            if flags & 2:
                cell = obj + u64(e, 8, True)
                if cell in ptr_cells:       # a pointer member a constructor sets to a static object
                    group(ptr_cells[cell], sub)
                continue
            group(obj + (u64(e, 8, True) if flags & 1 else 0), sub)
    b = tabs[root["addr"]]
    for i in range(len(b) // 32):
        e = b[32 * i:32 * i + 32]
        flags, typ = int.from_bytes(e[24:26], "little"), e[28]
        if typ == 0:
            break
        if typ != 6 or flags & 2 or flags & 16:
            continue
        group(u64(e, 8), u64(e, 16))
    return out


def clang_values(exprs):
    """{name: [values]} of `extern "C" const long name[] = {...}` evaluated by clang in Parameters.cpp's unit."""
    units = M.Units(ROOT, os.path.join(ROOT, "build", "param-memory-cache"))
    src = os.path.join(ROOT, "build", "param-memory-cache", "param_offsets.cpp")
    body = ['#include "../../ArduCopter/Copter.h"', "#include <type_traits>"] + (["#include <AP_BattMonitor/AP_BattMonitor_Analog.h>"] if GCS else []) + [
            "template <typename T, bool E = std::is_enum<T>::value> struct PK { static const long v = std::is_floating_point<T>::value ? 2 : (std::is_signed<T>::value ? 1 : 0); };",
            "template <typename T> struct PK<T, true> { static const long v = std::is_signed<typename std::underlying_type<T>::type>::value ? 1 : 0; };",
            "#define PT(e) typename std::remove_cv<typename std::remove_reference<decltype(e)>::type>::type"]
    for k, (n, vals) in enumerate(exprs):
        body.append('extern "C" const long pq_%d[] = {%s};' % (k, ", ".join("(long)(%s)" % v for v in vals)))
    text = "\n".join(body) + "\n"
    if not os.path.exists(src) or open(src).read() != text:
        with open(src, "w") as f:
            f.write(text)
    out = src + ".ll"
    fl = units.flags("ArduCopter/Parameters.cpp") + ["-fno-access-control"]
    p = subprocess.run(["clang++"] + fl + ["-O0", "-S", "-emit-llvm", "-o", out, src], cwd=str(units.b.WAF), capture_output=True, text=True)
    if p.returncode != 0:
        sys.exit(p.stderr[-4000:])
    mod = memir.Module(open(out).read())
    res = {}
    for k, (n, vals) in enumerate(exprs):
        g = mod.get("@pq_%d" % k)
        res[n] = [int.from_bytes(g["bytes"][8 * i:8 * i + 8], "little", signed=True) for i in range(len(vals))]
    return res


def main():
    est = sys.argv[1]
    d = json.load(open(AMAP))
    objs = d["objects"]
    addr = {o["name"]: o["addr"] for o in objs}
    with open(est) as f:
        line = f.readline()
    assert line.startswith("# params")
    paths = [t.split("=")[0] for t in line.split()[2:]]
    if VEHICLE:
        # (Phase 5c) AP_RTC's parameters (BRD_RTC_TYPES, BRD_RTC_TZ_MIN; AP_RTC.h:19-20) have their home in the World
        # too (its AP_RTC object is the World's: defaults, loads, the RTC's reads); est.txt's probe does not list them
        paths += [p for p in ("rtc.allowed_types", "rtc.tz_min") if p not in paths]
    # ParametersG2's constructor (ArduCopter/Parameters.cpp:1203-1269): its initializer list sets the pointer members
    # of its AP_SUBGROUPPTR entries to static objects (`mode_rtl_ptr(&copter.mode_rtl)`), and constructs its
    # AC_CommandModel members with arguments (`command_model_pilot_y(PILOT_Y_RATE_DEFAULT, PILOT_Y_EXPO_DEFAULT, 0.0f)`,
    # whose values the tables' AP_GROUPINFO_FLAGS_DEFAULT_POINTER entries read as defaults): both taken from that
    # initializer list, for the members compiled in (those with an AP_SUBGROUPPTR entry / those the probe names)
    ptxt = open(os.path.join(ROOT, "build", "reference", "ap", "ArduCopter", "Parameters.cpp")).read()
    import subprocess as sp
    flt = M.Units(ROOT, os.path.join(ROOT, "build", "param-memory-cache"))
    pre = sp.run(["clang++"] + flt.flags("ArduCopter/Parameters.cpp") + ["-E", "-P", os.path.join(str(flt.b.AP), "ArduCopter", "Parameters.cpp")],
                 cwd=str(flt.b.WAF), capture_output=True, text=True).stdout
    pctor = pre[pre.index("ParametersG2::ParametersG2(void)"):]
    pctor = pctor[:pctor.index("\n{")]
    ptrs = re.findall(r"(\w+_ptr)\(&copter\.([\w.]+)\)", pctor)
    ptrs = [(c, t) for c, t in ptrs if re.search(r"AP_SUBGROUPPTR\(\s*%s\b" % c, ptxt)]
    cms = re.findall(r"(command_model_\w+)\(([^,()]+),\s*([^,()]+),\s*([^,()]+)\)", pctor)
    exprs = [("param_loader", ["__builtin_offsetof(Copter, param_loader)"]),
             ("servo_channels", ["__builtin_offsetof(Copter, g2.servo_channels)"])]
    for k, (path, tab) in enumerate(EXTRA_CTORS):
        exprs.append(("extra:%d" % k, ["__builtin_offsetof(Copter, %s)" % path]))
    for c, t in ptrs:
        exprs.append(("ptr:" + c, ["__builtin_offsetof(Copter, g2.%s)" % c, "__builtin_offsetof(Copter, %s)" % t]))
    for c, a1, a2, a3 in cms:
        exprs.append(("cm:" + c, ["__builtin_offsetof(Copter, g2.%s)" % c] + ["__builtin_bit_cast(int, (float)(%s))" % x for x in (a1, a2, a3)]))
    if VEHICLE:
        exprs.append(("bridge_objects", ["__builtin_offsetof(Copter, %s)" % BRIDGE_MEMBER.get(o, o) for o in BRIDGE_OBJECTS]))
    if GCS:
        exprs += GCS_EXPRS
        for cell, cls, tab, vcell in RUNTIME:
            exprs.append(("rt:" + cell, ["__builtin_offsetof(Copter, %s)" % cell, "sizeof(%s)" % cls] +
                          (["__builtin_offsetof(Copter, %s)" % vcell] if vcell else [])))
        exprs.append(("batt", ["__builtin_offsetof(Copter, battery.drivers[0])", "sizeof(AP_BattMonitor_Analog)",
                               "__builtin_offsetof(Copter, battery)", "__builtin_offsetof(Copter, battery.state[0])",
                               "__builtin_offsetof(Copter, battery._params[0])"]))
    exprs += [
             ("format_version", ["__builtin_offsetof(Copter, g.format_version)", "Parameters::k_format_version"])]
    for p in paths:
        root, _, rest = p.partition(".")
        sym, cls, pre = ROOTS[root]
        m = re.match(r"^(.*)\.([xyz])$", rest)
        comp = 0
        if m:
            rest, comp = m.group(1), "xyz".index(m.group(2)) * 4
            val = "std::declval<%s&>().%s%s.get().%s" % (cls, pre, rest, "xyz"[comp // 4])
        else:
            val = "std::declval<%s&>().%s%s.get()" % (cls, pre, rest)
        exprs.append((p, ["__builtin_offsetof(%s, %s%s) + %d" % (cls, pre, rest, comp), "sizeof(PT(%s))" % val, "PK<PT(%s)>::v" % val]))
    vals = clang_values(exprs)
    ptr_cells = {addr["copter"] + vals["ptr:" + c][0]: addr["copter"] + vals["ptr:" + c][1] for c, t in ptrs}
    ctor = tree(objs, ptr_cells)
    for k, (path, tab) in enumerate(EXTRA_CTORS):
        ctor.append((addr["copter"] + vals["extra:%d" % k][0], addr[tab]))
    cm_calls = [(addr["copter"] + vals["cm:" + c][0], [vals["cm:" + c][k] & 0xffffffff for k in (1, 2, 3)]) for c, _, _, _ in cms]
    est_params = []
    for p in paths:
        root = p.partition(".")[0]
        sym = ROOTS[root][0]
        off, size, kind = vals[p]
        est_params.append({"path": p, "object": sym, "offset": off, "addr": addr[sym] + off, "size": size,
                           "kind": ["unsigned", "signed", "float"][kind]})
    os.makedirs(os.path.dirname(AMAP), exist_ok=True)
    with open(os.path.join(os.path.dirname(AMAP), "estimator_params.json"), "w") as f:
        json.dump(est_params, f, indent=1)
    if VEHICLE:
        with open(os.path.join(os.path.dirname(AMAP), "bridge_objects.json"), "w") as f:
            json.dump({o: addr["copter"] + v for o, v in zip(BRIDGE_OBJECTS, vals["bridge_objects"])}, f, indent=1)
    NS = "VehicleHarnessData" if VEHICLE else ("GCSHarnessData" if GCS else "ParamHarnessData")
    L = ["import %s" % ("Vehicle_lib" if VEHICLE else "GCS_lib" if GCS else "AP_Param_lib"), "", "/-! Generated by ardupilot/param/gen_param_harness.py (README.md, \"Phase 4: AP_Param\"). -/", "",
         "namespace %s" % NS, "",
         "/-- The static objects' constructors' `AP_Param::setup_object_defaults(this, var_info)`: (object, table). -/",
         "def ctorDefaults : Array (UInt64 × UInt64) := #[" + ", ".join("(0x%x, 0x%x)" % c for c in ctor) + "]", "",
         "/-- ParametersG2's constructor: pointer members set to static objects (cell, value). -/",
         "def ctorPointers : Array (UInt64 × UInt64) := #[" + ", ".join("(0x%x, 0x%x)" % c for c in sorted(ptr_cells.items())) + "]", "",
         "/-- ParametersG2's constructor: `AC_CommandModel(initial_rate, initial_expo, initial_tc)` members (object, argument bits). -/",
         "def ctorCommandModels : Array (UInt64 × UInt32 × UInt32 × UInt32) := #[" + ", ".join("(0x%x, 0x%x, 0x%x, 0x%x)" % (o, a[0], a[1], a[2]) for o, a in cm_calls) + "]", "",
         "/-- `&copter.g2.servo_channels`: SRV_Channels's constructor (SRV_Channels.cpp:344-362) sets the defaults of channels 17-32's",
         "functions to k_GPIO (`set_default`), which its table does not give. -/",
         "def servoChannels : UInt64 := 0x%x" % (addr["copter"] + vals["servo_channels"][0]), "",
         "/-- `&copter.param_loader` (Copter's `AP_Param param_loader{var_info}`). -/",
         "def paramLoader : UInt64 := 0x%x" % (addr["copter"] + vals["param_loader"][0]), "",
         "/-- `&copter.g.format_version` and `Parameters::k_format_version` (AP_Vehicle::load_parameters's arguments). -/",
         "def formatVersion : UInt64 := 0x%x" % (addr["copter"] + vals["format_version"][0]),
         "def formatVersionExpected : Int16 := %d" % vals["format_version"][1], "",
         "/-- The estimator World's parameter paths (est_probe.cpp's `# params`): address, size, kind (0 unsigned, 1 signed, 2 float). -/",
         "def estParams : Array (String × UInt64 × Nat × Nat) := #["]
    L.append(",\n".join('  ("%s", 0x%x, %d, %d)' % (e["path"], e["addr"], e["size"], ["unsigned", "signed", "float"].index(e["kind"])) for e in est_params))
    L += ["]", ""]
    if GCS:
        g = vals["gcs_fields"]
        L += ["/-- `&copter._gcs`; GCS's `_num_gcs`, `_chan`; `sizeof(GCS_MAVLINK_Copter)`; GCS_MAVLINK's",
              "`_channel_status.current_tx_seq`, `chan`; `sizeof(Location)` (clang). -/",
              "def gcsObj : UInt64 := 0x%x" % (addr["copter"] + vals["gcs_obj"][0]),
              "def offNumGcs : UInt64 := %d" % g[0], "def offChan : UInt64 := %d" % g[1], "def sizeChannel : Nat := %d" % g[2],
              "/-- `&copter.mode_auto.mission` (ModeAuto's AP_Mission, mode.h:619). -/",
              "def missionObj : UInt64 := 0x%x" % (addr["copter"] + vals["mission_obj"][0]),
              "def offTxSeq : UInt64 := %d" % g[3], "def offChanId : UInt64 := %d" % g[4], "def sizeLocation : Nat := %d" % g[5], ""]
        rows = []
        for cell, cls, tab, vcell in RUNTIME:
            v = vals["rt:" + cell]
            groups = subtree(objs, addr[tab])
            rows.append("  (0x%x, %d, 0x%x, %s, #[%s])  -- copter.%s: %s" % (
                addr["copter"] + v[0], v[1], addr[tab], "0x%x" % (addr["copter"] + v[2]) if vcell else "0",
                ", ".join("(%d, 0x%x)" % gt for gt in groups), cell, cls))
        bv = vals["batt"]
        L += ["/-- AP_BattMonitor::init's analog backend for instance 0 (BATT_MONITOR 4, AP_BattMonitor.cpp:617-619): the",
              "pointer member `drivers[0]`, sizeof, the table, `backend_var_info[0]`, and the constructor's arguments",
              "`*this`, `state[0]`, `_params[0]`. -/",
              "def battBackend : UInt64 × Nat × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 := (0x%x, %d, 0x%x, 0x%x, 0x%x, 0x%x, 0x%x)" % (
                  addr["copter"] + bv[0], bv[1], addr["AP_BattMonitor_Analog::var_info"], addr["AP_BattMonitor::backend_var_info"],
                  addr["copter"] + bv[2], addr["copter"] + bv[3], addr["copter"] + bv[4]), ""]
        L += ["/-- Copter::allocate_motors's parameter objects: (pointer member, sizeof, table, var_info pointer member or 0,",
              "the object's groups (offset, table) for the constructors' setup_object_defaults). -/",
              "def runtimeObjects : Array (UInt64 × Nat × UInt64 × UInt64 × Array (UInt64 × UInt64)) := #[",
              "\n".join(r.replace(")  -- ", ")%s  -- " % ("," if k + 1 < len(rows) else ""), 1) for k, r in enumerate(rows)), "]", ""]
    if VEHICLE:
        L += ["/-- The estimator objects in the memory (members of `copter`, clang's offsets): the `this` of their bridge adapters. -/"]
        for o, v in zip(BRIDGE_OBJECTS, vals["bridge_objects"]):
            L.append("def obj'%s : UInt64 := 0x%x" % (o, addr["copter"] + v))
        L.append("")
    L += ["end %s" % NS, ""]
    with open(os.path.join(ROOT, "lean", NS + ".lean"), "w") as f:
        f.write("\n".join(L))
    print("gen_param_harness: %d constructor default calls, %d estimator parameters" % (len(ctor), len(est_params)))


if __name__ == "__main__":
    main()
