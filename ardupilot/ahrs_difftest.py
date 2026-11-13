#!/usr/bin/env python3
"""Differential test of the AP_AHRS translation (README.md, "Phase 3: AP_AHRS translated").

`python3 difftest.py ardupilot/AHRS` runs this harness (config ardupilot/AHRS.json, "harness"). Both sides hold the
objects as the vehicle has them: `ahrs` (AP_AHRS, with its DCM and EKF3 backends and their estimates), the NavEKF3
front end `AP_AHRS_NavEKF3::EKF3`, AP_DAL's heap singleton, the cores, each core's EKFGSF_yaw and the view
(`create_view`). Each input line is a sequence of vehicle calls on the AHRS (ardupilot/ahrs_scenario.py: boot,
`update(true)` every 400 Hz step, the setters at their events) after the boundary has been given the values of the
line: every input of the translation (AP_DAL's, NavEKF3's, the cores', AP_AHRS's with its DCM's and EKF3
backend's). The C++ side compiles the unmodified ArduPilot sources with the reference build's flags and answers
each getter from the line (ardupilot/ahrs_env.cpp); the Lean side sets `w.heap'AP_DAL'inp`, `w.EKF3'inp`,
`w.heap'NavEKF3_core'inp` and `w.ahrs'inp` from it. After each line both print the results of the calls, the
getters the vehicle and the reference's `--est` probe read (config "getters"), the outputs to the boundary and
every leaf of every object (AP_AHRS with its backends, the front end, AP_DAL, every core, every EKFGSF_yaw, the
view, the shared statics). `--bench` times `AP_AHRS::update` on both sides instead."""

import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "ardupilot"))
import difftest as dt  # noqa: E402
import ekf3_difftest as ek  # noqa: E402
import ahrs_scenario  # noqa: E402

N = ek.N
ROOTS = [("AP_DAL", "w.heap'AP_DAL'inp", "env_dal"), ("NavEKF3", "w.EKF3'inp", "env_ekf3"),
         ("NavEKF3_core", "w.heap'NavEKF3_core'inp", "env_core"), ("AP_AHRS", "w.ahrs'inp", "env_ahrs")]
TOP = {c: cls for cls, _, c in ROOTS}

# the outputs of the translation and where the C++ side has them: (Lean, C++ expression, type)
OUTPUTS = [
    ("w.heap'AP_DAL'o._baro.update_calibration_calls", "env_out.baro_update_calibration_calls", "uint32_t"),
    ("w.ahrs'o.set_board_orientation", "AP::ins()._board_orientation", "Rotation"),
    ("w.ahrs'o.AP_compass_set_board_orientation", "AP::compass()._board_orientation", "Rotation"),
    ("(w.ahrs'o.update_calls + w.ahrs'o.dcm.update_calls)", "env_out.ins_update_calls", "uint32_t"),
    ("w.ahrs'o.boost_end_calls", "env_out.boost_end_calls", "uint32_t"),
    ("w.ahrs'o.gps_fusion", "AP_Notify::flags.gps_fusion", "bool"),
    ("w.ahrs'o.gps_glitching", "AP_Notify::flags.gps_glitching", "bool"),
    ("w.ahrs'o.have_pos_abs", "AP_Notify::flags.have_pos_abs", "bool"),
    ("w.ahrs'o.set_primary", "env_out.ins_set_primary", "uint8_t"),
    ("w.ahrs'o.delay_microseconds", "env_out.delay_microseconds", "uint16_t"),
    ("w.ahrs'o.home_lat", "hal.util->persistent_data.home_lat", "int32_t"),
    ("w.ahrs'o.home_lon", "hal.util->persistent_data.home_lon", "int32_t"),
    ("w.ahrs'o.home_alt_cm", "hal.util->persistent_data.home_alt_cm", "int32_t"),
    ("w.ahrs'o.write_home_to_storage_calls", "env_out.write_home_to_storage_calls", "uint32_t"),
    ("w.ahrs'o.dcm.wait_for_sample_calls", "env_out.ins_wait_for_sample_calls", "uint32_t"),
    ("w.ahrs'o.dcm.read_calls", "env_out.compass_read_calls", "uint32_t"),
    ("w.ahrs'o.dcm.roll_rad", "hal.util->persistent_data.roll_rad", "float"),
    ("w.ahrs'o.dcm.pitch_rad", "hal.util->persistent_data.pitch_rad", "float"),
    ("w.ahrs'o.dcm.yaw_rad", "hal.util->persistent_data.yaw_rad", "float"),
    ("w.ahrs'o.dcm.get_climb_rate_calls", "env_out.baro_get_climb_rate_calls", "uint32_t"),
]
ENV_OUT = ["baro_update_calibration_calls", "ins_update_calls", "boost_end_calls", "write_home_to_storage_calls",
           "ins_wait_for_sample_calls", "compass_read_calls", "baro_get_climb_rate_calls"]


def input_layout(sig):
    """The inputs of the translation in line order: (Lean record path, C++ struct path, field, C++ type, array
    length or None, leaves)."""
    out = []

    def add(cxx_class, lean_root, cxx_root):
        c = ek.cls(sig, cxx_class)
        for i in c["inputs"]:
            t = i["type"]
            n = None
            if t.endswith("[0]"):
                t, n = t[:-3], N
            out.append((lean_root, cxx_root, i["lean"], t, n, ek.leaves_of(sig, t)))
        for s in c.get("sub_inputs", []):
            add(s["class"], lean_root + "." + s["field"], cxx_root + "." + s["field"])
    for cxx_class, lroot, croot in ROOTS:
        add(cxx_class, lroot, croot)
    return out


def struct_name(croot):
    parts = croot.split(".")
    return "cpp2lean_inp_" + "_".join([TOP[parts[0]]] + parts[1:])


def env_header(sig, layout):
    """ahrs_env.h: the C++ structs holding the inputs of a line, named as the Lean Inputs."""
    structs, order = {}, []
    for lroot, croot, f, t, n, _ in layout:
        if croot not in structs:
            structs[croot] = []
            order.append(croot)
        structs[croot].append("    %s %s%s;" % (t, f, "[%d]" % n if n else ""))
    for cls_, _, croot in ROOTS:
        for s in ek.cls(sig, cls_).get("sub_inputs", []):
            k = croot + "." + s["field"]
            if k not in structs:
                structs[k] = []
                order.append(k)
    lines = ["// Generated by ardupilot/ahrs_difftest.py: the boundary inputs of a difftest line (C++ side), one field",
             "// per input of the AP_AHRS translation with its Lean name.", "#pragma once",
             "#include <AP_AHRS/AP_AHRS.h>", "#include <AP_NavEKF3/AP_NavEKF3.h>", "#include <AP_GPS/AP_GPS.h>",
             "#include <AP_Common/Location.h>", ""]
    for croot in sorted(order, key=lambda r: -r.count(".")):     # members before their holders
        subs = [k for k in order if k.startswith(croot + ".") and k.count(".") == croot.count(".") + 1]
        lines += ["struct %s {" % struct_name(croot)] + structs[croot] + \
                 ["    %s %s;" % (struct_name(k), k.split(".")[-1]) for k in subs] + ["};", ""]
    lines += ["struct cpp2lean_out_env { %s uint8_t ins_set_primary; uint16_t delay_microseconds; };" % " ".join("uint32_t %s;" % x for x in ENV_OUT),
              "extern cpp2lean_inp_AP_DAL env_dal;", "extern cpp2lean_inp_NavEKF3 env_ekf3;", "extern cpp2lean_inp_NavEKF3_core env_core;",
              "extern cpp2lean_inp_AP_AHRS env_ahrs;", "extern cpp2lean_out_env env_out;", "void *cpp2lean_raw_alloc(size_t n);",
              "void ahrs_env_apply();", ""]
    return "\n".join(lines)


def method(sig, name):
    return next(m for m in ek.cls(sig, "AP_AHRS")["methods"] if m["lean"].endswith(".AP_AHRS." + name))


def enum_cxx(sig, t):
    e = next((e for e in sig["enums"] if e["cxx"] == t), None)
    return e


# ---------------------------------------------------------------------------------------------
# C++

def cpp_tok(sig, t, expr):
    """A C++ print of a scalar or enum value (enums as their integer values)."""
    e = enum_cxx(sig, t)
    if e is not None:
        return dt.cpp_token_print(e["under"], expr, True)
    return dt.cpp_token_print(t, expr)


def cpp_getters(sig, cfg):
    lines = ["static void getters() {"]
    for g in cfg["getters"]:
        m = method(sig, g["name"])
        args = []
        for i, p in enumerate(m["params"]):
            if p["ref"] == "mut":
                ct = cfg.get("cxx_param_types", {}).get("%s.%s" % (g["name"], p["name"]), [p["type"], ""])[0]
                ct = "Quaternion" if ct == "QuaternionT<float>" else ct
                lines.append("    %s a%d_%s{}; memset((void *)&a%d_%s, 0, sizeof(a%d_%s));" % (ct, i, g["name"], i, g["name"], i, g["name"]))
                args.append("a%d_%s" % (i, g["name"]))
            else:
                e = enum_cxx(sig, p["type"])
                v = g["args"][p["name"]]
                args.append("(%s)%s" % (e["cxx"], v) if e else str(v))
        call = "ahrs.%s(%s)" % (g["name"], ", ".join(args))
        if m["ret"] == "void":
            lines.append("    %s;" % call)
        else:
            lines.append("    { auto r = %s; %s }" % (call, " ".join(dt.cpp_token_print(lt, "r" + cx, en is not None) for _, cx, lt, en in ek.leaves_of(sig, m["ret"]))))
        for i, p in enumerate(m["params"]):
            if p["ref"] == "mut":
                sfx = cfg.get("cxx_param_types", {}).get("%s.%s" % (g["name"], p["name"]), [p["type"], ""])[1]
                for _, cx, lt, en in ek.leaves_of(sig, p["type"]):
                    lines.append("    " + dt.cpp_token_print(lt, "a%d_%s%s%s" % (i, g["name"], sfx, cx), en is not None))
    lines += ["}", ""]
    return lines


CPP_OPS = """    static void ops(const char *o, long arg) {
        for (; *o; o++) {
            printf(" %c", *o);
            switch (*o) {
            case 'B': { AP_AHRS_View *v = ahrs.create_view(ROTATION_NONE); tp(v); ahrs.init(); ahrs.set_vehicle_class(AP_AHRS::VehicleClass::COPTER); ahrs.reset(); break; }
            case 'U': ahrs.update(true); break;
            case 'H': { Location l; bool ok = ahrs.get_location(l); tb(ok); if (ok) tb(ahrs.set_home(l)); break; }
            case 'L': ahrs.lock_home(); break;
            case 'O': { Location l; l.lat = -353632610; l.lng = 1491652300; l.alt = 58400; tb(ahrs.set_origin(l)); break; }
            case 'D': ahrs.resetHeightDatum(); break;
            case 'T': ahrs.set_terrain_hgt_stable(arg != 0); break;
            case 'K': ahrs.set_takeoff_expected(arg != 0); break;
            case 'W': ahrs.set_touchdown_expected(arg != 0); break;
            case 'Y': ahrs.request_yaw_reset(); break;
            case 'C': ahrs.check_lane_switch(); break;
            case 'E': ahrs._ekf_type.set(AP_AHRS::EKFType(arg)); break;
            default: printf("?"); break;
            }
        }
    }
"""


def cpp_driver(sig, cfg, layout):
    lines = ["// Generated by ardupilot/ahrs_difftest.py: the C++ side of the AP_AHRS difftest.",
             "#include <cinttypes>", "#include <cstdint>", "#include <cstdio>", "#include <cstdlib>", "#include <cstring>"]
    lines += dt.heap_registry(sig)
    lines += ["void *cpp2lean_raw_alloc(size_t n) { void *p = calloc(1, n); cpp2lean_log(p, n, true); return p; }",
              "#undef malloc", "#include \"ahrs_env.h\"", "#include <AP_AHRS/AP_AHRS.h>", "#include <AP_AHRS/AP_AHRS_View.h>",
              "#include <AP_NavEKF3/AP_NavEKF3.h>", "#include <AP_NavEKF3/AP_NavEKF3_core.h>", "#include <AP_DAL/AP_DAL.h>",
              "#include <AP_InertialSensor/AP_InertialSensor.h>", "#include <AP_Compass/AP_Compass.h>", "#include <AP_Notify/AP_Notify.h>", "",
              "// the vehicle's AHRS (AP_Vehicle.h:419; ardupilot/unity_ahrs.cpp: a file-scope object)", "AP_AHRS ahrs;",
              "extern const AP_HAL::HAL &hal;", ""]
    lines += dt.heap_names(sig)
    lines += dt.CPP_PRELUDE
    lines.append("static void dump() {")
    for w in sig["world"] + sig.get("world_statics", []):
        if w.get("local"):
            continue
        for lf, cxx, _ in dt.world_leaves(sig, w):
            lines.append("    " + dt.cpp_token_print(lf["type"], cxx, lf["enum"] is not None))
    for hi, h in enumerate(sig.get("heap", [])):
        c = ek.cls(sig, h["class"])
        lines.append("    { int k = 0; for (int i = 0; i < cpp2lean_nalloc; i++) { size_t m; if (cpp2lean_class_of(cpp2lean_allocs[i], &m) == %d) k += (int)m; } printf(\" h:%%d\", k); }" % hi)
        lines.append("    for (int i = 0; i < cpp2lean_nalloc; i++) { size_t m; if (cpp2lean_class_of(cpp2lean_allocs[i], &m) != %d) continue;" % hi)
        lines.append("        for (size_t j = 0; j < m; j++) { %s *o = (%s *)((char *)cpp2lean_allocs[i].p + j * sizeof(%s));" % (h["class"], h["class"], h["class"]))
        for lf in c["leaves"]:
            lines.append("            " + dt.cpp_token_print(lf["type"], "o->" + lf["cxx"], lf["enum"] is not None))
        lines.append("        } }")
    lines.append("    printf(\" o:\");")
    for _, cx, t in OUTPUTS:
        lines.append("    " + cpp_tok(sig, t, cx))
    lines += ["}", ""]
    lines.append("static void set_inputs(char **tok) {")
    k = 0
    for lroot, croot, f, t, n, lvs in layout:
        for j in range(n or 1):
            for lean, cxx, lt, en in lvs:
                tgt = "%s.%s%s%s" % (croot, f, "[%d]" % j if n else "", cxx)
                if en is not None:
                    e = next(e for e in sig["enums"] if e["lean"] == en)
                    lines.append("    %s = static_cast<%s>(strtoll(tok[%d], nullptr, 10));" % (tgt, e["cxx"], k))
                else:
                    lines.append("    %s = %s;" % (tgt, dt.cpp_read(lt, "tok[%d]" % k)))
                k += 1
    lines += ["}", ""]
    nin = k
    lines += cpp_getters(sig, cfg)
    lines.append(CPP_OPS)
    lines += ["int main(int argc, char **argv) {",
              "    if (argc > 1 && !strcmp(argv[1], \"--consts\")) {   // the inline getters that compute a constant (ahrs_scenario)",
              "        float r = AP::ins().get_gyro_drift_rate(); uint32_t u; memcpy(&u, &r, 4); printf(\"get_gyro_drift_rate %08x\\n\", u); return 0;",
              "    }",
              "    static char buf[1 << 20];", "    long line = 0;",
              "    printf(\"0 init |\"); dump(); printf(\"\\n\");",
              "    while (fgets(buf, sizeof buf, stdin)) {", "        line++;", "        static char *tok[1 << 15];", "        int nt = 0;",
              "        for (char *p = strtok(buf, \" \\n\"); p && nt < (1 << 15); p = strtok(nullptr, \" \\n\")) tok[nt++] = p;",
              "        if (nt != %d) { fprintf(stderr, \"bad input line %%ld (%%d tokens)\\n\", line, nt); return 1; }" % (nin + 2),
              "        set_inputs(tok + 2);", "        ahrs_env_apply();",
              "        printf(\"%ld\", line);",
              "        ops(tok[0], strtol(tok[1], nullptr, 10));",
              "        getters();",
              "        printf(\" |\"); dump(); printf(\"\\n\");", "    }", "    return 0;", "}", ""]
    return "\n".join(lines), nin


# ---------------------------------------------------------------------------------------------
# Lean

def lean_call(sig, m, extra_args, nm):
    """(lines, result tokens) of a call of AP_AHRS member function m on the World `w` (rebinding w)."""
    args = []
    rw = m["reads"] + m["writes"]
    if "p" in rw:
        args.append("w.ahrs'p")
    if "s" in rw:
        args.append("w.ahrs")
    if "w" in rw:
        args.append("w")
    if "o" in m["writes"]:
        args.append("w.ahrs'o")
    if m["uses_inp"]:
        args.append("w.ahrs'inp")
    args += extra_args
    comps = [c for c in ("p", "s", "w", "o") if c in m["writes"]]
    outs = [i for i, p in enumerate(m["params"]) if p["ref"] == "mut"]
    comps += ["o%d" % i for i in outs]
    if m["ret"] != "void":
        comps.append("r")
    names = ["%s_%d" % (nm, i) for i in range(len(comps))]
    lines = []
    call = "AP_AHRS.%s %s" % (m["lean"].split(".")[-1], " ".join(args))
    if comps:
        lines.append("  let %s := %s" % (names[0] if len(comps) == 1 else "(%s)" % ", ".join(names), call))
    for c, n_ in sorted(zip(comps, names), key=lambda x: 0 if x[0] == "w" else 1):
        if c == "w":
            lines.append("  let w := %s" % n_)
        elif c == "p":
            lines.append("  let w := { w with ahrs'p := %s }" % n_)
        elif c == "s":
            lines.append("  let w := { w with ahrs := %s }" % n_)
        elif c == "o":
            lines.append("  let w := { w with ahrs'o := %s }" % n_)
    toks = []
    if m["ret"] != "void":
        if m["ret"].endswith("*"):
            toks.append("tP (%s).name" % names[comps.index("r")])
        else:
            toks += [dt.lean_tok(lt, names[comps.index("r")] + ln, en) for ln, _, lt, en in ek.leaves_of(sig, m["ret"])]
    for i in outs:
        p = m["params"][i]
        toks += [dt.lean_tok(lt, names[comps.index("o%d" % i)] + ln, en) for ln, _, lt, en in ek.leaves_of(sig, p["type"])]
    return lines, toks


def lean_zero(sig, t):
    if t == "bool":
        return "false"
    if t in ("float", "double"):
        return "(%s.ofBits 0)" % dt.lean_type(t)
    if t in dt.INTS:
        return "(0 : %s)" % dt.lean_type(t)
    return "{}"


def lean_arg(sig, p, v):
    e = enum_cxx(sig, p["type"])
    if e is not None:
        return "(%s.ofInt'' %d)" % (e["lean"], v)
    return "(%s : %s)" % (v, dt.lean_type(p["type"]))


def lean_driver(sig, cfg, layout, nin, bench=False):
    ns = sig["namespace"]
    head = ek.lean_driver(sig, {"getters": []}, [], 0)
    head = head[:head.index("def setInputs")]       # the readers and printers of the NavEKF3 driver
    head = head.replace("ardupilot/ekf3_difftest.py: the Lean side of the NavEKF3 difftest", "ardupilot/ahrs_difftest.py: the Lean side of the AP_AHRS difftest")
    out = [head]
    gargs = {enum_cxx(sig, p["type"])["lean"] for g in cfg["getters"] for p in method(sig, g["name"])["params"]
             if p["ref"] != "mut" and enum_cxx(sig, p["type"]) is not None}
    used = sorted({en for _, _, _, _, _, lvs in layout for _, _, _, en in lvs if en} | gargs |
                  {enum_cxx(sig, "AP_AHRS::EKFType")["lean"], enum_cxx(sig, "Rotation")["lean"]})
    for en in used:
        e = next(e for e in sig["enums"] if e["lean"] == en)
        out.append("def %s.ofInt'' (v : Int) : %s :=" % (en, en))
        for i, (nm, v, ln) in enumerate(e["values"]):
            out.append("  %sif v == %d then %s.%s" % ("" if i == 0 else "else ", v, en, ln))
        out.append("  else default")
    out.append("")
    # inputs: one definition per record
    k = 0
    recs, order = {}, []
    for lroot, croot, f, t, n, lvs in layout:
        vals = []
        for j in range(n or 1):
            if len(lvs) == 1 and lvs[0][0] == "":
                vals.append(ek.lean_value(sig, lvs[0][2], "t[%d]!" % (k + 2), lvs[0][3]))
                k += 1
            else:
                fields = []
                for lean, cxx, lt, en in lvs:
                    fields.append((lean.strip("."), ek.lean_value(sig, lt, "t[%d]!" % (k + 2), en)))
                    k += 1
                vals.append(ek.nest_record(fields))
        v = "#[%s]" % ", ".join(vals) if n else vals[0]
        if lroot not in recs:
            recs[lroot] = []
            order.append(lroot)
        recs[lroot].append((f, v))
    assert k == nin
    W = "World"
    defs = []
    for ri, lroot in enumerate(order):
        out.append("def setInputs_%d (w : %s) (t : Array String) : %s :=" % (ri, W, W))
        out.append("  { w with %s := { %s with %s } }" % (lroot[2:], lroot, ", ".join("%s := %s" % (f, v) for f, v in recs[lroot])))
        out.append("")
        defs.append(ri)
    out.append("def setInputs (w : %s) (t : Array String) : %s :=" % (W, W))
    e = "w"
    for ri in defs:
        e = "(setInputs_%d %s t)" % (ri, e)
    out.append("  " + e)
    out.append("")
    # the dump, in chunks
    toks = []
    for w in sig["world"] + sig.get("world_statics", []):
        if w.get("local"):
            continue
        toks += [dt.lean_tok(lf["type"], lean, lf["enum"]) for lf, _, lean in dt.world_leaves(sig, w)]
    chunks = [toks[i:i + 150] for i in range(0, len(toks), 150)]
    for ci, ch in enumerate(chunks):
        out.append("def dumpW_%d (w : %s) : String :=" % (ci, W))
        out.append("  \"\"" + "".join(" ++ " + t for t in ch))
        out.append("")
    hparts = []
    for hi, h in enumerate(sig.get("heap", [])):
        c = ek.cls(sig, h["class"])
        ltoks = [dt.lean_tok(lf["type"], "st.%s" % lf["lean"], lf["enum"]) for lf in c["leaves"]]
        hch = [ltoks[i:i + 150] for i in range(0, len(ltoks), 150)] or [[]]
        for ci, ch in enumerate(hch):
            out.append("def dumpH_%d_%d (st : %s.State) : String :=" % (hi, ci, h["lean"]))
            out.append("  \"\"" + "".join(" ++ " + t for t in ch))
            out.append("")
        out.append("def dumpH_%d (w : %s) : String :=" % (hi, W))
        out.append("  \" h:\" ++ toString w.%s.size ++ w.%s.foldl (fun acc st => acc%s) \"\"" %
                   (h["field"], h["field"], "".join(" ++ dumpH_%d_%d st" % (hi, ci) for ci in range(len(hch)))))
        out.append("")
        hparts.append("dumpH_%d w" % hi)
    otoks = []
    for ln, _, t in OUTPUTS:
        e = enum_cxx(sig, t)
        otoks.append(dt.lean_tok(e["under"] if e else t, ln, e["lean"] if e else None))
    out.append("def dumpO (w : %s) : String :=" % W)
    out.append("  \" o:\"" + "".join(" ++ " + t for t in otoks))
    out.append("")
    out.append("def dump (w : %s) : String :=" % W)
    out.append("  " + " ++ ".join(["dumpW_%d w" % ci for ci in range(len(chunks))] + hparts + ["dumpO w"]))
    out.append("")
    # the getters
    out.append("def getters (w : %s) : %s × String := Id.run do" % (W, W))
    gtoks = []
    for gi, g in enumerate(cfg["getters"]):
        m = method(sig, g["name"])
        extra = [lean_zero(sig, p["type"]) if p["ref"] == "mut" else lean_arg(sig, p, g["args"][p["name"]]) for p in m["params"]]
        ls, tk = lean_call(sig, m, extra, "g%d" % gi)
        out += ls
        out.append("  let s%d : String := %s" % (gi, " ++ ".join(["\"\""] + tk)))
        gtoks.append("s%d" % gi)
    out.append("  return (w, %s)" % " ++ ".join(["\"\""] + gtoks))
    out.append("")
    # the vehicle's calls
    calls = {}

    def mk(name, mname, extra, show=True):
        m = method(sig, mname)
        ls, tk = lean_call(sig, m, extra, "c")
        calls[name] = (ls, tk if show else [])
    rot = enum_cxx(sig, "Rotation")["lean"]
    vc = enum_cxx(sig, "AP_AHRS::VehicleClass")["lean"]
    et = enum_cxx(sig, "AP_AHRS::EKFType")["lean"]
    mk("create_view", "create_view", ["%s.ROTATION_NONE" % rot, "(Binary32.ofBits 0)"])
    mk("init", "init", [])
    mk("set_vehicle_class", "set_vehicle_class", ["%s.COPTER" % vc])
    mk("reset", "reset", [])
    mk("update", "update", ["true"])
    mk("get_location", "get_location", ["{}"])
    mk("lock_home", "lock_home", [])
    mk("resetHeightDatum", "resetHeightDatum", [])
    mk("request_yaw_reset", "request_yaw_reset", [])
    mk("check_lane_switch", "check_lane_switch", [])
    for nm, mname in (("T", "set_terrain_hgt_stable"), ("K", "set_takeoff_expected"), ("W", "set_touchdown_expected")):
        mk(nm, mname, ["(arg != 0)"])
    for nm in list(calls):
        ls, tk = calls[nm]
        params = " (arg : Int)" if nm in ("T", "K", "W") else ""
        out.append("def call_%s (w : %s)%s : %s × String := Id.run do" % (nm, W, params, W))
        out += ls + ["  return (w, %s)" % " ++ ".join(["\"\""] + tk), ""]
    sh = method(sig, "set_home")
    so = method(sig, "set_origin")
    shl, shk = lean_call(sig, sh, ["l"], "h")
    sol, sok = lean_call(sig, so, ["{ lat := (-353632610 : Int32), lng := (1491652300 : Int32), alt := (58400 : Int32) }"], "g")
    out.append("def call_set_home (w : %s) (l : Location.State) : %s × String := Id.run do" % (W, W))
    out += shl + ["  return (w, %s)" % " ++ ".join(["\"\""] + shk), ""]
    out.append("def call_set_origin (w : %s) : %s × String := Id.run do" % (W, W))
    out += sol + ["  return (w, %s)" % " ++ ".join(["\"\""] + sok), ""]
    gl = method(sig, "get_location")
    gll, _ = lean_call(sig, gl, ["{}"], "q")
    # get_location's results: (loc, ok)
    out += ["def ops (w : %s) (o : List Char) (arg : Int) : %s × String := Id.run do" % (W, W),
            "  let mut w := w", "  let mut r := \"\"",
            "  for c in o do",
            "    r := r ++ \" \" ++ c.toString",
            "    if c == 'B' then",
            "      let (w1, s1) := call_create_view w", "      let (w2, _) := call_init w1", "      let (w3, _) := call_set_vehicle_class w2",
            "      let (w4, _) := call_reset w3", "      w := w4", "      r := r ++ s1",
            "    else if c == 'U' then",
            "      w := (call_update w).1",
            "    else if c == 'H' then",
            "      let (l, ok) := AP_AHRS.get_location w.ahrs {}",
            "      r := r ++ tB ok",
            "      if ok then",
            "        let (w1, s1) := call_set_home w l", "        w := w1", "        r := r ++ s1",
            "    else if c == 'L' then", "      w := (call_lock_home w).1",
            "    else if c == 'O' then", "      let (w1, s1) := call_set_origin w", "      w := w1", "      r := r ++ s1",
            "    else if c == 'D' then", "      w := (call_resetHeightDatum w).1",
            "    else if c == 'T' then", "      w := (call_T w arg).1",
            "    else if c == 'K' then", "      w := (call_K w arg).1",
            "    else if c == 'W' then", "      w := (call_W w arg).1",
            "    else if c == 'Y' then", "      w := (call_request_yaw_reset w).1",
            "    else if c == 'C' then", "      w := (call_check_lane_switch w).1",
            "    else if c == 'E' then",
            "      w := { w with ahrs'p := { w.ahrs'p with _ekf_type := %s.ofInt'' arg } }" % et,
            "    else", "      r := r ++ \"?\"",
            "  return (w, r)", ""]
    if bench:
        out += ["def predicted (w : World) : Bool :=",
                "  match w.heap'NavEKF3_core[0]? with",
                "  | some c => c.framesSincePredict == 0",
                "  | none => false", "",
                "partial def bench (h : IO.FS.Stream) (o : IO.FS.Stream) (w : %s) : IO Unit := do" % W,
                "  let line ← h.getLine", "  if line.isEmpty then return",
                "  let t := (((line.trimAscii.toString).splitOn \" \").filter (· ≠ \"\")).toArray",
                "  let w := setInputs w t",
                "  let os := t[0]!.toList",
                "  let pre := os.filter (· ≠ 'U')",
                "  let (w, _) := ops w pre (inInt t[1]!)",
                "  let w ← pure w",
                "  let t0 ← IO.monoNanosNow",
                "  let w := (call_update w).1",
                "  let p := predicted w",
                "  let act := AP_AHRS.EKFType.toInt w.ahrs.state.active_EKF_type",
                "  let t1 ← IO.monoNanosNow",
                "  o.putStr (s!\"U {t1 - t0} {if p then 1 else 0} {act}\\n\")",
                "  bench h o w", "",
                "def main : IO Unit := do",
                "  let o ← IO.getStdout",
                "  bench (← IO.getStdin) o World.init", ""]
        return "\n".join(out)
    out += ["partial def loop (h : IO.FS.Stream) (o : IO.FS.Stream) (w : %s) (n : Nat) : IO Unit := do" % W,
            "  let line ← h.getLine", "  if line.isEmpty then return",
            "  let t := (((line.trimAscii.toString).splitOn \" \").filter (· ≠ \"\")).toArray",
            "  let w := setInputs w t",
            "  let (w, r) := ops w t[0]!.toList (inInt t[1]!)",
            "  let (w, g) := getters w",
            "  o.putStr (toString (n + 1) ++ r ++ g ++ \" |\" ++ dump w ++ \"\\n\")",
            "  o.flush",
            "  loop h o w (n + 1)", "",
            "def main : IO Unit := do",
            "  let w := World.init",
            "  let o ← IO.getStdout",
            "  o.putStr (\"0 init |\" ++ dump w ++ \"\\n\")",
            "  loop (← IO.getStdin) o w 0", ""]
    return "\n".join(out)


def cpp_bench(drv):
    """The C++ side of `--bench`: the driver's main replaced by a timed loop (the setters untimed, AP_AHRS::update timed)."""
    head = drv[:drv.index("int main(int argc")]
    return head + "\n".join([
        "#include <chrono>",
        "int main() {", "    static char buf[1 << 20];",
        "    while (fgets(buf, sizeof buf, stdin)) {", "        static char *tok[1 << 15];", "        int nt = 0;",
        "        for (char *p = strtok(buf, \" \\n\"); p && nt < (1 << 15); p = strtok(nullptr, \" \\n\")) tok[nt++] = p;",
        "        set_inputs(tok + 2);", "        ahrs_env_apply();",
        "        char pre[64]; int np = 0; for (const char *c = tok[0]; *c && np < 63; c++) if (*c != 'U') pre[np++] = *c; pre[np] = 0;",
        "        { int fd = dup(1); fflush(stdout); FILE *nul = freopen(\"/dev/null\", \"w\", stdout); (void)nul; ops(pre, strtol(tok[1], nullptr, 10)); fflush(stdout); dup2(fd, 1); close(fd); }",
        "        auto t0 = std::chrono::steady_clock::now();",
        "        ahrs.update(true);",
        "        auto t1 = std::chrono::steady_clock::now();",
        "        printf(\"U %lld\\n\", (long long)std::chrono::duration_cast<std::chrono::nanoseconds>(t1 - t0).count());",
        "    }", "    return 0;", "}", ""])


def build(cfg, sig, layout, bdir, bench):
    with open(os.path.join(bdir, "ahrs_env.h"), "w") as f:
        f.write(env_header(sig, layout))
    drv, nin = cpp_driver(sig, cfg, layout)
    if bench:
        drv = drv.replace("#include <cstring>", "#include <cstring>\n#include <unistd.h>", 1)
    with open(os.path.join(bdir, "ahrs_driver.cpp"), "w") as f:
        f.write(cpp_bench(drv) if bench else drv)
    ref = os.environ.get("CPP2LEAN_REF", os.path.join(HERE, "build", "reference", "ap"))
    lib = os.path.join(ref, "libraries")
    p = dt.run([sys.executable, os.path.join(HERE, "ardupilot", "ref_flags.py"), "--json", cfg["ref_flags"]])
    flags = [x for x in json.loads(p.stdout.decode()) if not x.startswith("-W")] + ["-Wno-everything", "-fno-access-control", "-I", bdir]
    flags += dt.cpp2lean.CODEGEN_EXTRA
    objs = []
    for src in [os.path.join(lib, x) for x in cfg["cxx_sources"]] + [os.path.join(HERE, x) for x in cfg["cxx_env"]] + [os.path.join(bdir, "ahrs_driver.cpp")]:
        o = os.path.join(bdir, src.replace(lib + os.sep, "").replace(HERE + os.sep, "").replace("/", "_").replace(".cpp", ".o"))
        if not os.path.exists(o) or os.path.getmtime(o) < os.path.getmtime(src) or src.endswith(("ahrs_driver.cpp", "ahrs_env.cpp")):
            dt.run([dt.CXX] + flags + ["-c", src, "-o", o])
        objs.append(o)
    exe = os.path.join(bdir, "ahrs_cpp" + ("_bench" if bench else ""))
    dt.run([dt.CXX, "-o", exe] + objs + ["-Wl,-dead_strip"] + dt.musl_link())
    return exe, nin


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("config", nargs="?", default="ardupilot/AHRS")
    ap.add_argument("--steps", type=int, default=None)
    ap.add_argument("--runs", default=None, help="comma-separated run names (default: all)")
    ap.add_argument("--bench", action="store_true", help="measure the time per AP_AHRS::update instead")
    a = ap.parse_args()
    with open(os.path.join(HERE, a.config + ".json")) as f:
        cfg = json.load(f)
    out_dir = os.path.join(HERE, cfg["out"])
    if not cfg.get("no_translate") and not os.environ.get("CPP2LEAN_NO_TRANSLATE"):
        dt.run([os.path.join(HERE, cfg["translate"])], cwd=HERE)
    ns = cfg["namespace"]
    with open(os.path.join(out_dir, ns + ".signatures.json")) as f:
        sig = dt.split_world_statics(json.load(f))
    layout = input_layout(sig)
    bdir = os.path.join(HERE, "build", "ahrs_difftest")
    os.makedirs(bdir, exist_ok=True)
    exe, nin = build(cfg, sig, layout, bdir, a.bench)
    cexe = exe if not a.bench else build(cfg, sig, layout, bdir, False)[0]
    consts = {}
    for l in subprocess.run([cexe, "--consts"], stdout=subprocess.PIPE, check=True).stdout.decode().split("\n"):
        if l:
            nm, hx = l.split()
            consts[nm] = __import__("struct").unpack(">f", bytes.fromhex(hx))[0]
    # the Lean side
    for fn in os.listdir(out_dir):
        if fn.endswith(".lean") and fn != "CFloat.lean":
            with open(os.path.join(out_dir, fn)) as src, open(os.path.join(dt.DEMO, fn), "w") as dst:
                text = src.read()
                if os.environ.get("CPP2LEAN_MUTATE") and fn == ns + ".lean":
                    # sensitivity checks (README.md): a JSON list of [regex, replacement] applied to the translation
                    for pat, rep in json.loads(os.environ["CPP2LEAN_MUTATE"]):
                        text, k = __import__("re").subn(pat, rep, text)
                        print("mutation of %s: %d replacements of /%s/" % (fn, k, pat))
                dst.write(text)
    with open(os.path.join(dt.DEMO, "AHRSMain.lean"), "w") as f:
        f.write(lean_driver(sig, cfg, layout, nin, bench=a.bench))
    env = dict(os.environ, LEAN_NUM_THREADS="1")
    p = subprocess.run(["lake", "build", "ahrs_lean"], cwd=dt.DEMO, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    out = p.stdout.decode()
    if p.returncode != 0:
        sys.stderr.write(out[-8000:])
        sys.exit("ahrs_difftest: lake build ahrs_lean failed")
    if "warning" in out:
        sys.stderr.write("\n".join(l for l in out.split("\n") if "warning" in l)[:4000] + "\n")
        sys.exit("ahrs_difftest: warnings in the Lean build")
    lexe = os.path.join(dt.DEMO, ".lake", "build", "bin", "ahrs_lean")
    runs = [r for r in cfg["runs"] if not a.runs or r["name"] in a.runs.split(",")]
    if a.bench:
        return bench(runs, sig, layout, bdir, exe, lexe, a.steps, consts)
    rc = 0
    for run in runs:
        steps = a.steps or run["steps"]
        lines = ahrs_scenario.lines(run, steps, lambda vals: ek.tokens_of(sig, layout, vals), consts)
        base = os.path.join(bdir, run["name"])
        with open(base + ".in", "w") as f:
            for l in lines:
                f.write(l + "\n")
        diffs, nan_only, m = dt.compare_stream([cexe], [lexe], base)
        n = dt.report("ardupilot/AHRS AP_AHRS (%s)" % run["name"], diffs, nan_only, m, "tokens")
        rc |= 1 if n else 0
    sys.exit(rc)


def bench(runs, sig, layout, bdir, exe, lexe, steps, consts):
    """Both timed drivers on each run's lines: ns per AP_AHRS::update, by kind (all; the EKF3 prediction steps; the
    others; DCM active)."""
    import statistics
    for run in runs:
        n = steps or run["steps"]
        lines = ahrs_scenario.lines(run, n, lambda vals: ek.tokens_of(sig, layout, vals), consts)
        base = os.path.join(bdir, run["name"] + "_bench")
        with open(base + ".in", "w") as f:
            f.write("\n".join(lines) + "\n")
        lo = subprocess.run([lexe], stdin=open(base + ".in"), stdout=subprocess.PIPE, check=True).stdout.decode().split("\n")
        co = subprocess.run([exe], stdin=open(base + ".in"), stdout=subprocess.PIPE, check=True).stdout.decode().split("\n")
        rows = []
        for k, (l, c) in enumerate(zip(lo, co)):
            if not l:
                continue
            _, ns_, pred, act = l.split()
            rows.append((k, int(ns_), pred == "1", int(act), int(c.split()[1])))

        def summ(sel, label):
            r = [x for x in rows if sel(x)]
            if not r:
                return
            ln = [x[1] for x in r]
            cn = [x[4] for x in r]
            print("  %-44s %6d calls  Lean mean %9.0f ns  median %9.0f  p99 %9.0f   C++ mean %7.0f ns  ratio %5.0f" %
                  (label, len(r), statistics.mean(ln), statistics.median(ln), sorted(ln)[int(0.99 * (len(ln) - 1))],
                   statistics.mean(cn), statistics.mean(ln) / max(1.0, statistics.mean(cn))))
        print("ardupilot/AHRS bench (%s, %d steps):" % (run["name"], n))
        summ(lambda x: True, "AP_AHRS::update, all steps")
        summ(lambda x: x[2], "AP_AHRS::update, EKF3 prediction steps")
        summ(lambda x: not x[2], "AP_AHRS::update, other steps")
        summ(lambda x: x[3] == 0, "AP_AHRS::update, DCM active")
        summ(lambda x: x[0] >= 14000, "AP_AHRS::update after GPS aiding (> 35 s)")


if __name__ == "__main__":
    main()
