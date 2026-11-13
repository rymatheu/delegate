#!/usr/bin/env python3
"""The estimator bridge's adapters (README.md "Phase 5: the estimator bridge"): ardupilot/out/Vehicle/VehicleBridge.lean.

The vehicle translation (cpp2lean --param-memory ardupilot/vehicle/Vehicle.json, key `bridge_module`) calls every
estimator function through an adapter `VehicleBridge.<Class>.<function>'<arity>` in the memory's state monad and writes
each adapter's memory-side signature to ardupilot/out/Vehicle/Vehicle_lib.bridge.json: the object's address for a member
function, a temporary for a record result, the arguments as the translator passes them (scalars as values, references and
records as addresses) with clang's layout of every record, the configured vehicle inputs. This script generates the
adapters from that file and from the estimator World's translation (ardupilot/out/Estimator/Estimator_lib.signatures.json
for each method's World signature: what it reads and writes, its parameters' references and records' leaves; the Lean
text for its exact parameter list). An adapter only marshals:

  memory -> World   scalars converted to the World's types (enumerations by their values), records read leaf by leaf at
                    clang's offsets (bit-fields by their bits) into the World's `State` structures, references' current
                    values; the World's boundary inputs that are vehicle state set from the memory state (the HAL's armed
                    flag `Mem.armed` for every reader; AP_DAL's time flying from the translated
                    AP_Vehicle::get_time_flying_ms, passed by the call site)
  call              the World's translation on `(← get).w` (its object, its inputs, the World, the output log)
  World -> memory   the World and the log stored back into the memory state, out-parameters (non-const references)
                    written back to memory, a record result written into the caller's temporary (`sret`)

Written by hand (the table HAND below, each with its reason): the accessors (`AP::ahrs()` ...: the object's address in
the memory, clang's offset in `copter`), `sitl()` (null: the SITL object is not in this memory), and the functions the
World does not translate (listed in the generated file; they record the call, PMem.bridge, and give the default). The
MAVLink senders of the estimator classes (Phase 5c) are generated: the World's translation makes their sends Output
events, replayed on the memory after the call.

Usage: ardupilot/vehicle/gen_bridge.py   (after ardupilot/vehicle/translate_vehicle.sh and gen_param_harness.py's
vehicle target); writes ardupilot/out/Vehicle/VehicleBridge.lean and lean/VehicleBridge.lean.
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
OUT = os.path.join(ROOT, "ardupilot", "out", "Vehicle")

LD = {"float": ("F32", "Binary32"), "double": ("F64", "Binary64"), "uint8_t": ("U8", "UInt8"), "unsigned char": ("U8", "UInt8"),
      "int8_t": ("I8", "Int8"), "signed char": ("I8", "Int8"), "char": ("I8", "Int8"), "uint16_t": ("U16", "UInt16"),
      "unsigned short": ("U16", "UInt16"), "int16_t": ("I16", "Int16"), "short": ("I16", "Int16"),
      "uint32_t": ("U32", "UInt32"), "unsigned int": ("U32", "UInt32"), "int32_t": ("I32", "Int32"), "int": ("I32", "Int32"),
      "uint64_t": ("U64", "UInt64"), "unsigned long": ("U64", "UInt64"), "int64_t": ("I64", "Int64"), "long": ("I64", "Int64"),
      "bool": ("B", "Bool"), "_Bool": ("B", "Bool"),
      "postype_t": ("F64", "Binary64")}   # (Phase 5c) AP_AHRS_Backend::Estimates::position_D (ftype.h: double)

# the accessors: the estimator object's member of `copter` (clang's offset)
ACCESSORS = {"ahrs": "ahrs", "AP::ahrs": "ahrs", "ins": "ins", "AP::ins": "ins", "gps": "gps", "AP::gps": "gps",
             "baro": "barometer", "AP::baro": "barometer", "compass": "compass", "AP::compass": "compass",
             "rtc": "rtc", "AP::rtc": "rtc"}
# the estimator's own pre-arm checks that are not in the World's translation (they pass in the recorded sessions)
PASSING_CHECKS = {"AP_Baro::arming_checks", "AP_GPS::pre_arm_checks", "AP_InertialSensor::pre_arm_check_gyro_backend_rate_hz",
                  "Compass::configured"}
# (Phase 5d) AP_AHRS::pre_arm_check is translated in the World (its `char *failure_msg` a text sink, cpp2lean.py
# --text-buffers): its adapter is generated
# written by hand, with the reason
HAND = {
    "sitl": ("pure 0x800", "SITL::SIM is the World's stand-in; the vehicle sees a zeroed SITL object (address 0x800, in the null "
             "page below the image): its parameters are 0, as the reference's defaults (SIM_LOOP_DELAY 0: AP_Scheduler::loop "
             "does not delay; null made it delay 1000 us, one input line per loop)"),
    "AP::sitl": ("pure 0x800", "as `sitl`"),
    "AP_Declination::get_earth_field_ga": ("do\n"
                                           "    let lat ← PMem.ldI32 (a0 + 8)\n"
                                           "    let lng ← PMem.ldI32 (a0 + 12)\n"
                                           "    let alt ← PMem.ldI32 (a0 + 4)\n"
                                           "    let v := Estimator_lib.AP_Declination.get_earth_field_ga { lat := lat, lng := lng, alt := alt }\n"
                                           "    PMem.stF32 sret v.x\n"
                                           "    PMem.stF32 (sret + 4) v.y\n"
                                           "    PMem.stF32 (sret + 8) v.z",
                                           "a static function of the World's translation (no object): the Location from the memory (clang's "
                                           "layout: alt +4, lat +8, lng +12), the field written to the result"),
    "AP_AHRS::create_view": ("do\n"
                             "    let (w0, eo0, armed) ← modifyGet fun m => ((m.w, m.eo, m.armed), { m with w := Estimator_lib.World.init, eo := #[] })\n"
                             "    let w := setArmed w0 armed\n"
                             "    let (s', w', res) := Estimator_lib.AP_AHRS.create_view w.ahrs w (if a0 == 0 then Estimator_lib.Rotation.ROTATION_NONE else default) a1\n"
                             "    modify fun m => { m with w := { w' with ahrs := s' }, eo := eo0 }\n"
                             "    return (if res == WPtr.null then 0 else 0x200)",
                             "the World's view is a heap slot (`ahrs._view`), which every AP_AHRS_View adapter reads; the vehicle "
                             "keeps a pointer: the fixed address 0x200 (outside the image) when the World made the view, else null"),
    # Phase 5c: AP_AHRS::send_ekf_status_report, AP_GPS::send_mavlink_gps_raw/gps2_raw are translated in the World (their
    # mavlink_msg_*_send calls are Output events, replayed on the memory by the translation's worldOutputs'drain); their
    # adapters are generated (before: the recorded frame, PMem.bframe)
    "AP_GPS::handle_msg": ("PMem.unreached \"AP_GPS::handle_msg\"", "GPS injection over MAVLink: not in the recorded sessions (GCS.json: unreached)"),
}


def parse_lean_defs(text):
    """{full Lean name: (params [(name, type)], return type)} of the `def`s of Estimator_lib (namespaces tracked)."""
    out = {}
    ns = []
    for line in text.split("\n"):
        m = re.match(r"^namespace (\S+)$", line)
        if m:
            ns.append(m.group(1))
            continue
        m = re.match(r"^end (\S+)$", line)
        if m and ns and ns[-1] == m.group(1):
            ns.pop()
            continue
        m = re.match(r"^(?:partial )?def (\S+) (.*)$", line)
        if not m or not ns:
            continue
        name, rest = m.group(1), m.group(2)
        params, i = [], 0
        while i < len(rest) and rest[i] == "(":
            d, j = 0, i
            while True:
                if rest[j] == "(":
                    d += 1
                elif rest[j] == ")":
                    d -= 1
                    if d == 0:
                        break
                j += 1
            inner = rest[i + 1:j]
            pn, _, pt = inner.partition(" : ")
            params.append((pn.strip(), re.sub(r"\s*:=.*$", "", pt).strip()))
            i = j + 1
            while i < len(rest) and rest[i] == " ":
                i += 1
        if not rest[i:].startswith(": "):
            continue
        ret = re.sub(r"\s*:=.*$", "", rest[i + 2:]).strip()
        out[".".join(ns + [name])] = (params, ret)
    return out


def split_top(t, sep="×"):
    out, d, cur = [], 0, ""
    for ch in t:
        if ch in "([{":
            d += 1
        elif ch in ")]}":
            d -= 1
        if ch == sep and d == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    out.append(cur.strip())
    return out


def enum_ofint(text, enum):
    """the enumerators of `enum` (a full Lean name) and their values, from its generated `toInt`"""
    short = enum.split(".", 1)[1]                 # Estimator_lib.X.Y -> X.Y
    parts = short.split(".")
    nm = parts[-1]
    pat = re.compile(r"^def %s\.toInt : %s → (\w+)\n((?:  \| \.\w+ => \([^)]*\)\n)+)" % (re.escape(nm), re.escape(nm)), re.M)
    for m in pat.finditer(text):
        # the namespace of this definition must be the enum's
        before = text[:m.start()]
        opened = re.findall(r"^(namespace|end) (\S+)$", before, re.M)
        st = []
        for k, n in opened:
            if k == "namespace":
                st.append(n)
            elif st and st[-1] == n:
                st.pop()
        if ".".join(st[1:] + [nm]) == short:
            arms = re.findall(r"\| \.(\w+) => \(([-\d]+) : \w+\)", m.group(2))
            return m.group(1), arms
    return None, None


def may_wait(text):
    """(Phase 5c) the World's functions that may wait for input lines: those that reach EstScheduler::step (the World's
    lock-step waits: `delay`, `delay_microseconds`, `wait_for_sample`, the calibrations), by the Lean call graph of the
    translation (a name inside a namespace resolved there first, then globally)."""
    bodies, ns, cur = {}, [], None
    for line in text.split("\n"):
        m = re.match(r"^namespace (\S+)", line)
        if m:
            ns.append(m.group(1))
            cur = None
            continue
        m = re.match(r"^end (\S+)$", line)
        if m and ns and ns[-1] == m.group(1):
            ns.pop()
            cur = None
            continue
        m = re.match(r"^(?:partial )?def (\S+)", line)
        if m:
            cur = ".".join(ns[1:] + [m.group(1)]) if ns and ns[0] == "Estimator_lib" else ".".join(ns + [m.group(1)])
            bodies[cur] = []
            continue
        if cur is not None:
            bodies[cur].append(line)
    names = set(bodies)
    calls = {}
    for f, b in bodies.items():
        pre = f.rsplit(".", 1)[0] + "." if "." in f else ""
        out = set()
        for tok in set(re.findall(r"[A-Za-z_][\w'.]*", "\n".join(b))):
            tok = tok[len("Estimator_lib."):] if tok.startswith("Estimator_lib.") else tok
            if pre + tok in names:
                out.add(pre + tok)
            elif tok in names:
                out.add(tok)
        calls[f] = out
    wait = {"EstScheduler.step"}
    changed = True
    while changed:
        changed = False
        for f, cs in calls.items():
            if f not in wait and cs & wait:
                wait.add(f)
                changed = True
    return wait


# (Phase 5c) World functions that may wait but whose calls are not repeated (no snapshot of the state is kept: AP_AHRS's
# update runs on every loop and waits only on the DCM's gyro re-initialization, which the recorded flights do not reach): a
# wait that runs out of lines there is reported (`cpp2lean::world_unexpected_wait`, the replay's log)
NO_RETRY = re.compile(r"^(AP_AHRS|AP_AHRS_DCM)\.")


def wait_body(body, lean, report):
    """(Phase 5c) the adapter of a World function that may wait for input lines (`may_wait`): the World is never fed
    ahead of the memory side (lean/VehicleReplay.lean), so a wait of the World's code can run out of lines; the
    translation then sees synthetic lines (reference/hal/est_scheduler.cpp) and marks the point (`est_mark 3`). The call
    is made on a copy of the state: when it ran out, the memory is set back to before the call, the driver runs the
    lock-step points and events of the call up to that point (the reference's, at their lines; `cpp2lean::world_events`,
    which returns how many events are done) with the World as the call left it (the values the events read: a parameter
    saved or notified), then the World is set back to before the call and the driver writes the output line and reads and
    feeds the next line (`cpp2lean::world_next`), and the call is repeated; the events done are dropped from the log of
    the call that completes."""
    i = next(k for k, l in enumerate(body) if l.startswith("  let (w0, eo0, armed) ← modifyGet"))
    j = next(k for k, l in enumerate(body) if l.startswith("  modify fun m => { m with w := w, eo :="))
    pre, core, post = body[:i], body[i:j + 1], body[j + 1:]
    check = "(← get).w.est_scheduler._exhausted && (← PMem.hal \"cpp2lean::world_more\" 0 #[]) != 0"
    if NO_RETRY.match(lean):
        report.setdefault("wait_no_retry", []).append(lean)
        return pre + core + ["  if %s then" % check, "    discard <| PMem.hal \"cpp2lean::world_unexpected_wait\" 0 #[]"] + post
    report.setdefault("wait_retry", []).append(lean)
    out = pre + ["  let mut pdone : UInt64 := 0", "  repeat", "    let m0 ← get"]
    out += ["  " + l for l in core]
    out += ["    if %s then" % check,
            "      let eo := (← get).eo",
            "      let wa := (← get).w",
            "      set { m0 with eo := eo, w := wa }",
            "      pdone ← PMem.hal \"cpp2lean::world_events\" 0 #[pdone]",
            "      modify fun m => { m with w := m0.w }",
            "      discard <| PMem.hal \"cpp2lean::world_next\" 0 #[]",
            "      continue",
            "    modify fun m => { m with eo := m.eo.extract pdone.toNat m.eo.size }"]
    out += ["  " + l for l in post]
    out += ["  return default"]
    return out


def main():
    sig = json.load(open(os.path.join(ROOT, "ardupilot", "out", "Estimator", "Estimator_lib.signatures.json")))
    ltext = open(os.path.join(ROOT, "ardupilot", "out", "Estimator", "Estimator_lib.lean")).read()
    defs = parse_lean_defs(ltext)
    waits = may_wait(ltext)
    adapters = json.load(open(os.path.join(OUT, "Vehicle_lib.bridge.json")))
    objaddr = json.load(open(os.path.join(OUT, "bridge_objects.json")))
    methods = {}
    for c in sig["classes"]:
        for m in c.get("methods", []):
            methods.setdefault((c["cxx"], m["cxx"]), []).append(m)
    world = {w["class"]: w for w in sig["world"] if w.get("class")}
    heap = {h["class"]: h for h in sig["heap"]}
    L = ["import ParamMemoryV", "import GCSMemoryV", "import VehicleMemoryV", "", "/-!",
         "GENERATED by ardupilot/vehicle/gen_bridge.py (do not edit): the adapters of the estimator bridge (README.md \"Phase 5:",
         "the estimator bridge\"). The vehicle translation calls each estimator function through its adapter here; an adapter",
         "marshals the arguments between the byte memory (clang's layouts) and the value World inside the memory state (`w`),",
         "sets the World's boundary inputs that are vehicle state from the memory state, calls the World's translation and",
         "stores the World, the output log and the out-parameters back. No adapter computes an estimator value.", "-/", "",
         "open FloatLib.Floats (Binary32 Binary64)", "", "set_option linter.unusedVariables false", "set_option maxRecDepth 4000", "",
         "namespace VehicleBridge", "", "open Estimator_lib", "",
         "/-- The HAL's armed flag (`hal.util->get_soft_armed()`, `Mem.armed`) as every reader in the World reads it: the IMU",
         "stand-in, AP_RTC, AP_DAL, AP_AHRS and its DCM, AP_Baro. -/",
         "def setArmed (w : World) (armed : Bool) : World :=",
         "  { w with heap'AP_InertialSensor_SITL'inp := { w.heap'AP_InertialSensor_SITL'inp with get_soft_armed := armed },",
         "           rtc'inp := { w.rtc'inp with get_soft_armed := armed },",
         "           heap'AP_DAL'inp := { w.heap'AP_DAL'inp with get_soft_armed := armed },",
         "           barometer'inp := { w.barometer'inp with get_soft_armed := armed },",
         "           ahrs'inp := { w.ahrs'inp with get_soft_armed := armed, dcm := { w.ahrs'inp.dcm with get_soft_armed := armed } } }", ""]
    enums_done = {}
    report = {"generated": [], "hand": [], "not_in_world": []}

    def ofint(enum):
        if enum in enums_done:
            return enums_done[enum]
        under, arms = enum_ofint(ltext, enum)
        if arms is None:
            sys.exit("gen_bridge: no toInt for %s" % enum)
        fn = "ofInt'" + re.sub(r"\W", "_", enum.split(".", 1)[1])
        L.append("/-- `%s` from its value (the enumerators' values from its toInt) -/" % enum)
        L.append("def %s (v : %s) : %s :=" % (fn, LD[{"Int32": "int32_t", "UInt8": "uint8_t", "Int8": "int8_t", "UInt16": "uint16_t", "Int16": "int16_t", "UInt32": "uint32_t"}[under]][1], enum))
        for k, (e, v) in enumerate(arms):
            L.append("  %sif v == (%s : %s) then .%s" % ("" if k == 0 else "else ", v, under, e))
        L.append("  else default")
        L.append("")
        enums_done[enum] = (fn, under)
        return enums_done[enum]

    def leaf_map(desc_leaves, world_leaves):
        """[(memory leaf, World leaf)] matched by the C++ path"""
        lay = {l["path"]: l for l in desc_leaves}
        out = []
        for wl in world_leaves:
            ml = lay.get(wl["cxx"])
            if ml is None:
                raise KeyError("no layout leaf %s (have %s)" % (wl["cxx"], list(lay)))
            out.append((ml, wl))
        return out

    def load_rec(addr, desc, wleaves, lean_type, body, tag):
        """memory record at addr -> a World State value bound to `tag`"""
        tree = {}
        for k, (ml, wl) in enumerate(leaf_map(desc["leaves"], wleaves)):
            v = "%s'%d" % (tag, k)
            if ml["width"] is not None:
                body.append("  let %s := (← PMem.ldBits %s %d %d).to%s" % (v, addr, ml["bitoff"], ml["width"], LD[wl["type"]][1]))
            else:
                body.append("  let %s ← PMem.ld%s (%s + %d)" % (v, LD[ml["type"]][0], addr, ml["off"]))
            node = tree
            ps = wl["lean"].split(".")
            for p in ps[:-1]:
                node = node.setdefault(p, {})
            node[ps[-1]] = v

        def lit(n):
            return "{ " + ", ".join("%s := %s" % (k, lit(v) if isinstance(v, dict) else v) for k, v in n.items()) + " }"
        body.append("  let %s : %s := %s" % (tag, lean_type, lit(tree)))

    def store_rec(addr, desc, wleaves, val, body):
        for ml, wl in leaf_map(desc["leaves"], wleaves):
            x = "%s.%s" % (val, wl["lean"])
            if ml["width"] is not None:
                body.append("  PMem.stBits %s %d %d (%s).toUInt64" % (addr, ml["bitoff"], ml["width"], x))
            else:
                # (Phase 5c) a member of an enumeration type the World stores as its underlying integer (the World
                # leaf's type: `AirspeedEstimateType airspeed_estimate_type` as uint8_t)
                lt = ml["type"] if ml["type"] in LD else wl["type"]
                body.append("  PMem.st%s (%s + %d) %s" % (LD[lt][0], addr, ml["off"], x))

    for a in adapters:
        q = a["q"]
        name = a["adapter"].split(".", 1)[1]
        params = []
        if a["method"]:
            params.append("(this : UInt64)")
        if a["ret"]["pass"] in ("sret", "copy"):
            params.append("(sret : UInt64)")
        for k, p in enumerate(a["params"]):
            params.append("(a%d : %s)" % (k, p["type"]["lean"] if p["pass"] == "value" else "UInt64"))
        for nm, fq in a["inputs"]:
            # `pre_*`: a translated member function the World's translation drops, run on the memory before the World
            # call (Phase 5b: AP_GPS::init's convert_parameters); the others are values of vehicle state
            params.append("(%s : PMem.M %s)" % (nm, "Unit" if nm.startswith("pre_") else "UInt32"))
        rp = a["ret"]["pass"]
        rty = {"void": "Unit", "sret": "Unit", "object": "UInt64", "copy": "UInt64"}.get(rp) or a["ret"]["type"]["lean"]
        head = "def %s %s : PMem.M %s := do" % (name, " ".join(params), rty)
        doc = "/-- `%s : %s` -/" % (q, a["sig"])

        def default_body():
            b = []
            if rp == "sret":
                b.append("  discard <| PMem.memset sret 0 %d" % a["ret"]["type"]["size"])
                b.append("  return ()")
            elif rp == "void":
                b.append("  return ()")
            else:
                b.append("  return default")
            return b
        if q in ACCESSORS and ACCESSORS[q] not in objaddr:
            L += ["/-- `%s : %s`: the object is not a member of `copter` in this build (the adapters of its class ignore the address): 0. Written by hand: an accessor. -/" % (q, a["sig"]),
                  head, "  return 0", ""]
            report["hand"].append((q, "accessor: no object in the memory"))
            continue
        if q in ACCESSORS:
            L += ["/-- `%s : %s`: the object's address in the memory (`copter.%s`, clang's offset). Written by hand: an accessor. -/" % (q, a["sig"], ACCESSORS[q]),
                  head, "  return 0x%x" % objaddr[ACCESSORS[q]], ""]
            report["hand"].append((q, "accessor: the object's address"))
            continue
        if q in HAND:
            text, why = HAND[q]
            L += ["/-- `%s : %s`. Written by hand: %s. -/" % (q, a["sig"], why), head]
            if text.startswith("pure") or text.startswith("do\n"):
                L.append("  " + text)
            else:
                L.append("  " + text)
                L += default_body()
            L.append("")
            report["hand"].append((q, why))
            continue
        cls, _, mname = q.rpartition("::")
        cands = [m for m in methods.get((cls, mname), []) if len(m["params"]) == len(a["params"])]
        if not cands and q in PASSING_CHECKS:
            # the estimator classes' own pre-arm checks, not in the World's translation: they pass (the reference arms
            # with checks at 41.855 s: COMMAND_ACK of MAV_CMD_COMPONENT_ARM_DISARM with MAV_RESULT_ACCEPTED); the
            # failure strings (formatting, D10) are not written
            L += ["/-- `%s : %s`. Not in the estimator World's translation: an estimator pre-arm check, which passes in the "
                  "recorded sessions (the reference arms with checks); the call is recorded (`PMem.bridge`). -/" % (q, a["sig"]),
                  head, "  PMem.bridge %s" % json.dumps(q), "  return true", ""]
            report["not_in_world"].append(q)
            continue
        if not cands:
            L += ["/-- `%s : %s`. Not in the estimator World's translation: the call is recorded (`PMem.bridge`) and gives the default. -/" % (q, a["sig"]),
                  head, "  PMem.bridge %s" % json.dumps(q)] + default_body() + [""]
            report["not_in_world"].append(q)
            continue
        m = cands[0]
        if len(cands) > 1:
            # overloads with as many parameters: by the parameters' C++ types
            def norm(t):
                return re.sub(r"\s+", "", re.sub(r"\b(const|struct|class)\b", "", t)).replace("Vector3f", "Vector3<float>")
            want = [norm(p["type"].get("name") or "") for p in a["params"]]
            m = next((c for c in cands if [norm(p["type"]) for p in c["params"]] == want), cands[0])
        lean = m["lean"]
        if lean not in defs:
            sys.exit("gen_bridge: %s: no Lean definition %s" % (q, lean))
        lps, lret = defs[lean]
        # the World object
        if cls in world:
            wo = world[cls]
            spath = "w.%s" % wo["name"]
            ipath = "w.%s'inp" % wo["name"] if any(p[0] == wo["name"] + "'inp" for p in wo["parts"]) else None

            def sset(v, wo=wo):
                return "{ w with %s := %s }" % (wo["name"], v)
        elif cls == "AP_AHRS_View":
            spath = "w.heap'AP_AHRS_View[WPtr.index w.ahrs._view]!"
            ipath = None

            def sset(v):
                return "{ w with heap'AP_AHRS_View := w.heap'AP_AHRS_View.set! (WPtr.index w.ahrs._view) (%s) }" % v
        else:
            sys.exit("gen_bridge: %s: no World object of class %s" % (q, cls))
        body = []
        armed = "w" in m["reads"] or m["uses_inp"] or "w" in m["writes"]
        writes = bool(set(m["writes"]) & {"s", "w", "o"})
        inl = []
        for nm, fq in a["inputs"]:
            if nm.startswith("pre_"):
                # the dropped call, before the World is taken out of the memory state (its HAL delays step the World)
                body.append("  %s" % nm)
            if nm == "link_chan":
                # (Phase 5c) AP_AHRS::send_ekf_status_report(link): `link.get_chan()`, a boundary input of the World's
                # translation, from the translated GCS_MAVLINK::get_chan on the link object (passed by the call site)
                fn, under = ofint("Estimator_lib.mavlink_channel_t")
                body.append("  let ch ← %s" % nm)
                inl.append("  w := { w with ahrs'inp := { w.ahrs'inp with get_chan := %s ch } }" % fn)
            if nm == "time_flying_ms":
                # AP_DAL's boundary inputs that are vehicle state: AP_Vehicle::get_time_flying_ms (the translated vehicle
                # function, passed by the call site), the HAL's free memory (lockstep.cpp's Util: 512 KiB), no wheel encoder
                body.append("  let tf ← %s" % nm)
                inl.append("  w := { w with heap'AP_DAL'inp := { w.heap'AP_DAL'inp with get_time_flying_ms := tf, available_memory := 524288, nonnull := false, num_sensors := 0 } }")
        args = []
        cxx = [p for p in m["params"]]
        k = 0
        mutrefs = []
        tbufs = []      # (Phase 5d) the `char *` parameters (text sinks)
        words = {}      # (Phase 5d) record parameters the World holds as their bit pattern: k -> the memory leaf
        try:
            for pn, pt in lps:
                if pn == "s":
                    args.append(spath)
                elif pn == "w":
                    args.append("w")
                elif pn == "o":
                    args.append("eo0")
                elif pn == "inp":
                    if ipath is None:
                        raise KeyError("inputs of %s" % cls)
                    args.append(ipath)
                elif pn == "p":
                    raise KeyError("Params")
                else:
                    while k < len(cxx) and cxx[k].get("boundary"):
                        k += 1      # (Phase 5c) a boundary object (`GCS_MAVLINK &link`): its reads are the World's inputs
                    if k >= len(cxx):
                        raise KeyError("parameter %s" % pn)
                    wp, mp = cxx[k], a["params"][k]
                    if wp.get("ref") == "tbuf":
                        # (Phase 5d, cpp2lean.py --text-buffers) a `char *buf` parameter is a text sink: the World starts
                        # from `CText.none` (the translation rejects reading a `char *` parameter's incoming text) and
                        # returns the text it wrote; the adapter pushes `Output.text_sink buf text`, which the vehicle's
                        # drain formats into the caller's buffer with the translated AP_HAL::Util::snprintf
                        if mp["pass"] != "value" or mp["type"]["kind"] != "ptr" or mp["type"].get("name") != "char":
                            raise KeyError("text parameter %s not a `char *`" % pn)
                        args.append("Estimator_lib.CText.none")
                        tbufs.append(k)
                        mutrefs.append((k, None, wp))
                        k += 1
                        continue
                    if mp["pass"] == "value":
                        v = "a%d" % k
                        if wp.get("enum"):
                            fn, under = ofint(wp["enum"])
                            args.append("(%s %s)" % (fn, v if LD.get(wp["under"], (None, None))[1] == mp["type"]["lean"] else "(%s.to%s)" % (v, under)))
                        elif pt == "USize" and mp["type"]["lean"] == "UInt64":
                            # (Phase 5d) `size_t` (AP_Baro::arming_checks's buflen): the World's `USize`, the memory's
                            # 64-bit value (the target's size_t)
                            args.append("(%s.toUSize)" % v)
                        else:
                            args.append(v)
                    elif mp["pass"] in ("ref", "rec"):
                        td = mp["type"]
                        if td["kind"] == "rec" and not wp.get("leaves") and wp.get("scalar") and wp["type"] in LD:
                            # (Phase 5d) a union of one width the World holds as its bit pattern (`nav_filter_status`:
                            # its bit-field struct `flags` and `uint32_t value`, AP_Nav_Common.h; the World's `status` is
                            # the word): the memory's leaf of that type at offset 0 covering the whole record, loaded and
                            # (for `T &`) stored back
                            wl = next((l for l in td["leaves"] if l["off"] == 0 and l["width"] is None and
                                       LD.get(l["type"]) == LD[wp["type"]]), None)
                            if wl is None or td["size"] != {"U8": 1, "I8": 1, "U16": 2, "I16": 2, "U32": 4, "I32": 4, "U64": 8, "I64": 8}.get(LD[wp["type"]][0]):
                                raise KeyError("record parameter without leaves")
                            body.append("  let r%d ← PMem.ld%s a%d  -- `%s` (the union's word)" % (k, LD[wp["type"]][0], k, wl["path"]))
                            args.append("r%d" % k)
                            words[k] = wl
                        elif td["kind"] == "rec":
                            if not wp.get("leaves"):
                                raise KeyError("record parameter without leaves")
                            load_rec("a%d" % k, td, wp["leaves"], wp["lean_type"], body, "r%d" % k)
                            args.append("r%d" % k)
                        else:
                            body.append("  let r%d ← PMem.ld%s a%d" % (k, LD[{"Binary32": "float", "Binary64": "double", "Bool": "bool"}.get(td["lean"], td["name"] or "")][0] if td["lean"] in ("Binary32", "Binary64", "Bool") else
                                                                        {"UInt8": "U8", "Int8": "I8", "UInt16": "U16", "Int16": "I16", "UInt32": "U32", "Int32": "I32", "UInt64": "U64", "Int64": "I64"}[td["lean"]], k))
                            args.append("r%d" % k)
                        if wp.get("ref") == "mut":
                            mutrefs.append((k, td, wp))
                    else:
                        raise KeyError("pass %s" % mp["pass"])
                    k += 1
            while k < len(cxx) and cxx[k].get("boundary"):
                k += 1
            if k != len(cxx):
                raise KeyError("parameters: %d of %d" % (k, len(cxx)))
            comps = []
            if "s" in m["writes"]:
                comps.append("s'")
            if "w" in m["writes"]:
                comps.append("w'")
            if "o" in m["writes"]:
                comps.append("o'")
            for kk, _, _ in mutrefs:
                comps.append("q%d" % kk)
            if m["ret"] != "void":
                comps.append("res")
            nret = len(split_top(lret))
            if not comps:
                raise KeyError("no result")
            if nret != len(comps):
                raise KeyError("result arity %d (Lean %s) for %s" % (len(comps), lret, comps))
            call = "%s %s" % (lean, " ".join(args))
            if writes:
                # the World and the log taken out of the memory state for the call (no second reference: the World's
                # in-place updates stay in place), stored back after it
                body.append("  let (w0, eo0, armed) ← modifyGet fun m => ((m.w, m.eo, m.armed), { m with w := Estimator_lib.World.init, eo := #[] })")
            else:
                body.append("  let m ← get")
                body.append("  let (w0, eo0, armed) := (m.w, m.eo, m.armed)")
            body.append("  let mut w := %s" % ("setArmed w0 armed" if armed else "w0"))
            body += inl
            body.append("  let %s := %s" % (comps[0] if len(comps) == 1 else "(" + ", ".join(comps) + ")", call))
            if "w'" in comps:
                body.append("  w := w'")
            if "s'" in comps:
                body.append("  w := %s" % sset("s'"))
            if writes:
                body.append("  modify fun m => { m with w := w, eo := %s }" % ("o'" if "o'" in comps else "eo0"))
            for kk, td, wp in mutrefs:
                if kk in tbufs:
                    body.append("  modify fun m => { m with eo := m.eo.push (Estimator_lib.Output.text_sink a%d q%d) }" % (kk, kk))
                elif kk in words:
                    body.append("  PMem.st%s a%d q%d" % (LD[wp["type"]][0], kk, kk))
                elif td["kind"] == "rec":
                    store_rec("a%d" % kk, td, wp["leaves"], "q%d" % kk, body)
                else:
                    sfx = {"Binary32": "F32", "Binary64": "F64", "Bool": "B", "UInt8": "U8", "Int8": "I8", "UInt16": "U16", "Int16": "I16",
                           "UInt32": "U32", "Int32": "I32", "UInt64": "U64", "Int64": "I64"}[td["lean"]]
                    body.append("  PMem.st%s a%d q%d" % (sfx, kk, kk))
            if rp == "void":
                body.append("  return ()")
            elif rp == "sret":
                if not m.get("ret_leaves"):
                    raise KeyError("record result without leaves")
                store_rec("sret", a["ret"]["type"], m["ret_leaves"], "res", body)
                body.append("  return ()")
            elif rp == "copy":
                # (Phase 5c, Vehicle.json `bridge_pointer_results`) a `const T *` result pointing into the World
                # (`AP_AHRS::get_secondary_estimates`: a WPtr to one of AP_AHRS's member objects): the object's leaves
                # stored at clang's layout into the caller's temporary (sret) by a generated `store'T`, whose address is
                # the result; the World's null pointer -> 0
                rname = a["ret"]["type"]["name"]
                rl = next((p for ms in methods.values() for mm in ms for p in mm["params"]
                           if p["type"] == rname and p.get("leaves")), None)
                if rl is None:
                    raise KeyError("no World leaves of %s" % rname)
                st = rl["lean_type"].split(".", 1)[1]
                helper = "store'" + re.sub(r"\W", "_", rname)
                if helper not in enums_done:
                    # the record's State fields and their Lean types (an enumeration stored as its value, toInt)
                    ns = st.rsplit(".", 1)[0]
                    blk = re.search(r"^namespace %s\n(?:.*\n)*?structure State where\n((?:  .*\n)+?)deriving" % re.escape(ns), ltext, re.M)
                    ftypes = dict(re.findall(r"^  (\w+) : (\S+)", blk.group(1), re.M)) if blk else {}
                    H = ["/-- (Phase 5c) the World's `%s` stored at clang's layout at `a` (the copy behind a pointer result) -/" % rname,
                         "def %s (a : UInt64) (v : %s) : PMem.M Unit := do" % (helper, rl["lean_type"])]
                    for ml, wl in leaf_map(a["ret"]["type"]["leaves"], rl["leaves"]):
                        x = "v.%s" % wl["lean"]
                        ft = ftypes.get(wl["lean"])
                        if "." not in wl["lean"] and ft and ft not in ("Bool", "Binary32", "Binary64") and not re.match(r"U?Int\d+$", ft):
                            x = "(%s.toInt %s)" % (ft, x)
                        if ml["width"] is not None:
                            H.append("  PMem.stBits a %d %d (%s).toUInt64" % (ml["bitoff"], ml["width"], x))
                        else:
                            lt = ml["type"] if ml["type"] in LD else wl["type"]
                            H.append("  PMem.st%s (a + %d) %s" % (LD[lt][0], ml["off"], x))
                    L.extend(H + [""])
                    enums_done[helper] = True
                arms = re.findall(r"^  \| (\w+)'(\w+)  -- the member object `\1\.\2`", ltext, re.M)
                body.append("  match res with")
                n_arms = 0
                for obj, fld in arms:
                    if not re.search(r"^  %s : %s(?: :=.*)?$" % (re.escape(fld), re.escape(st)), ltext, re.M) or \
                            not any(wo["name"] == obj for wo in world.values()):
                        continue
                    body.append("  | .%s'%s =>" % (obj, fld))
                    body.append("    %s sret w.%s.%s" % (helper, obj, fld))
                    body.append("    return sret")
                    n_arms += 1
                if not n_arms:
                    raise KeyError("no World object of type %s" % st)
                body.append("  | _ => return 0")
            elif rp == "value":
                if m.get("ret_enum"):
                    tl = a["ret"]["type"]["lean"]
                    body.append("  return (%s.toInt res)%s" % (m["ret_enum"], "" if LD.get(m["ret_under"], (0, ""))[1] == tl else ".to" + tl))
                else:
                    body.append("  return res")
            else:
                raise KeyError("result pass %s" % rp)
        except KeyError as e:
            L += ["/-- `%s : %s`. Not adapted (%s): the call is recorded (`PMem.bridge`) and gives the default. -/" % (q, a["sig"], e),
                  head, "  PMem.bridge %s" % json.dumps(q)] + default_body() + [""]
            report["not_in_world"].append("%s (%s)" % (q, e))
            continue
        if lean.split("Estimator_lib.", 1)[-1] in waits and writes:
            body = wait_body(body, lean.split("Estimator_lib.", 1)[-1], report)
        L += ["/-- `%s : %s` -> `%s` -/" % (q, a["sig"], lean), head] + body + [""]
        report["generated"].append(q)
    # (Phase 5b) the estimator's scalar data members that translated code reads directly (`bridge_field_reads`):
    # the value of the World object's field
    fpath = os.path.join(OUT, "Vehicle_lib.bridge_fields.json")
    for fa in (json.load(open(fpath)) if os.path.exists(fpath) else []):
        cls, _, fld = fa["q"].rpartition("::")
        nm = fa["adapter"].split(".", 1)[1]
        if cls == "AP_AHRS_View":
            src = "(w.heap'AP_AHRS_View[WPtr.index w.ahrs._view]!)"
        elif cls in world:
            src = "w.%s" % world[cls]["name"]
        else:
            sys.exit("gen_bridge: field %s: no World object of class %s" % (fa["q"], cls))
        L += ["/-- `%s` (a data member read by translated code): the World object's field -/" % fa["q"],
              "def %s (this : UInt64) : PMem.M %s := do" % (nm, fa["type"]["lean"]),
              "  let w := (← get).w",
              "  return %s.%s" % (src, fld), ""]
        report["generated"].append(fa["q"])
    L += ["end VehicleBridge", ""]
    text = "\n".join(L)
    for d in (OUT, os.path.join(ROOT, "lean")):
        open(os.path.join(d, "VehicleBridge.lean"), "w").write(text)
    json.dump(report, open(os.path.join(OUT, "VehicleBridge.report.json"), "w"), indent=1)
    print("gen_bridge: %d adapters: %d generated, %d written by hand, %d not adapted (not in the World: recorded, default)" % (
        len(adapters), len(report["generated"]), len(report["hand"]), len(report["not_in_world"])))
    for x in report["not_in_world"]:
        print("  not adapted: %s" % x)


if __name__ == "__main__":
    main()
