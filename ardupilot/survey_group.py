#!/usr/bin/env python3
"""Group the rejections of a survey log (ardupilot/survey_ekf3.sh) by the translator feature they
need, with counts and example locations (README.md, "Phase 3: EKF data structures").

Usage: python3 ardupilot/survey_group.py LOG [--markdown]
The groups are matched in order (the first matching rule wins); `cpp2lean --survey` reports every
rejected statement, so one source line can count once per rejected construct in it."""
import re
import sys

RULES = [
    ("F1 pointer members, pointers to World objects (other agent)",
     r"member `(frontend|core|yawEstimator|_airspeed|gyro_filtered|accel_filtered|pos)` that is not a data member|pointer or reference type `(const )?(class )?(NavEKF3|NavEKF3_core|EKFGSF_yaw|AP_DAL|AP_DAL_Airspeed) \*`|cast `PointerToBoolean`|cast `NullToPointer`"),
    ("F1 reference members bound to World objects (`dal`, `public_origin`; other agent)",
     r"reference member `(dal|public_origin)`|local reference variable `dal`"),
    ("F1 calls on classes outside the translation (front ends, AP_AHRS, HAL)",
     r"a method of a class that is not translated|type `(const )?(AP_InertialSensor|AP_HAL::HAL|Compass|AP_Baro|AP_AHRS|AP_GPS|HALSITL::Semaphore)`|call of method `(get_earth_field_ga|get_declination|allocation_error)` without an object"),
    ("F13 AP_Param (`frontend->_param` values, AP_Enum conversions, var_info)",
     r"AP_ParamT|parameter class|var_info entry"),
    ("F7 text (GCS send_text, snprintf, vsnprintf, panic, FILE)",
     r"`(send_text|snprintf|vsnprintf)`|panic|`FILE \*`"),
    ("F8 loops bounded by a data member whose type does not bound it (`i <= stateIndexLim`)",
     r"loop whose trip count"),
    ("local `const` references to state that the function writes (`const ftype &q0 = stateStruct.quat[0]`)",
     r"local reference `\w+` to something that may change"),
    ("F10 static locals and mutable globals",
     r"static local variable|reference to global variable"),
    ("survey configuration: AP_Math templates and functions included as translated files (a lib-dir in a translation)",
     r"template `\w+` that is not instantiated|identifier `s` in a member function|overloaded operator|array of class objects `Vector3f|construction of `Location|initializer of member `pos`|`memset` other than|call to library function `random\(\)`"),
    ("HAL clock reads (`AP_HAL::micros`, boundary functions)",
     r"`micros(64)?\(\)`|`millis\(\)`"),
    ("views of the state's struct view (`stateStruct.position.xy() = ...`), calls on returned references",
     r"assignment to something other than|on an object returned by reference"),
    ("definite assignment the checker cannot prove (`ftype SA5_inv; if (...) SA5_inv = ...`)",
     r"may be uninitialized"),
    ("enum ordering comparisons", r"ordering comparison of enum"),
    ("brace initializer lists of objects (`AP_DAL::log_*` records)", r"brace or parenthesized initializer list"),
]


def main():
    path = sys.argv[1]
    md = "--markdown" in sys.argv
    rows = [l.rstrip("\n") for l in open(path) if ": rejected: " in l]
    groups = {name: [] for name, _ in RULES}
    other = []
    for l in rows:
        msg = l.split(": rejected: ", 1)[1]
        for name, rx in RULES:
            if re.search(rx, msg):
                groups[name].append(l)
                break
        else:
            other.append(l)
    groups["other"] = other
    print("%d rejections" % len(rows))
    if md:
        print("| feature | count | examples |")
        print("|---|---|---|")
    for name, ls in groups.items():
        if not ls:
            continue
        ex = []
        for l in ls:
            loc = ":".join(l.split(":")[:2])
            if loc not in ex:
                ex.append(loc)
            if len(ex) == 3:
                break
        if md:
            print("| %s | %d | %s |" % (name, len(ls), ", ".join("`%s`" % e for e in ex)))
        else:
            print("%5d  %s  (e.g. %s)" % (len(ls), name, ", ".join(ex)))
    if other and not md:
        print("other:")
        for l in other:
            print("   " + l)


if __name__ == "__main__":
    main()
