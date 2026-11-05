#!/usr/bin/env python3
"""Copy two function definitions of the AHRS out of ArduPilot's sources, unmodified, for the AHRS
view translation (ardupilot/translate_ahrs_view.sh): AP_AHRS_View::update (AP_AHRS_View.cpp:61-83)
and AP_AHRS::calc_trig (AP_AHRS_Backend.cpp:93-135) at commit 802db19de1.

The two .cpp files cannot be compiled against the stub headers (their headers reach the EKF, the
INS, GPS and MAVLink), so the translated unit is ardupilot/unity_ahrs_view.cpp: the declarations of
AP_AHRS_View_decls.h, then the two definitions. Each is written to a file of the same name as its
source here, at the same line numbers (the lines before it are blank), so that the translation's
comments and clang's diagnostics cite the ArduPilot lines. The script checks that the first and
last lines are the expected ones and that every copied byte equals the source.

Usage: python3 ardupilot/ahrs/extract.py AP_LIBRARIES_DIR
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PIECES = [("AP_AHRS/AP_AHRS_View.cpp", 61, 83, "void AP_AHRS_View::update()", "}"),
          ("AP_AHRS/AP_AHRS_Backend.cpp", 93, 135, "void AP_AHRS::calc_trig(const Matrix3f &rot,", "}")]


def main():
    lib = sys.argv[1]
    for rel, a, b, first, last in PIECES:
        src = open(os.path.join(lib, rel), "rb").read().decode()
        lines = src.split("\n")
        piece = lines[a - 1:b]
        if piece[0].rstrip() != first or piece[-1].rstrip() != last:
            sys.exit("extract.py: %s:%d-%d is not the expected definition (%r ... %r)" % (rel, a, b, piece[0], piece[-1]))
        text = "\n" * (a - 1) + "\n".join(piece) + "\n"
        assert text.split("\n")[a - 1:b] == piece
        out = os.path.join(HERE, os.path.basename(rel))
        if not os.path.exists(out) or open(out).read() != text:
            with open(out, "w") as f:
                f.write(text)
        print("%s:%d-%d -> ardupilot/ahrs/%s" % (rel, a, b, os.path.basename(rel)))


if __name__ == "__main__":
    main()
