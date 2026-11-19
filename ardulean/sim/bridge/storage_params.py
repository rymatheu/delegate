"""Set parameters directly in an ArduCopter storage image (AP_Param's EEPROM format, revision 6), without booting a vehicle.

The image starts with a 4-byte header ("PA", revision 6, 0); then come entries of a 4-byte header (key 9 bits as key_low 8
+ key_high 1, type 5 bits, group element 18 bits; AP_Param::Param_header) followed by the value (INT8 1 byte, INT16 2,
INT32 4, FLOAT 4, VECTOR3F 12 bytes), up to the sentinel header (key 0x1FF, type 0x1F, group 0xFF). AP_Param stores only
parameters whose values differ from the code defaults. `with_params` overwrites the value of an entry that exists and
appends a new entry before the sentinel otherwise.

KNOWN: the (key, type, group element) of the parameters the formation sessions set this way (sim/fly_gorge_formation.py
--udp), at the pinned ArduPilot: MAV_SYSID is GCS group element 1 of k_param_gcs (key 260), INT32 since
GCS::convert_parameters widened it; WP_YAW_BEHAVIOR is k_param_wp_yaw_behavior (key 26), INT8. Both read off boot images
that ArduCopter wrote after a PARAM_SET of each.
"""
import struct

TYPES = {1: ("<b", 1), 2: ("<h", 2), 3: ("<i", 4), 4: ("<f", 4)}
KNOWN = {"MAV_SYSID": (260, 3, 1), "WP_YAW_BEHAVIOR": (26, 1, 0)}
SENTINEL = (0x1FF, 0x1F, 0xFF)
SIZES = {1: 1, 2: 2, 3: 4, 4: 4, 5: 12}


def _header(key, typ, grp):
    return struct.pack("<I", (key & 0xFF) | (typ << 8) | ((key >> 8) << 13) | (grp << 14))


def entries(image: bytes):
    """[(offset, key, type, group, value bytes)] and the sentinel's offset."""
    if image[0:3] != b"PA\x06":
        raise ValueError("not an AP_Param revision 6 image")
    o, out = 4, []
    while True:
        h = struct.unpack_from("<I", image, o)[0]
        key, typ, grp = (h & 0xFF) | (((h >> 13) & 1) << 8), (h >> 8) & 0x1F, h >> 14
        if (key, typ) == SENTINEL[:2]:
            return out, o
        out.append((o, key, typ, grp, image[o + 4:o + 4 + SIZES[typ]]))
        o += 4 + SIZES[typ]


def with_params(image: bytes, params: dict) -> bytes:
    """The image with the named parameters (names of KNOWN) set to the given values."""
    b = bytearray(image)
    for name, value in params.items():
        key, typ, grp = KNOWN[name]
        fmt, n = TYPES[typ]
        val = struct.pack(fmt, int(value) if typ != 4 else float(value))
        es, end = entries(bytes(b))
        hit = [o for o, k, t, g, _ in es if (k, t, g) == (key, typ, grp)]
        if hit:
            b[hit[0] + 4:hit[0] + 4 + n] = val
            continue
        sent = bytes(b[end:end + 4])
        new = _header(key, typ, grp) + val
        if any(b[end + 4:end + 4 + len(new)]) or end + len(new) + 4 > len(b):
            raise ValueError("no free space after the sentinel")
        b[end:end + len(new)] = new
        b[end + len(new):end + len(new) + 4] = sent
    return bytes(b)
