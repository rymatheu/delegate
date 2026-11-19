#!/usr/bin/env python3
"""Hand-checked case of px4_mavlink: a heartbeat out, a parameter request answered, bytes on the
serial-link ports. Run with build/px4venv/bin/python after generating the Python MAVLink dialect:
  build/px4venv/bin/python build/src/mavlink/pymavlink/tools/mavgen.py --lang Python3 \\
    --wire-protocol 2.0 --output build/gen/px4_mavlink/pymav/development.py \\
    build/src/mavlink/message_definitions/v1.0/development.xml

Frames are built with pymavlink from the same message definitions (development.xml at PX4's
mavlink commit), from system 1, component 1 (MAV_SYS_ID, MAV_COMP_ID defaults), MAVLink 2,
unsigned, with the sequence numbers the module's single send counter gives them.
Step 0 (t = 1 s): Mavlink::task_main's first pass with streams: the HEARTBEAT stream (1 Hz in mode
  normal) sends first, seq 0 (HEARTBEAT.hpp): type = vehicle_status.system_type = 0 (no
  vehicle_status yet), autopilot 12 (MAV_AUTOPILOT_PX4), base_mode 1 (CUSTOM_MODE_ENABLED, disarmed),
  custom_mode 65536 (main mode MANUAL = 1 << 16: nav_state 0), system_status 0. Checked: its 21
  bytes, the first 5 words and the first byte of word 5 (the frame continues into PING, seq 1,
  LINK_NODE_STATUS, MISSION_CURRENT).
Step 4: a GCS HEARTBEAT (255/190) on mavlink_rx_*; step 8: PARAM_REQUEST_READ for "MAV_SYS_ID"
  (index -1) to 1/1. The receiver thread is blocked in poll on the port; the step's bytes make it
  runnable, it parses the frame and hands the request to MavlinkParametersManager, whose send()
  in the next pass of the module's task sends PARAM_VALUE in the same step (seq 4, after the four
  messages of step 0): param_id MAV_SYS_ID, value = the int32 1 as its bits, type 6 (INT32),
  param_count = the parameters of this module's table, param_index = MAV_SYS_ID's position in it
  (px4::parameters is sorted by name: the stack's 743). Checked: the whole 37-byte frame.
Step 12: PARAM_SET MAV_SYS_ID = 5 (INT32). The stack's parameters are served read-only
  (px4.txt `params readonly`): PX4's handler calls param_set, which the store refuses, then
  answers as it always does with PARAM_VALUE of the stored value (mavlink_parameters.cpp:124-136):
  MAV_SYS_ID still 1, seq 5. Checked: the whole frame.
"""
import json
import os
import struct
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
HARNESS = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
sys.path.insert(0, os.path.join(HARNESS, 'py'))
sys.path.insert(0, os.path.join(HARNESS, 'build/gen/px4_mavlink/pymav'))
import px4_case  # noqa: E402
import development as mav  # noqa: E402

T = lambda k: 1000000 + 2500 * k  # noqa: E731


def rx(b):
    d = {'mavlink_rx_len': len(b)}
    b = b + bytes((-len(b)) % 4)
    d.update({f'mavlink_rx_{i}': int.from_bytes(b[4 * i:4 * i + 4], 'little') for i in range(len(b) // 4)})
    return d


def tx_words(b):
    b = b + bytes((-len(b)) % 4)
    return [int.from_bytes(b[4 * i:4 * i + 4], 'little') for i in range(len(b) // 4)]


gcs = mav.MAVLink(None, srcSystem=255, srcComponent=190)
steps = [{'t_us': T(k)} for k in range(20)]
steps[4].update(rx(gcs.heartbeat_encode(mav.MAV_TYPE_GCS, mav.MAV_AUTOPILOT_INVALID, 0, 0,
                                        mav.MAV_STATE_ACTIVE).pack(gcs)))
steps[8].update(rx(gcs.param_request_read_encode(1, 1, b'MAV_SYS_ID', -1).pack(gcs)))
five = struct.unpack('<f', struct.pack('<i', 5))[0]
steps[12].update(rx(gcs.param_set_encode(1, 1, b'MAV_SYS_ID', five, mav.MAV_PARAM_TYPE_INT32).pack(gcs)))

params = px4_case.defaults('px4_mavlink')
names = sorted(params)
ap = mav.MAVLink(None, srcSystem=1, srcComponent=1)
ap.seq = 0
hb = ap.heartbeat_encode(0, mav.MAV_AUTOPILOT_PX4, 1, 65536, 0).pack(ap)
ap.seq = 4
one = struct.unpack('<f', struct.pack('<i', 1))[0]
pv = ap.param_value_encode(b'MAV_SYS_ID', one, mav.MAV_PARAM_TYPE_INT32, len(names),
                           names.index('MAV_SYS_ID')).pack(ap)
ap.seq = 5
pv_set = ap.param_value_encode(b'MAV_SYS_ID', one, mav.MAV_PARAM_TYPE_INT32, len(names),
                               names.index('MAV_SYS_ID')).pack(ap)
w0 = tx_words(hb)
expect = {0: {f'mavlink_tx_{i}': w for i, w in enumerate(w0[:5])}, 8: {'mavlink_tx_len': len(pv)}}
expect[8].update({f'mavlink_tx_{i}': w for i, w in enumerate(tx_words(pv))})
expect[8].update({f'mavlink_tx_{i}': 0 for i in range(len(tx_words(pv)), 128)})
expect[8]['px4_mavlink_errors'] = 0
expect[12] = {'mavlink_tx_len': len(pv_set), 'px4_mavlink_errors': 0}
expect[12].update({f'mavlink_tx_{i}': w for i, w in enumerate(tx_words(pv_set))})
outs = px4_case.record('px4_mavlink', params, steps, expect, __doc__)
assert outs[0]['mavlink_tx_5'] & 0xff == hb[20], 'last heartbeat byte'
print('heartbeat (21 bytes) and PARAM_VALUE (37 bytes) as built by hand')
