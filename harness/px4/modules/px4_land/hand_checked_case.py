#!/usr/bin/env python3
"""Writes hand-checked-case.json for px4_land: three local position ticks worked out from
LandDetector::Run (LandDetector.cpp:81-205) and MulticopterLandDetector (MulticopterLandDetector.cpp),
PX4's default parameters. The local position carries no valid field (all flags false), the IMU
topics are not published (acceleration and rates 0), the thrust setpoint is never published (0).

Step 0 (t = 2 s): the first run (timestamp 0 -> parameters read). Not armed (no actuator_armed),
  so the ground contact, maybe landed and landed inputs are true, and their hysteresis start true
  (LandDetector.h:146-148); freefall's input is true (|a| = 0 < 2) but its hysteresis starts
  false and needs 0.3 s. The local position is 0 s old but v_z_valid and z_valid are false, so
  vertical movement is true; v_xy_valid false, so no horizontal movement; thrust 0 is low; no
  range sensor, so the close-to-ground check is skipped; at rest, since the last motion was at
  0 s, 2 s ago (> 1 s). The message is published (first time): landed, maybe landed, ground
  contact, low throttle, vertical movement, close-to-ground-or-skipped and at rest true.
Step 1 (t = 2.0025 s): nothing changed and less than 1 s passed: not published.
Step 2 (t = 2.005 s): actuator_armed armed. Ground contact's input needs no vertical movement:
  false, and a hysteresis goes to false at once; maybe landed: no vertical estimate (v_z_valid
  false), so it needs the 8 s minimum-thrust hysteresis, which started at 2 s: false; landed:
  armed, so maybe landed's state: false; at rest needs landed: false. Published (changed).
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'px4_common'))
from hand_case import write

HERE = os.path.dirname(os.path.abspath(__file__))


def inp(t, armed=False):
    d = {'t_us': t, 'vehicle_local_position_updated': True, 'vehicle_local_position_timestamp': t,
         'vehicle_local_position_timestamp_sample': t}
    if armed:
        d.update({'actuator_armed_updated': True, 'actuator_armed_timestamp': t,
                  'actuator_armed_armed': True})
    return d


ld = lambda **k: {f'vehicle_land_detected_{n}': v for n, v in k.items()}
o0 = ld(updated=True, timestamp=2000000, landed=True, maybe_landed=True, ground_contact=True,
        has_low_throttle=True, vertical_movement=True, close_to_ground_or_skipped_check=True,
        at_rest=True)
o1 = dict(o0, vehicle_land_detected_updated=False)
o2 = ld(updated=True, timestamp=2005000, has_low_throttle=True, vertical_movement=True,
        close_to_ground_or_skipped_check=True)
write('px4_land', __doc__, {}, [inp(2000000), inp(2002500), inp(2005000, armed=True)], [o0, o1, o2],
      os.path.join(HERE, 'hand-checked-case.json'))
