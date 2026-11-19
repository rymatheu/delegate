#!/usr/bin/env python3
"""A hand check of one path through px4_sensors: a gyro sample through calibration to
vehicle_angular_velocity (the input records px4/modules/px4_sensors/gyro-check-input.json, 6 ticks at 400 Hz).

Set-up: the SITL gyro and accel (device 1310988), CAL_GYRO0_ID = 1310988 with offsets
(0.01, -0.02, 0.005) rad/s, identity rotations (CAL_GYRO0_ROT = 0, SENS_BOARD_ROT = 0, board offsets
0), the gyro low-pass and derivative filters off (IMU_GYRO_CUTOFF = IMU_DGYRO_CUTOFF = 0; notch
filters off by default). Every tick a gyro sample (0.1, 0.2, -0.3) rad/s and an accel sample.

Expected, from the code: sensor_calibration::Gyroscope::Correct returns rotation * (data - offset)
(Gyroscope.hpp), so each axis is the binary32 subtraction f32(raw) - f32(offset); with the filters
off VehicleAngularVelocity publishes that value unfiltered, stamped with the sample time, and the
derivative 0 (filter off). It starts publishing at the fourth tick, once the gyro is selected
(sensor_selection, from the voted vehicle_imu) and its sample rate is estimated; this script checks
ticks 3-5 bit for bit and that nothing is published before.

Only these output fields are checked (the module has 108); `harness replay` compares whole records,
so this is a script around `py/replay_csv.py` rather than a replayable expected record. Its input file is
therefore not named like the hand-checked replay cases (`*hand-checked-case*.json`, which `harness replay`
checks record for record): its output records are not expected values; this script reads only its columns."""
import csv, os, struct, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
H = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
def f32(x): return struct.unpack('<f', struct.pack('<f', x))[0]
out = os.path.join(H, 'build', 'hand_check_gyro.csv')
subprocess.run([sys.executable, '-I', '-B', os.path.join(H, 'py/replay_csv.py'),
                os.path.join(HERE, 'gyro-check-input.json'), out, '--cols', 'vehicle_angular_velocity_'],
               check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
rows = list(csv.DictReader(open(out)))
exp = [f32(f32(0.1) - f32(0.01)), f32(f32(0.2) - f32(-0.02)), f32(f32(-0.3) - f32(0.005))]
ok = True
for k, r in enumerate(rows):
    pub = r['vehicle_angular_velocity_updated'] == 'true'
    if k < 3:
        ok &= not pub
        continue
    got = [f32(float(r[f'vehicle_angular_velocity_xyz_{i}'])) for i in range(3)]
    t = 1000000 + 2500 * k
    ok &= pub and got == exp and int(r['vehicle_angular_velocity_timestamp_sample']) == t and \
        all(float(r[f'vehicle_angular_velocity_xyz_derivative_{i}']) == 0 for i in range(3))
    print(k, got, exp)
print('hand check', 'PASSED' if ok else 'FAILED')
sys.exit(0 if ok else 1)
