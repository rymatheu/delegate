#!/usr/bin/env python3
"""Writes hand-checked-case.json for px4_sim_in: two ticks worked out from adapter.cpp.
Tick 0 (t = 2500 us): IMU only: gyro (0.25, -0.5, 0.125) rad/s and specific force (0.5, -0.25, -9.75)
  m/s² copied to sensor_gyro / sensor_accel, device 1310988, one sample, temperature NaN, stamped
  2500; no baro, compass or GPS message.
Tick 1 (t = 5000 us): the same IMU, a baro sample (59000 Pa, -12.5 °C), a compass sample
  (250, -125, 500) mGauss = (0.25, -0.125, 0.5) Gauss, and a GPS fix at latitude 473977420e-7 deg,
  longitude 85455940e-7 deg, 4321.5 m, velocity (3, 4, -0.5) m/s: the degrees are carried as the
  binary32 value plus the binary32 rest (hi + lo = the binary64 degrees to 1e-12), ground speed 5,
  course atan2(4, 3), 3D fix, 10 satellites, eph 0.5, epv 0.8, hdop 0.7, vdop 1.1, speed variance 0.25,
  heading fields NaN."""
import json, math, os, re, struct
HERE = os.path.dirname(os.path.abspath(__file__))
HARNESS = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
def f32(x): return struct.unpack('<f', struct.pack('<f', x))[0]
def hx(x): return '0x%08x' % struct.unpack('<I', struct.pack('<f', x))[0]
NAN = '0x7fc00000'
txt = open(os.path.join(HARNESS, 'px4/modules/px4_sensors/Ports.lean')).read()
block = txt.split('def input : Schema := #[')[1].split(']\n')[0]
fields = [(n, t) for n, t in re.findall(r'name := "([^"]+)", type := \.(\w+)', block)
          if any(n.startswith(p) for p in ('sensor_accel_', 'sensor_gyro_', 'sensor_baro_', 'sensor_mag_', 'sensor_gps_'))]
def word(t, v):
    if isinstance(v, str): return v
    if t == 'f32': return hx(v)
    if t == 'bool': return 'true' if v else 'false'
    return str(int(v))
def split(x):
    hi = f32(x); return hi, f32(x - hi)
plant_fields = ['t_us', 'imu2_ax', 'imu2_ay', 'imu2_az', 'imu2_gx', 'imu2_gy', 'imu2_gz', 'baro_fresh', 'baro_pa',
                'baro_degc', 'mag_fresh', 'mag_x', 'mag_y', 'mag_z', 'gps_fresh', 'gps_lat_e7', 'gps_lon_e7',
                'gps_alt', 'gps_vn', 'gps_ve', 'gps_vd']
ptypes = {'t_us': 'u32', 'baro_fresh': 'bool', 'mag_fresh': 'bool', 'gps_fresh': 'bool', 'gps_lat_e7': 'i32', 'gps_lon_e7': 'i32'}
inputs, outputs = [], []
for k, t in enumerate([2500, 5000]):
    slow = k == 1
    p = dict(t_us=t, imu2_ax=0.5, imu2_ay=-0.25, imu2_az=-9.75, imu2_gx=0.25, imu2_gy=-0.5, imu2_gz=0.125,
             baro_fresh=slow, baro_pa=59000.0 if slow else 0.0, baro_degc=-12.5 if slow else 0.0,
             mag_fresh=slow, mag_x=250.0 if slow else 0.0, mag_y=-125.0 if slow else 0.0, mag_z=500.0 if slow else 0.0,
             gps_fresh=slow, gps_lat_e7=473977420 if slow else 0, gps_lon_e7=85455940 if slow else 0,
             gps_alt=4321.5 if slow else 0.0, gps_vn=3.0 if slow else 0.0, gps_ve=4.0 if slow else 0.0, gps_vd=-0.5 if slow else 0.0)
    inputs.append({n: word(ptypes.get(n, 'f32'), p[n]) for n in plant_fields})
    o = {n: (0.0 if ty == 'f32' else (False if ty == 'bool' else 0)) for n, ty in fields}
    for s in ('accel', 'gyro'):
        o.update({f'sensor_{s}_count': 1, f'sensor_{s}_timestamp': t, f'sensor_{s}_timestamp_sample': t,
                  f'sensor_{s}_device_id': 1310988, f'sensor_{s}_temperature': NAN, f'sensor_{s}_samples': 1})
    o.update(sensor_accel_x=0.5, sensor_accel_y=-0.25, sensor_accel_z=-9.75, sensor_gyro_x=0.25, sensor_gyro_y=-0.5, sensor_gyro_z=0.125)
    if slow:
        o.update(sensor_baro_count=1, sensor_baro_timestamp=t, sensor_baro_timestamp_sample=t, sensor_baro_device_id=6620172,
                 sensor_baro_pressure=59000.0, sensor_baro_temperature=-12.5,
                 sensor_mag_count=1, sensor_mag_timestamp=t, sensor_mag_timestamp_sample=t, sensor_mag_device_id=197388,
                 sensor_mag_x=f32(250.0 / 1000.0), sensor_mag_y=f32(-125.0 / 1000.0), sensor_mag_z=f32(500.0 / 1000.0),
                 sensor_mag_temperature=NAN)
        lat, lon = 473977420 * 1e-7, 85455940 * 1e-7
        la, lalo = split(lat); lo_, lolo = split(lon); al, allo = split(4321.5)
        o.update(sensor_gps_updated=True, sensor_gps_timestamp=t, sensor_gps_timestamp_sample=t,
                 sensor_gps_latitude_deg=la, sensor_gps_latitude_deg_lo=lalo, sensor_gps_longitude_deg=lo_,
                 sensor_gps_longitude_deg_lo=lolo, sensor_gps_altitude_msl_m=al, sensor_gps_altitude_msl_m_lo=allo,
                 sensor_gps_altitude_ellipsoid_m=al, sensor_gps_altitude_ellipsoid_m_lo=allo, sensor_gps_fix_type=3,
                 sensor_gps_satellites_used=10, sensor_gps_eph=0.5, sensor_gps_epv=0.8, sensor_gps_hdop=0.7,
                 sensor_gps_vdop=1.1, sensor_gps_s_variance_m_s=0.25, sensor_gps_vel_n_m_s=3.0, sensor_gps_vel_e_m_s=4.0,
                 sensor_gps_vel_d_m_s=-0.5, sensor_gps_vel_m_s=5.0, sensor_gps_cog_rad=f32(math.atan2(4.0, 3.0)),
                 sensor_gps_vel_ned_valid=True, sensor_gps_heading=NAN, sensor_gps_heading_offset=NAN,
                 sensor_gps_heading_accuracy=NAN)
    outputs.append({n: word(ty, o[n]) for n, ty in fields})
json.dump({"module": "px4_sim_in", "code_hash": "(computed by hand)", "campaign": "none", "kind": "hand-checked",
           "clause": "", "case": 0, "step": 1, "note": __doc__.replace('\n', ' '), "params": {},
           "inputs": inputs, "outputs": outputs}, open(os.path.join(HERE, 'hand-checked-case.json'), 'w'), indent=2)
