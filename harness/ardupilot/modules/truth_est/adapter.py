"""truth_est adapter: the plant's true state under the estimator's signal names (test fixture).
Reads its schemas from build/gen/truth_est/module_schema.json (harness gen truth_est)."""
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
HARNESS = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
sys.path.insert(0, os.path.join(HARNESS, 'py'))
import module_protocol as mp  # noqa: E402

SCHEMA = mp.load_schema(os.path.join(HARNESS, 'build', 'gen', 'truth_est', 'module_schema.json'))
P = {}


def init(params):
    P.clear()
    P.update(params)
    P['_density'] = 1.0


def step(i):
    if i['baro_fresh'] and i['baro_pa'] > 0:
        # rho / SSL_AIR_DENSITY, rho = p / (ISA_GAS_CONSTANT T) (AP_Math/definitions.h)
        P['_density'] = i['baro_pa'] / (287.26 * (i['baro_degc'] + 273.15)) / 1.225
    q1, q2, q3, q4 = i['q1'], i['q2'], i['q3'], i['q4']
    # ArduPilot QuaternionT::to_euler (roll, pitch, yaw)
    roll = math.atan2(2 * (q1 * q2 + q3 * q4), 1 - 2 * (q2 * q2 + q3 * q3))
    pitch = math.asin(max(-1.0, min(1.0, 2 * (q1 * q3 - q4 * q2))))
    yaw = math.atan2(2 * (q1 * q4 + q2 * q3), 1 - 2 * (q3 * q3 + q4 * q4))
    # rotation body -> NED
    r = [[1 - 2 * (q3 * q3 + q4 * q4), 2 * (q2 * q3 - q1 * q4), 2 * (q2 * q4 + q1 * q3)],
         [2 * (q2 * q3 + q1 * q4), 1 - 2 * (q2 * q2 + q4 * q4), 2 * (q3 * q4 - q1 * q2)],
         [2 * (q2 * q4 - q1 * q3), 2 * (q3 * q4 + q1 * q2), 1 - 2 * (q2 * q2 + q3 * q3)]]
    a = (i['imu2_ax'], i['imu2_ay'], i['imu2_az'])
    aef = [sum(r[k][j] * a[j] for j in range(3)) for k in range(3)]
    o = {f['name']: (False if f['type'] == 'bool' else 0) for f in SCHEMA['output']}
    o.update(est_accel_x=i['imu2_ax'], est_accel_y=i['imu2_ay'], est_accel_z=i['imu2_az'],
             est_gyro_x=i['imu2_gx'], est_gyro_y=i['imu2_gy'], est_gyro_z=i['imu2_gz'],
             gyro_x=i['imu2_gx'], gyro_y=i['imu2_gy'], gyro_z=i['imu2_gz'],
             est_q1=q1, est_q2=q2, est_q3=q3, est_q4=q4, est_roll=roll, est_pitch=pitch,
             est_yaw=yaw, est_sin_yaw=math.sin(yaw), est_cos_yaw=math.cos(yaw),
             est_pos_ok=True,
             est_pos_n=i['pos_n'], est_pos_e=i['pos_e'], est_pos_d=i['pos_d'],
             est_vel_ok=True, est_vel_n=i['vel_n'], est_vel_e=i['vel_e'],
             est_vel_d=i['vel_d'], est_pos_rate_d_ok=True,
             est_pos_rate_d=i['vel_d'],
             est_accel_ef_x=aef[0], est_accel_ef_y=aef[1], est_accel_ef_z=aef[2],
             est_gain_scaler_xy=1.0, est_gain_scaler_z=1.0, est_origin_ok=True,
             est_origin_lat_e7=P['origin_lat_e7'], est_origin_lon_e7=P['origin_lon_e7'],
             est_origin_alt_cm=P['origin_alt_cm'], est_healthy=True, est_initialised=True,
             est_filter_status=0x1A33F, est_variances_ok=True, est_baro_alt=-i['pos_d'],
             est_gps_status=3, est_gps_num_sats=10, air_density_ratio=P['_density'],
             est_prearm_ok=True, est_ins_accel_healthy=True, est_ins_gyro_healthy=True,
             est_baro_healthy=True, est_gps_healthy=True, est_gps_hdop=100, est_gps_vdop=100,
             est_innov_ok=True)
    return o


def main():
    out = mp.take_stdout()
    manifest = mp.manifest_json(SCHEMA, os.environ.get('TRUTH_EST_HASH', 'see code_inputs.txt'),
                                'python3 -I adapter.py', sys.version.split()[0])
    sys.exit(mp.serve(SCHEMA, manifest, init, step, out))


main()
