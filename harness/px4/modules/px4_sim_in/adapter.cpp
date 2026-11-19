// adapter.cpp: px4_sim_in, plant_sim's sensor samples as PX4's raw sensor topics (see Module.lean).
// Not PX4 code: the conversions a PX4 simulator driver makes, written out.
#include "module_protocol.h"

#include <math.h>

void module_init(const Params &) {}

// a float64 PX4 field as the generator carries it: the value rounded to binary32, and the rest
static void split(double x, float &hi, float &lo)
{
	hi = (float)x;
	lo = (float)(x - (double)hi);
}

void module_step(const Input &in, Output &out)
{
	const uint32_t t = in.t_us;
	// IMU: the newest sample of the tick (after the third 1200 Hz substep)
	out.sensor_accel_count = 1;              // one message in the topic's single slot
	out.sensor_accel_timestamp = t;
	out.sensor_accel_timestamp_sample = t;
	out.sensor_accel_device_id = 1310988;
	out.sensor_accel_x = in.imu2_ax;
	out.sensor_accel_y = in.imu2_ay;
	out.sensor_accel_z = in.imu2_az;
	out.sensor_accel_temperature = NAN;
	out.sensor_accel_samples = 1;
	out.sensor_gyro_count = 1;              // one message in the topic's single slot
	out.sensor_gyro_timestamp = t;
	out.sensor_gyro_timestamp_sample = t;
	out.sensor_gyro_device_id = 1310988;
	out.sensor_gyro_x = in.imu2_gx;
	out.sensor_gyro_y = in.imu2_gy;
	out.sensor_gyro_z = in.imu2_gz;
	out.sensor_gyro_temperature = NAN;
	out.sensor_gyro_samples = 1;

	if (in.baro_fresh) {
		out.sensor_baro_count = 1;
		out.sensor_baro_timestamp = t;
		out.sensor_baro_timestamp_sample = t;
		out.sensor_baro_device_id = 6620172;
		out.sensor_baro_pressure = in.baro_pa;
		out.sensor_baro_temperature = in.baro_degc;
	}

	if (in.mag_fresh) {
		out.sensor_mag_count = 1;
		out.sensor_mag_timestamp = t;
		out.sensor_mag_timestamp_sample = t;
		out.sensor_mag_device_id = 197388;
		out.sensor_mag_x = in.mag_x / 1000.f;    // mGauss -> Gauss
		out.sensor_mag_y = in.mag_y / 1000.f;
		out.sensor_mag_z = in.mag_z / 1000.f;
		out.sensor_mag_temperature = NAN;
	}

	if (in.gps_fresh) {
		out.sensor_gps_updated = true;
		out.sensor_gps_timestamp = t;
		out.sensor_gps_timestamp_sample = t;
		split(in.gps_lat_e7 * 1e-7, out.sensor_gps_latitude_deg, out.sensor_gps_latitude_deg_lo);
		split(in.gps_lon_e7 * 1e-7, out.sensor_gps_longitude_deg, out.sensor_gps_longitude_deg_lo);
		split((double)in.gps_alt, out.sensor_gps_altitude_msl_m, out.sensor_gps_altitude_msl_m_lo);
		split((double)in.gps_alt, out.sensor_gps_altitude_ellipsoid_m, out.sensor_gps_altitude_ellipsoid_m_lo);
		out.sensor_gps_fix_type = 3;
		out.sensor_gps_satellites_used = 10;
		out.sensor_gps_eph = 0.5f;
		out.sensor_gps_epv = 0.8f;
		out.sensor_gps_hdop = 0.7f;
		out.sensor_gps_vdop = 1.1f;
		out.sensor_gps_s_variance_m_s = 0.25f;
		out.sensor_gps_vel_n_m_s = in.gps_vn;
		out.sensor_gps_vel_e_m_s = in.gps_ve;
		out.sensor_gps_vel_d_m_s = in.gps_vd;
		out.sensor_gps_vel_m_s = sqrtf(in.gps_vn * in.gps_vn + in.gps_ve * in.gps_ve);
		out.sensor_gps_cog_rad = atan2f(in.gps_ve, in.gps_vn);
		out.sensor_gps_vel_ned_valid = true;
		out.sensor_gps_heading = NAN;
		out.sensor_gps_heading_offset = NAN;
		out.sensor_gps_heading_accuracy = NAN;
	}
}
