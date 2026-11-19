// stubs_frames.cpp: terrain, Location and the EKF origin, which the guidance module does not
// reach: destinations come as NED meters from the EKF origin (the supervisor converts a Location
// with the origin it holds), and terrain is out of scope (every is_terrain_alt argument is false).
//
//   symbol                                   reached from (AC_WPNav.cpp), and why not reached
//   AP::terrain(), AP_Terrain::height_above_terrain
//                                            get_terrain_source / get_terrain_U_m (184-815): only
//                                            from the terrain branches (advance_wp_target_along_track
//                                            when _is_terrain_alt, convert_origin_to_alt_frame,
//                                            set_spline_destination_NED_m on a frame change).
//                                            _is_terrain_alt stays false. Abort.
//   Location::get_vector_xy_from_origin_NE_m, ::get_alt_m, ::get_alt_frame
//                                            get_vector_NED_m (1036), from the _loc setters, which
//                                            the module does not call. Abort.
//   Location::from_ekf_offset_NED_m, AP::ahrs(), AP_AHRS::get_origin
//                                            get_wp_destination_loc (358), reached only through the
//                                            vtable entry get_oa_wp_destination; not called. Abort.
#include <stdio.h>
#include <stdlib.h>

#include <AP_Common/Location.h>
#include <AP_Terrain/AP_Terrain.h>
#include <AP_AHRS/AP_AHRS.h>

__attribute__((noreturn)) static void frames_unreachable(const char *what)
{
    fprintf(stderr, "guidance: cut symbol reached: %s\n", what);
    abort();
}

namespace AP {
AP_Terrain *terrain()
{
    frames_unreachable("AP::terrain");
}

AP_AHRS &ahrs()
{
    frames_unreachable("AP::ahrs");
}
}

bool AP_Terrain::height_above_terrain(float &terrain_altitude, bool extrapolate)
{
    frames_unreachable("AP_Terrain::height_above_terrain");
}

bool AP_AHRS::get_origin(Location &ret) const
{
    frames_unreachable("AP_AHRS::get_origin");
}

Location Location::from_ekf_offset_NED_m(const Vector3d &ekf_offset_ned_m, AltFrame frame)
{
    frames_unreachable("Location::from_ekf_offset_NED_m");
}

Location::AltFrame Location::get_alt_frame() const
{
    frames_unreachable("Location::get_alt_frame");
}

bool Location::get_alt_m(AltFrame desired_frame, float &ret_alt) const
{
    frames_unreachable("Location::get_alt_m");
}

template <typename T>
bool Location::get_vector_xy_from_origin_NE_m(T &vec_ne) const
{
    frames_unreachable("Location::get_vector_xy_from_origin_NE_m");
}
template bool Location::get_vector_xy_from_origin_NE_m<Vector2p>(Vector2p &vec_ne) const;
