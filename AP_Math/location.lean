import AP_Math.vector2

/-!
# `AP_Math/location.h` and `location.cpp`, the two planar helpers `AC_WPNav` calls

PORT FIX: added with the `AC_WPNav` port, which calls them in `get_wp_distance_to_destination_m`
and `get_wp_bearing_to_destination_rad` (`AC_WPNav.cpp:676-697`).

Mirrors, at ArduPilot 802db19de1, `location.h:14-18` (`get_horizontal_distance`, the
`Vector2<float>` instance) and `location.cpp:27-36` (`get_bearing_rad`, `get_bearing_cd`).

Left out: the WGS84/ECEF conversions and the rest of `location.cpp`; `Location` itself
(`AP_Common/Location.cpp`) is not ported.
-/

namespace AP_Math

/-- `get_horizontal_distance<float>(origin, destination)` (`location.h:14-18`):
`(destination - origin).length()`. -/
def get_horizontal_distance (origin destination : Vector2f) : Float32 :=
  (destination - origin).length

/-- `get_bearing_rad(origin, destination)` (`location.cpp:27-30`):
`wrap_2PI(atan2f(destination.y - origin.y, destination.x - origin.x))`, clockwise from north. -/
def get_bearing_rad (origin destination : Vector2f) : Float32 :=
  wrap_2PI (Float32.atan2 (destination.y - origin.y) (destination.x - origin.x))

/-- `get_bearing_cd(origin, destination)` (`location.cpp:33-36`). -/
def get_bearing_cd (origin destination : Vector2f) : Float32 :=
  rad_to_cd (get_bearing_rad origin destination)

end AP_Math
