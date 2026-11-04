import AP_Math.vector3

/-!
# `AP_Math/matrix3.h` and `matrix3.cpp`, the part `Quaternion.earth_to_body` needs

`Matrix3f` is `Matrix3<float>`, rows `a`, `b`, `c`. Mirrors, at ArduPilot 802db19de1,
`matrix3.h:50-72` (rows, constructors) and `matrix3.cpp:145-151` (`operator*(const Vector3<T>&)`),
and (PORT FIX, added with the Copter loop) `matrix3.cpp:49-60` (`to_euler`).

Left out: everything else in `Matrix3` (rotation, Euler conversions, transpose, inverse,
`mul_transpose`, normalization); the cascade does not use `Matrix3`.
-/

/-- `Matrix3<float>`; the default is the zero matrix. -/
structure Matrix3f where
  a : Vector3f := {}
  b : Vector3f := {}
  c : Vector3f := {}
deriving Repr, Inhabited

namespace Matrix3f

/-- `operator*(const Vector3<T> &v)`: row-by-vector dot products, as written in `matrix3.cpp`. -/
def mul_vec (m : Matrix3f) (v : Vector3f) : Vector3f :=
  ⟨m.a.x * v.x + m.a.y * v.y + m.a.z * v.z,
   m.b.x * v.x + m.b.y * v.y + m.b.z * v.z,
   m.c.x * v.x + m.c.y * v.y + m.c.z * v.z⟩

instance : HMul Matrix3f Vector3f Vector3f := ⟨mul_vec⟩

-- PORT FIX: added for the Copter loop, which derives the AHRS view's Euler angles from the
-- body-to-NED rotation matrix (`AP_AHRS_View::update`, `AP_AHRS_View.cpp:65`).
/-- `to_euler(T *roll, T *pitch, T *yaw)` (`matrix3.cpp:49-60`); returns `(roll, pitch, yaw)`.
`atan2F` on `float` arguments is `atan2f` (see `quaternion.lean`). -/
def to_euler (m : Matrix3f) : Float32 × Float32 × Float32 :=
  let pitch := -AP_Math.safe_asin m.c.x
  let roll := Float32.atan2 m.c.y m.c.z
  let yaw := Float32.atan2 m.b.x m.a.x
  (roll, pitch, yaw)

end Matrix3f
