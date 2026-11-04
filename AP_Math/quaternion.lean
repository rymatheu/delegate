import AP_Math.matrix3

/-!
# `AP_Math/quaternion.h` and `quaternion.cpp`, `Quaternion` = `QuaternionT<float>`

Mirrors, at ArduPilot 802db19de1, `quaternion.h:28-57` (fields, constructors, `is_nan`),
`:153-157` (`initialise`), and in `quaternion.cpp`: `:58-80` (`rotation_matrix(Matrix3f&)`),
`:411-417` (`earth_to_body`), `:420-439` (`from_euler`), `:453-483` (`from_axis_angle`, both forms),
`:486-492` (`rotate(const Vector3&)`), `:496-505` (`to_axis_angle`), `:586-621`
(`get_euler_roll/pitch/yaw`, `to_euler`), `:632-659` (`length`, `length_squared`, `inverse`,
`invert`), `:661-689` (`normalize`, `is_zero`, `zero`), `:694-709` (`is_unit_length`),
`:711-731` (`operator*` Hamilton product), `:737-759` (`operator*(const Vector3&)`),
`:761-780` (`operator*=`).

Precision. The review (`ardupilot-review.md` section 1) and the task brief assume that the
`sinF`/`cosF`/`atan2F`/`sqrtF` macros call the `double` libm here when `HAL_WITH_EKF_DOUBLE`. They do
not. The macros expand to `sin(x)` etc. (`ftype.h:16-23`); with `-fsingle-precision-constant` the
argument is `float` (`0.5*theta` is `0.5f*theta`), and `<math.h>` in C++ (libstdc++ and libc++)
puts the `float` overloads `std::sin(float)` etc. into the global namespace, so overload
resolution picks `sinf`, `cosf`, `atan2f`, `sqrtf`. Checked by compiling
`float f(float t){ return sin(0.5*t); }` after `#include <cmath>` and `<math.h>`: g++ 15 with
`-fsingle-precision-constant` and Apple clang 17 with `-cl-single-precision-constant` both emit a
call to `sinf` (and `atan2f`, `fsqrt` for the other two). Without the flag, clang emits
`fcvt; bl sin; fcvt`. So every quaternion operation here is binary32, libm included.

Conventions. Mutating methods (`normalize`, `invert`, `rotate`, `zero`, `initialise`) return the
new quaternion. Methods that overwrite every field regardless of `*this` (`from_euler`,
`from_axis_angle`) are functions of their arguments only. Overloads: `from_axis_angle(Vector3)`
is `from_axis_angle`, `from_axis_angle(axis, theta)` is `from_axis_angle_theta`;
`from_euler(const Vector3&)` is `from_euler_vec`; `to_euler(float&, float&, float&)` returns a
triple and `to_euler(Vector3f&)` is `to_euler_vec`. `operator*=` computes the same expressions
as `operator*`, so it is `mul`.

Left out: `rotation_matrix(Matrix3d&)`, `from_rotation_matrix`, `from_rotation`,
`rotate(enum Rotation)`, `from_vector312`, `to_vector312`, `from_axis_angle_fast` (both),
`from_angular_velocity`, `rotate_fast`, `to_euler(double&...)`, `operator/`,
`angular_difference`, `roll_pitch_difference`, `operator[]`, `todouble`/`tofloat`, and
`QuaternionT<double>`. None is called by the cascade.
-/

/-- `QuaternionT<float>`; the default constructor gives the identity `(1, 0, 0, 0)`. -/
structure Quaternion where
  q1 : Float32 := 1
  q2 : Float32 := 0
  q3 : Float32 := 0
  q4 : Float32 := 0
deriving Repr, Inhabited

namespace Quaternion

open AP_Math (sq wrap_PI safe_asin)

/-- `is_nan()`. -/
def is_nan (q : Quaternion) : Bool := q.q1.isNaN || q.q2.isNaN || q.q3.isNaN || q.q4.isNaN

/-- `initialise()`: `q1 = 1.0f; q2 = q3 = q4 = 0.0f`. -/
def initialise (_q : Quaternion) : Quaternion := ⟨1.0, 0.0, 0.0, 0.0⟩

/-- `rotation_matrix(Matrix3f &m)`. -/
def rotation_matrix (q : Quaternion) : Matrix3f :=
  let q3q3 := q.q3 * q.q3
  let q3q4 := q.q3 * q.q4
  let q2q2 := q.q2 * q.q2
  let q2q3 := q.q2 * q.q3
  let q2q4 := q.q2 * q.q4
  let q1q2 := q.q1 * q.q2
  let q1q3 := q.q1 * q.q3
  let q1q4 := q.q1 * q.q4
  let q4q4 := q.q4 * q.q4
  { a := ⟨1.0 - 2.0 * (q3q3 + q4q4), 2.0 * (q2q3 - q1q4), 2.0 * (q2q4 + q1q3)⟩
    b := ⟨2.0 * (q2q3 + q1q4), 1.0 - 2.0 * (q2q2 + q4q4), 2.0 * (q3q4 - q1q2)⟩
    c := ⟨2.0 * (q2q4 - q1q3), 2.0 * (q3q4 + q1q2), 1.0 - 2.0 * (q2q2 + q3q3)⟩ }

/-- `earth_to_body(Vector3 &v)`: `v = m * v` with `m = rotation_matrix()`. -/
def earth_to_body (q : Quaternion) (v : Vector3f) : Vector3f := q.rotation_matrix * v

/-- `from_euler(roll, pitch, yaw)`, 321 order; `cosF(roll*0.5)` is `cosf(roll*0.5f)`. -/
def from_euler (roll pitch yaw : Float32) : Quaternion :=
  let cr2 := (roll * 0.5).cos
  let cp2 := (pitch * 0.5).cos
  let cy2 := (yaw * 0.5).cos
  let sr2 := (roll * 0.5).sin
  let sp2 := (pitch * 0.5).sin
  let sy2 := (yaw * 0.5).sin
  ⟨cr2 * cp2 * cy2 + sr2 * sp2 * sy2,
   sr2 * cp2 * cy2 - cr2 * sp2 * sy2,
   cr2 * sp2 * cy2 + sr2 * cp2 * sy2,
   cr2 * cp2 * sy2 - sr2 * sp2 * cy2⟩

/-- `from_euler(const Vector3<T> &v)`. -/
def from_euler_vec (v : Vector3f) : Quaternion := from_euler v.x v.y v.z

/-- `from_axis_angle(const Vector3<T> &axis, T theta)`; `axis` must be a unit vector. -/
def from_axis_angle_theta (axis : Vector3f) (theta : Float32) : Quaternion :=
  if AP_Math.is_zero theta then ⟨1.0, 0.0, 0.0, 0.0⟩
  else
    let st2 := (0.5 * theta).sin
    ⟨(0.5 * theta).cos, axis.x * st2, axis.y * st2, axis.z * st2⟩

/-- `from_axis_angle(Vector3<T> v)`, rotation-vector form. -/
def from_axis_angle (v : Vector3f) : Quaternion :=
  let theta := v.length
  if AP_Math.is_zero theta then ⟨1.0, 0.0, 0.0, 0.0⟩
  else from_axis_angle_theta (v / theta) theta

/-- `to_axis_angle(Vector3<T> &v)`: the rotation vector. -/
def to_axis_angle (q : Quaternion) : Vector3f :=
  let l := (sq q.q2 + sq q.q3 + sq q.q4).sqrt
  let v : Vector3f := ⟨q.q2, q.q3, q.q4⟩
  if !AP_Math.is_zero l then
    let v := v / l
    v * wrap_PI (2.0 * Float32.atan2 l q.q1)
  else v

/-- `get_euler_roll()`. -/
def get_euler_roll (q : Quaternion) : Float32 :=
  Float32.atan2 (2.0 * (q.q1 * q.q2 + q.q3 * q.q4)) (1.0 - 2.0 * (q.q2 * q.q2 + q.q3 * q.q3))

/-- `get_euler_pitch()`: `safe_asin(2.0f*(q1*q3 - q4*q2))`. -/
def get_euler_pitch (q : Quaternion) : Float32 :=
  safe_asin (2.0 * (q.q1 * q.q3 - q.q4 * q.q2))

/-- `get_euler_yaw()`. -/
def get_euler_yaw (q : Quaternion) : Float32 :=
  Float32.atan2 (2.0 * (q.q1 * q.q4 + q.q2 * q.q3)) (1.0 - 2.0 * (q.q3 * q.q3 + q.q4 * q.q4))

/-- `to_euler(float &roll, float &pitch, float &yaw)`. -/
def to_euler (q : Quaternion) : Float32 × Float32 × Float32 :=
  (q.get_euler_roll, q.get_euler_pitch, q.get_euler_yaw)

/-- `to_euler(Vector3f &rpy)`. -/
def to_euler_vec (q : Quaternion) : Vector3f :=
  ⟨q.get_euler_roll, q.get_euler_pitch, q.get_euler_yaw⟩

/-- `length()`: `sqrtF(sq(q1) + sq(q2) + sq(q3) + sq(q4))`, i.e. `sqrtf`. -/
def length (q : Quaternion) : Float32 := (sq q.q1 + sq q.q2 + sq q.q3 + sq q.q4).sqrt

/-- `length_squared()`. -/
def length_squared (q : Quaternion) : Float32 :=
  q.q1 * q.q1 + q.q2 * q.q2 + q.q3 * q.q3 + q.q4 * q.q4

/-- `inverse()`: the conjugate. -/
def inverse (q : Quaternion) : Quaternion := ⟨q.q1, -q.q2, -q.q3, -q.q4⟩

/-- `invert()`. -/
def invert (q : Quaternion) : Quaternion := ⟨q.q1, -q.q2, -q.q3, -q.q4⟩

/-- `normalize()`: unchanged when `is_zero(length())` (the C++ also raises `INTERNAL_ERROR`). -/
def normalize (q : Quaternion) : Quaternion :=
  let quatMag := q.length
  if !AP_Math.is_zero quatMag then
    let quatMagInv := 1.0 / quatMag
    ⟨q.q1 * quatMagInv, q.q2 * quatMagInv, q.q3 * quatMagInv, q.q4 * quatMagInv⟩
  else q

/-- `is_zero()`. -/
def is_zero (q : Quaternion) : Bool :=
  AP_Math.is_zero q.q1 && AP_Math.is_zero q.q2 && AP_Math.is_zero q.q3 && AP_Math.is_zero q.q4

/-- `zero()`. -/
def zero (_q : Quaternion) : Quaternion := ⟨0.0, 0.0, 0.0, 0.0⟩

/-- `is_unit_length()`: `fabsF(length_squared() - 1) < 1E-3`, all `float`. -/
def is_unit_length (q : Quaternion) : Bool := (q.length_squared - 1).abs < 1E-3

/-- Hamilton product `operator*(const QuaternionT<T> &v)`, also `operator*=`. -/
def mul (q v : Quaternion) : Quaternion :=
  let w1 := q.q1
  let x1 := q.q2
  let y1 := q.q3
  let z1 := q.q4
  let w2 := v.q1
  let x2 := v.q2
  let y2 := v.q3
  let z2 := v.q4
  ⟨w1 * w2 - x1 * x2 - y1 * y2 - z1 * z2,
   w1 * x2 + x1 * w2 + y1 * z2 - z1 * y2,
   w1 * y2 - x1 * z2 + y1 * w2 + z1 * x2,
   w1 * z2 + x1 * y2 - y1 * x2 + z1 * w2⟩

/-- `operator*(const Vector3<T> &v)`: rotate `v` by this quaternion
(`v + 2 q1 (qv × v) + 2 qv × (qv × v)`, as written in `quaternion.cpp:747-758`). -/
def mul_vec (q : Quaternion) (v : Vector3f) : Vector3f :=
  let uv0 := q.q3 * v.z - q.q4 * v.y
  let uv1 := q.q4 * v.x - q.q2 * v.z
  let uv2 := q.q2 * v.y - q.q3 * v.x
  let uv0 := uv0 + uv0
  let uv1 := uv1 + uv1
  let uv2 := uv2 + uv2
  ⟨v.x + (q.q1 * uv0 + q.q3 * uv2 - q.q4 * uv1),
   v.y + (q.q1 * uv1 + q.q4 * uv0 - q.q2 * uv2),
   v.z + (q.q1 * uv2 + q.q2 * uv1 - q.q3 * uv0)⟩

instance : HMul Quaternion Quaternion Quaternion := ⟨mul⟩
instance : HMul Quaternion Vector3f Vector3f := ⟨mul_vec⟩

/-- `rotate(const Vector3<T> &v)`: `*this *= r` with `r.from_axis_angle(v)`. -/
def rotate (q : Quaternion) (v : Vector3f) : Quaternion := q * from_axis_angle v

end Quaternion
