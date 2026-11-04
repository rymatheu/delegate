import AP_Math

/-!
# Spot checks for the `AP_Math` port

Evaluates each ported function on hand-picked inputs (zeros, negative zero, values below
`FLT_EPSILON`, branch points, NaN) and prints the result in decimal and as its bit pattern.
Run with `lake env lean --run AP_Math/Check.lean` after `lake build AP_Math`. Not imported by
`AP_Math.lean`.
-/

open AP_Math

namespace AP_Math.Check

def hex (width : Nat) (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  "0x" ++ String.ofList (List.replicate (width - s.length) '0') ++ s

def f (x : Float32) : String := s!"{x} [{hex 8 x.toBits.toNat}]"
def d (x : Float) : String := s!"{x} [{hex 16 x.toBits.toNat}]"
def b (x : Bool) : String := toString x
def v2 (v : Vector2f) : String := s!"({f v.x}, {f v.y})"
def v2p (v : Vector2p) : String := s!"({d v.x}, {d v.y})"
def v3 (v : Vector3f) : String := s!"({f v.x}, {f v.y}, {f v.z})"
def q (q : Quaternion) : String := s!"({f q.q1}, {f q.q2}, {f q.q3}, {f q.q4})"

def nan : Float32 := Float32.ofBits 0x7fc00000
def inf : Float32 := Float32.ofBits 0x7f800000
def nz : Float32 := Float32.ofBits 0x80000000
/-- `FLT_EPSILON / 2`, below the `is_zero` threshold. -/
def small : Float32 := Float32.ofBits 0x33800000
/-- The largest `float` below `FLT_EPSILON`. -/
def below_eps : Float32 := Float32.ofBits 0x33ffffff
def nextUp (x : Float32) : Float32 := Float32.ofBits (x.toBits + 1)
def nextDown (x : Float32) : Float32 := Float32.ofBits (x.toBits - 1)

def line (s : String) : IO Unit := IO.println s

def scalars : IO Unit := do
  line "-- constants"
  line s!"M_PI = {f M_PI}"
  line s!"M_PI_2 = {f M_PI_2}"
  line s!"M_2PI = {f M_2PI}"
  line s!"DEG_TO_RAD = {f DEG_TO_RAD}"
  line s!"RAD_TO_DEG = {f RAD_TO_DEG}"
  line s!"FLT_EPSILON = {f FLT_EPSILON}"
  line "-- is_zero / is_positive / is_negative"
  for x in [0, nz, small, below_eps, FLT_EPSILON, -FLT_EPSILON, nan] do
    line s!"x = {f x}: is_zero {b (is_zero x)}, is_positive {b (is_positive x)}, is_negative {b (is_negative x)}"
  line s!"is_zero_d 1e-8 = {b (is_zero_d 1e-8)}, is_positive_d 1e-8 = {b (is_positive_d 1e-8)}"
  line s!"is_equal 1 (1 + 2^-24) = {b (is_equal 1 (nextUp 1))}, is_equal 1 1.0001 = {b (is_equal 1 1.0001)}"
  line "-- constrain_float"
  line s!"constrain_float NaN -1 3 = {f (constrain_float nan (-1) 3)}"
  line s!"constrain_float 5 -1 3 = {f (constrain_float 5 (-1) 3)}"
  line s!"constrain_float -5 -1 3 = {f (constrain_float (-5) (-1) 3)}"
  line s!"constrain_float -0 0 1 = {f (constrain_float nz 0 1)}"
  line s!"constrain_float inf -1 3 = {f (constrain_float inf (-1) 3)}"
  line "-- safe_sqrt / safe_asin / MIN / MAX"
  line s!"safe_sqrt 4 = {f (safe_sqrt 4)}, safe_sqrt -1 = {f (safe_sqrt (-1))}, safe_sqrt NaN = {f (safe_sqrt nan)}, safe_sqrt -0 = {f (safe_sqrt nz)}"
  line s!"safe_asin 2 = {f (safe_asin 2)}, safe_asin -1 = {f (safe_asin (-1))}, safe_asin NaN = {f (safe_asin nan)}, safe_asin 0.5 = {f (safe_asin 0.5)}"
  line s!"MIN -0 0 = {f (MIN nz 0)} (Lean min: {f (min nz 0)}), MAX 0 -0 = {f (MAX 0 nz)}, MIN NaN 1 = {f (MIN nan 1)}, MIN 1 NaN = {f (MIN 1 nan)}"
  line "-- fmodf / wrap_2PI / wrap_PI"
  for (x, y) in [((7 : Float32), M_2PI), (-7, M_2PI), (nz, 1), (1e30, M_2PI), (M_2PI, M_2PI),
                 (5.5, -2), (1e-40, 3e-41), (3, inf), (inf, 1), (1, 0)] do
    line s!"fmodf {f x} {f y} = {f (fmodf x y)}"
  for x in [(0 : Float32), nz, 4, -4, M_PI, -M_PI, nextUp M_PI, -1e-9, 100, nan] do
    line s!"x = {f x}: wrap_2PI {f (wrap_2PI x)}, wrap_PI {f (wrap_PI x)}"
  line "-- radians / degrees / calc_lowpass_alpha_dt"
  line s!"radians 30 = {f (radians 30)}, degrees 1 = {f (degrees 1)}, cd_to_rad 4500 = {f (cd_to_rad 4500)}, rad_to_cd 1 = {f (rad_to_cd 1)}"
  line s!"calc_lowpass_alpha_dt 0.0025 20 = {f (calc_lowpass_alpha_dt 0.0025 20)}"
  line s!"calc_lowpass_alpha_dt 0 20 = {f (calc_lowpass_alpha_dt 0 20)}, (0.0025, 0) = {f (calc_lowpass_alpha_dt 0.0025 0)}, (-1, 20) = {f (calc_lowpass_alpha_dt (-1) 20)}"

def vectors : IO Unit := do
  line "-- Vector2f / Vector3f / Vector2p"
  let a : Vector2f := ⟨3, 4⟩
  let c : Vector2f := ⟨-1, 2⟩
  line s!"a = {v2 a}: length {f a.length}, length_squared {f a.length_squared}, normalized {v2 a.normalized}"
  line s!"a*c = {f (a * c)}, a%c = {f (a % c)}, angle a = {f a.angle}, angle_between a c = {f (a.angle_between c)}"
  line s!"limit_length a 2 = {v2 (a.limit_length 2).1} {b (a.limit_length 2).2}; limit_length a 10 = {b (a.limit_length 10).2}"
  line s!"is_zero (small, -small) = {b (Vector2f.is_zero ⟨small, -small⟩)}, is_zero (small, eps) = {b (Vector2f.is_zero ⟨small, FLT_EPSILON⟩)}, is_nan (0, NaN) = {b (Vector2f.is_nan ⟨0, nan⟩)}"
  line s!"normalized 0 = {v2 (Vector2f.normalized {})}"
  let u : Vector3f := ⟨1, 2, 2⟩
  let w : Vector3f := ⟨0, 0, -1⟩
  line s!"u = {v3 u}: length {f u.length}, u*w {f (u * w)}, u%w {v3 (u % w)}, angle_between {f (u.angle_between w)}"
  line s!"limit_length_xy u 1 = {v3 (u.limit_length_xy 1).1}"
  let p : Vector2p := ⟨1e7 + 0.25, -3⟩
  let p0 : Vector2p := ⟨1e7, 1⟩
  line s!"(p - p0).tofloat = {v2 (p - p0).tofloat}, p.length = {d p.length}"
  line s!"Vector3p length (1e8, 1, 1) = {d (Vector3p.length ⟨1e8, 1, 1⟩)}"

def quats : IO Unit := do
  line "-- Quaternion"
  let id : Quaternion := {}
  line s!"from_axis_angle 0 = {q (Quaternion.from_axis_angle {})}"
  line s!"from_axis_angle (small,0,0) = {q (Quaternion.from_axis_angle ⟨small, 0, 0⟩)}"
  line s!"from_axis_angle_theta (1,0,0) -0 = {q (Quaternion.from_axis_angle_theta ⟨1, 0, 0⟩ nz)}"
  let r := Quaternion.from_axis_angle ⟨0.1, 0.2, 0.3⟩
  line s!"r = from_axis_angle (0.1,0.2,0.3) = {q r}"
  line s!"r.to_axis_angle = {v3 r.to_axis_angle}"
  line s!"id.to_axis_angle = {v3 id.to_axis_angle}, (id*id) = {q (id * id)}"
  line s!"r * r.inverse = {q (r * r.inverse)}"
  line s!"r * (1,0,0) = {v3 (r * (⟨1, 0, 0⟩ : Vector3f))}, earth_to_body r (1,0,0) = {v3 (r.earth_to_body ⟨1, 0, 0⟩)}"
  let e := Quaternion.from_euler 0.1 (-0.2) 3.0
  line s!"from_euler 0.1 -0.2 3.0 = {q e}; to_euler_vec = {v3 e.to_euler_vec}"
  line s!"length r = {f r.length}, is_unit_length r = {b r.is_unit_length}, normalize ⟨2,0,0,0⟩ = {q (Quaternion.normalize ⟨2, 0, 0, 0⟩)}"
  line s!"normalize 0 = {q (Quaternion.normalize ⟨0, 0, 0, 0⟩)}, is_zero 0 = {b (Quaternion.is_zero ⟨0, 0, 0, 0⟩)}, is_nan = {b (Quaternion.is_nan ⟨nan, 0, 0, 0⟩)}"
  line s!"get_euler_pitch ⟨0.7071068,0,0.7071068,0⟩ = {f (Quaternion.get_euler_pitch ⟨0.7071068, 0, 0.7071068, 0⟩)} (safe_asin clips)"
  line s!"rotate id (0,0,0.5) = {q (id.rotate ⟨0, 0, 0.5⟩)}"

def control : IO Unit := do
  line "-- sqrt_controller (p = 4.5, D = 9.6)"
  let p : Float32 := 4.5
  let D : Float32 := 9.6
  let ld := D / sq p
  line s!"linear_dist = {f ld}"
  for e in [(0 : Float32), nz, small, ld, nextUp ld, -ld, nextDown (-ld), 1, -1, 100, nan] do
    line s!"e = {f e}: dt=0.0025 {f (sqrt_controller e p D 0.0025)}, dt=0 {f (sqrt_controller e p D 0)}"
  line s!"D = 0 (linear): {f (sqrt_controller 1 p 0 0)}; p = 0 (sqrt): {f (sqrt_controller 2 0 D 0)}, {f (sqrt_controller (-2) 0 D 0)}, {f (sqrt_controller small 0 D 0)}"
  line s!"continuity at branch: sqrt branch at nextUp ld {f (sqrt_controller (nextUp ld) p D 0)} vs p*ld {f (ld * p)}"
  line "-- inv_sqrt_controller / stopping_distance / sqrt_controller_accel"
  for o in [(0 : Float32), 1, -1, D / p, 5, -5] do
    line s!"output = {f o}: inv {f (inv_sqrt_controller o p D)}, round trip {f (sqrt_controller (inv_sqrt_controller o p D) p D 0)}"
  line s!"inv p = 0: {f (inv_sqrt_controller 3 0 D)}, D = 0: {f (inv_sqrt_controller 3 p 0)}, both 0: {f (inv_sqrt_controller 3 0 0)}"
  line s!"stopping_distance 5 1 2.5 = {f (stopping_distance 5 1 2.5)}"
  line s!"sqrt_controller_accel linear: {f (sqrt_controller_accel 0.1 0.45 0.3 p D)}, sqrt: {f (sqrt_controller_accel 1 (sqrt_controller 1 p D 0) 0.3 p D)}, away: {f (sqrt_controller_accel 1 1 (-0.3) p D)}, zero: {f (sqrt_controller_accel 0 0 0 p D)}"
  line "-- shape_accel / shape_vel_accel / shape_pos_vel_accel / shape_angle_vel_accel"
  line s!"shape_accel 10 0 50 0.0025 = {f (shape_accel 10 0 50 0.0025)}, jerk 0: {f (shape_accel 10 1 0 0.0025)}, dt 0: {f (shape_accel 10 1 50 0)}"
  line s!"shape_vel_accel 5 0 0 0 -2.5 2.5 5 0.0025 true = {f (shape_vel_accel 5 0 0 0 (-2.5) 2.5 5 0.0025 true)}"
  line s!"shape_vel_accel bad accel_min: {f (shape_vel_accel 5 0 0 0.7 0 2.5 5 0.0025 true)}"
  line s!"shape_pos_vel_accel 10 0 0 0 0 0 -5 5 -2.5 2.5 5 0.0025 true = {f (shape_pos_vel_accel 10 0 0 0 0 0 (-5) 5 (-2.5) 2.5 5 0.0025 true)}"
  line s!"shape_pos_vel_accel zero = {f (shape_pos_vel_accel 0 0 0 0 0 0 (-5) 5 (-2.5) 2.5 5 0.0025 true)}"
  line s!"shape_angle_vel_accel 3.1 0 0 -3.1 0 0 -3 3 19 80 0.0025 true = {f (shape_angle_vel_accel 3.1 0 0 (-3.1) 0 0 (-3) 3 19 80 0.0025 true)}"
  line "-- update_vel_accel / update_pos_vel_accel"
  line s!"update_vel_accel 1 2 0.0025 0 0 = {f (update_vel_accel 1 2 0.0025 0 0)}, limited: {f (update_vel_accel 1 2 0.0025 1 1)}, limited, vel opposing: {f (update_vel_accel (-0.001) 2 0.0025 1 1)}"
  let (pp, pv) := update_pos_vel_accel 100 1 2 0.0025 0 0 0
  line s!"update_pos_vel_accel 100 1 2 0.0025 0 0 0 = ({d pp}, {f pv})"
  let (pp, pv) := update_pos_vel_accel 100 1 2 0.0025 1 1 1
  line s!"update_pos_vel_accel limited = ({d pp}, {f pv})"
  line "-- 2-D"
  line s!"sqrt_controller_xy (3,4) = {v2 (sqrt_controller_xy ⟨3, 4⟩ p D 0.0025)}, 0 = {v2 (sqrt_controller_xy {} p D 0.0025)}"
  line s!"limit_accel_xy (1,0) (3,4) 2 = {v2 (limit_accel_xy ⟨1, 0⟩ ⟨3, 4⟩ 2).1}, ref 0.1: {v2 (limit_accel_xy ⟨0.1, 0⟩ ⟨3, 4⟩ 2).1}, ref 0: {v2 (limit_accel_xy {} ⟨3, 4⟩ 2).1}, under: {b (limit_accel_xy ⟨1, 0⟩ ⟨1, 1⟩ 2).2}"
  line s!"limit_accel_corner_xy (1,0) (3,4) 2 = {v2 (limit_accel_corner_xy ⟨1, 0⟩ ⟨3, 4⟩ 2).1}, braking: {v2 (limit_accel_corner_xy ⟨1, 0⟩ ⟨-3, 4⟩ 2).1}, vel 0: {v2 (limit_accel_corner_xy {} ⟨3, 4⟩ 2).1}"
  line s!"shape_accel_xy (10,0) 0 50 0.0025 = {v2 (shape_accel_xy ⟨10, 0⟩ {} 50 0.0025)}, vec3: {v3 (shape_accel_xy_vec3 ⟨10, 0, 7⟩ ⟨0, 0, -1⟩ 50 0.0025)}"
  line s!"shape_vel_accel_xy (5,0) 0 (0,1) 0 2.5 5 0.0025 true = {v2 (shape_vel_accel_xy ⟨5, 0⟩ {} ⟨0, 1⟩ {} 2.5 5 0.0025 true)}"
  line s!"shape_pos_vel_accel_xy (10,0) 0 0 (0,0) (0,1) 0 5 2.5 5 0.0025 true = {v2 (shape_pos_vel_accel_xy ⟨10, 0⟩ {} {} {} ⟨0, 1⟩ {} 5 2.5 5 0.0025 true)}"
  line s!"shape_pos_vel_accel_xy zero = {v2 (shape_pos_vel_accel_xy {} {} {} {} {} {} 5 2.5 5 0.0025 true)}"
  let (pp, pv) := update_pos_vel_accel_xy ⟨100, -100⟩ ⟨1, 1⟩ ⟨2, -2⟩ 0.0025 {} {} {}
  line s!"update_pos_vel_accel_xy = ({v2p pp}, {v2 pv})"
  let (pp, pv) := update_pos_vel_accel_xy ⟨100, -100⟩ ⟨1, 1⟩ ⟨2, 2⟩ 0.0025 ⟨1, 0⟩ ⟨1, 0⟩ ⟨1, 0⟩
  line s!"update_pos_vel_accel_xy limited = ({v2p pp}, {v2 pv})"
  line "-- kinematic_limit / angle conversions"
  for dir in [(⟨1, 0, 0⟩ : Vector3f), ⟨0, 0, 1⟩, ⟨0, 0, -1⟩, ⟨1, 0, 1⟩, ⟨1, 0, -0.1⟩, {}] do
    line s!"kinematic_limit {v3 dir} 10 1.5 2.5 = {f (kinematic_limit dir 10 1.5 2.5)}"
  line s!"angle_rad_to_accel_mss (radians 30) = {f (angle_rad_to_accel_mss (radians 30))}, angle_deg_to_accel_mss 45 = {f (angle_deg_to_accel_mss 45)}"
  line s!"accel_mss_to_angle_rad 9.80665 = {f (accel_mss_to_angle_rad 9.80665)}, accel_mss_to_angle_deg 9.80665 = {f (accel_mss_to_angle_deg 9.80665)}"

end AP_Math.Check

def main : IO Unit := do
  AP_Math.Check.scalars
  AP_Math.Check.vectors
  AP_Math.Check.quats
  AP_Math.Check.control
