import Vehicle
import MissionData.Course

/-!
# `quick_cex`: evaluated counterexamples for QUICK.md

Runs the controller step (`Contracts.Mission.tickT`, copied as `tickC` so that the executable does
not link Mathlib) from `boot w`, `construct lines = .ok w`, on short sample streams, and prints the
mixer inputs, the rate targets, the thrust vector and the mission index after each tick.

`lake build quick_cex && .lake/build/bin/quick_cex (q1|nan|q2|q6|q3)`
-/
open Vehicle

def tickC (w₀ : World) (s : Option World) (smp : Sample) : World × Array Float32 :=
  let wa := match s with | some w => w | none => takeover w₀ smp
  tick wa smp

def rest (gx gy gz : Float32) (q : AC_Attitude_lib.Quaternion.State := { q1 := 1, q2 := 0, q3 := 0, q4 := 0 }) (z : Float := 0) (vx vz : Float32 := 0) : Sample :=
  { pos := { x := 0, y := 0, z := z }, vel := { x := vx, y := 0, z := vz },
    acc := { x := 0, y := 0, z := -9.80665 }, quat := q,
    gyro := { x := gx, y := gy, z := gz }, dt_us := 2500 }

def run (lines : List String) (smps : List Sample) : IO Unit := do
  match construct lines with
  | .error e => IO.println s!"error {e}"
  | .ok w =>
    let w₀ := boot w
    let mut s : Option World := none
    let mut t := 0
    for smp in smps do
      let (w', act) := tickC w₀ s smp
      s := some w'
      let rb := AC_Attitude_lib.AC_AttitudeControl_Multi.rate_bf_targets w'.as
      IO.println s!"t={t} roll_in={w'.ms._roll_in} pitch_in={w'.ms._pitch_in} yaw_in={w'.ms._yaw_in} thr_in={w'.ms._throttle_in} thr_filt={w'.ms._throttle_filter.output} thr_avg_max={w'.ms._throttle_avg_max} rate_bf=({rb.x},{rb.y},{rb.z}) act={act}"
      let tv := AC_PosControl_lib.AC_PosControl.get_thrust_vector w'.ps
      IO.println s!"    tv=({tv.x},{tv.y},{tv.z}) angmax={w'.ap._ang_vel_roll_max_degs},{w'.ap._ang_vel_yaw_max_degs} nav={w'.au.nav_index}"
      let ps := w'.ps
      IO.println s!"    vel_target=({ps._vel_target_ned_ms.x},{ps._vel_target_ned_ms.y},{ps._vel_target_ned_ms.z}) accel_target=({ps._accel_target_ned_mss.x},{ps._accel_target_ned_mss.y},{ps._accel_target_ned_mss.z}) vel_desired=({ps._vel_desired_ned_ms.x},{ps._vel_desired_ned_ms.y},{ps._vel_desired_ned_ms.z}) pos_desired=({ps._pos_desired_ned_m.x},{ps._pos_desired_ned_m.y},{ps._pos_desired_ned_m.z}) roll_t={ps._roll_target_rad} pitch_t={ps._pitch_target_rad}"
      t := t + 1

/-- Q4: a feedback stream (each sample at the previous tick's position target with the previous
tick's velocity target, level, at rest in acceleration), and the largest velocity and
acceleration references the navigator writes into `AC_PosControl` over `n` ticks. -/
def q4 (n : Nat) : IO Unit := do
  match construct MissionData.courseLines with
  | .error e => IO.println s!"error {e}"
  | .ok w =>
    let w₀ := boot w
    let p := w₀.wpp
    IO.println s!"WP_SPD={p._wp_speed_ms} WP_SPD_UP={p._wp_speed_up_ms} WP_SPD_DN={p._wp_speed_down_ms} WP_ACC={p._wp_accel_mss} WP_ACC_C={p._wp_accel_c_mss} WP_ACC_Z={p._wp_accel_z_mss} WP_JERK={p._wp_jerk_msss} WP_RADIUS={p._wp_radius_m}"
    let mut s : Option World := none
    let mut smp := rest 0 0 0
    let mut vxy : Float := 0
    let mut vup : Float := 0
    let mut vdn : Float := 0
    let mut axy : Float := 0
    let mut az : Float := 0
    let mut tv : Nat := 0
    let mut ta : Nat := 0
    for t in [0:n] do
      let (w', _) := tickC w₀ s smp
      s := some w'
      let ps := w'.ps
      let vd := ps._vel_desired_ned_ms
      let ad := ps._accel_desired_ned_mss
      let h := Float.sqrt (vd.x.toFloat ^ 2 + vd.y.toFloat ^ 2)
      if h > vxy then vxy := h; tv := t
      if -vd.z.toFloat > vup then vup := -vd.z.toFloat
      if vd.z.toFloat > vdn then vdn := vd.z.toFloat
      let ah := Float.sqrt (ad.x.toFloat ^ 2 + ad.y.toFloat ^ 2)
      if ah > axy then axy := ah; ta := t
      if Float.abs ad.z.toFloat > az then az := Float.abs ad.z.toFloat
      let pd := ps._pos_desired_ned_m
      smp := { pos := { x := pd.x, y := pd.y, z := pd.z }, vel := vd,
               acc := { x := 0, y := 0, z := -9.80665 }, quat := { q1 := 1, q2 := 0, q3 := 0, q4 := 0 },
               gyro := { x := 0, y := 0, z := 0 }, dt_us := 2500 }
    IO.println s!"max |v_desired_NE| - 1 = {vxy - 1.0} (exact {exactDecimal vxy})"
    IO.println s!"max |v_desired_NE| = {vxy} (tick {tv}), max up = {vup}, max down = {vdn}, max |a_desired_NE| = {axy} (tick {ta}), max |a_desired_D| = {az}"

/-- Q3: search for finite inputs on which `limit_accel_xy` returns an acceleration longer than its
limit (pseudo-random accelerations of magnitude up to `10^k`, a fixed reference direction). -/
def q3 : IO Unit := do
  let amax : Float32 := 5.66   -- 9.80665 * tan(30°)
  let mut worst : Float := 0
  let mut wa : AC_PosControl_lib.Vector2f.State := {}
  let mut wv : AC_PosControl_lib.Vector2f.State := {}
  let mut seed : UInt64 := 12345
  for _ in [0:2000000] do
    seed := seed * 6364136223846793005 + 1442695040888963407
    let u1 := (seed >>> 11).toFloat / 9007199254740992.0
    seed := seed * 6364136223846793005 + 1442695040888963407
    let u2 := (seed >>> 11).toFloat / 9007199254740992.0
    seed := seed * 6364136223846793005 + 1442695040888963407
    let u3 := (seed >>> 11).toFloat / 9007199254740992.0
    seed := seed * 6364136223846793005 + 1442695040888963407
    let u4 := (seed >>> 11).toFloat / 9007199254740992.0
    let mag := Float.pow 10.0 (u1 * 6.0)
    let vang := u3 * 6.283185307179586
    let ang := vang + (u2 - 0.5) * 1.0e-5 * Float.pow 10.0 (u2 * 5.0)
    let vmag := u4
    let a : AC_PosControl_lib.Vector2f.State := { x := (mag * Float.cos ang).toFloat32, y := (mag * Float.sin ang).toFloat32 }
    let v : AC_PosControl_lib.Vector2f.State := { x := (vmag * Float.cos vang).toFloat32, y := (vmag * Float.sin vang).toFloat32 }
    let (r, _) := AC_PosControl_lib.limit_accel_xy v a amax
    let l := Float.sqrt (r.x.toFloat ^ 2 + r.y.toFloat ^ 2) / amax.toFloat
    if l > worst then
      worst := l; wa := a; wv := v
  IO.println s!"worst |out|/accel_max = {worst} at accel=({wa.x},{wa.y}) vel_norm=({wv.x},{wv.y})"

/-- Q3 at tick level: the nominal feedback stream up to tick `n0`, then one sample whose velocity is
offset by `m` in direction `θ`; the ratio of the thrust vector's horizontal length to
`9.80665 tan(lean angle max)` after that tick. -/
def q3t : IO Unit := do
  match construct MissionData.courseLines with
  | .error e => IO.println s!"error {e}"
  | .ok w =>
    let w₀ := boot w
    let mut s : Option World := none
    let mut smp := rest 0 0 0
    for _ in [0:500] do
      let (w', _) := tickC w₀ s smp
      s := some w'
      let ps := w'.ps
      let pd := ps._pos_desired_ned_m
      smp := { pos := { x := pd.x, y := pd.y, z := pd.z }, vel := ps._vel_desired_ned_ms,
               acc := { x := 0, y := 0, z := -9.80665 }, quat := { q1 := 1, q2 := 0, q3 := 0, q4 := 0 },
               gyro := { x := 0, y := 0, z := 0 }, dt_us := 2500 }
    let some w500 := s | return
    let lim := AC_Attitude_lib.AC_AttitudeControl_Multi.lean_angle_max_rad w500.ap
    IO.println s!"lean_angle_max_rad = {lim}, vel_desired = ({w500.ps._vel_desired_ned_ms.x},{w500.ps._vel_desired_ned_ms.y})"
    let amax := 9.80665 * Float.tan lim.toFloat
    let mut worst : Float := 0
    let mut wm : Float := 0
    let mut wt : Float := 0
    for k in [0:80] do
      let m := Float.pow 10.0 (5.0 + k.toFloat / 20.0)
      for j in [0:2001] do
        let th := 0.7853981633974483 + (j.toFloat - 1000.0) * 1.0e-6
        let v := smp.vel
        let smp' := { smp with vel := { x := v.x + (m * Float.cos th).toFloat32, y := v.y + (m * Float.sin th).toFloat32, z := v.z } }
        let (w', _) := tickC w₀ s smp'
        let tv := AC_PosControl_lib.AC_PosControl.get_thrust_vector w'.ps
        let r := Float.sqrt (tv.x.toFloat ^ 2 + tv.y.toFloat ^ 2) / amax
        if r > worst then
          worst := r; wm := m; wt := th
    IO.println s!"worst |tv_NE| / (g tan(lean max)) = {worst} at velocity offset {wm} m/s, direction {wt} rad"

def main (args : List String) : IO Unit := do
  match args with
  | ["q1"] => run MissionData.courseLines [rest 0 0 0, rest 10 0 0, rest 0 0 0]
  | ["nan"] => run MissionData.courseLines [rest (0.0/0.0) 0 0, rest (0.0/0.0) 0 0]
  | ["q2"] => run (MissionData.courseLines ++ ["ATC_RATE_R_MAX 360", "ATC_RATE_P_MAX 360", "ATC_RATE_Y_MAX 60"]) [rest 0 0 0, rest 0 0 100 { q1 := 0, q2 := 1, q3 := 0, q4 := 0 }, rest 0 0 100 { q1 := 0, q2 := 1, q3 := 0, q4 := 0 }]
  | ["q6"] => run MissionData.courseLines [rest 0 0 0 (z := 1e300), rest 0 0 0 (z := 1e300)]
  | ["thr"] => run MissionData.courseLines [rest 0 0 0, rest 0 0 0 (vz := 3), rest 0 0 0 (vz := 3), rest 0 0 0 (vz := -3), rest 0 0 0 (vz := -3)]
  | ["q6b"] => run MissionData.courseLines [rest 0 0 0, rest 0 0 0 (vx := 3.0e38), rest 0 0 0 (vx := 3.0e38)]
  | ["thr2"] => run MissionData.courseLines [rest 0 0 0, rest 0 0 0 (z := -10) (vz := -3), rest 0 0 0 (z := -10) (vz := -3), rest 0 0 0 (z := 10) (vz := 3), rest 0 0 0 (z := 10) (vz := 3)]
  | ["q6c"] => run MissionData.courseLines [rest 0 0 0, rest 0 0 0 (z := 1.0e20), rest 0 0 0 (z := 1.0e20)]
  | ["q2b"] =>
    run (MissionData.courseLines ++ ["ATC_RATE_R_MAX 30", "ATC_RATE_P_MAX 30", "ATC_RATE_Y_MAX 30"]) (rest 0 0 0 :: List.replicate 40 (rest 0 0 0 ({ q1 := 0.9689124, q2 := 0.247404, q3 := 0, q4 := 0 } : AC_Attitude_lib.Quaternion.State)))
  | ["q2c"] =>
    run (MissionData.courseLines ++ ["ATC_RATE_R_MAX 30", "ATC_RATE_P_MAX 30", "ATC_RATE_Y_MAX 30"]) [rest 0 0 0, rest 0 0 10 ({ q1 := 0.9238795, q2 := 0.3826834, q3 := 0, q4 := 0 } : AC_Attitude_lib.Quaternion.State)]
  | ["q4"] => q4 12000
  | ["q3"] => q3
  | ["q3t"] => q3t
  | _ => IO.println "usage"
