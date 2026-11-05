import Vehicle
import MissionData.Course

/-!
# `nav_cex`: evaluated counterexamples to `nav_contract`

Drives the controller step `tickT w₀` of `Contracts/Mission/Loop.lean` (copied below verbatim as
`tickC`, so that this executable does not link Mathlib), from `w₀ = boot w` with
`construct courseLines = .ok w` (`MissionWorld`), with a feedback sample stream: the first sample is
the vehicle at rest at `START`, attitude `(1,0,0,0)`, specific force `(0, 0, -9.80665f)`; every later
sample is at the previous tick's target with the previous tick's desired velocity. Optionally
(`complete`) the velocity of the sample of the tick at which the mission completes is replaced by
`(VX, VY, VZ)`; or (`fuzz`, seed `VX`) every later sample is offset from the previous target by a
pseudo-random persistent offset of norm at most `0.09` m, with a pseudo-random velocity in
`[-3, 3]³` (`fuzznear`: within `0.3` m/s of the previous velocity target per component, so that the
mission completes); while the target rests at `w7` the velocity stays within `0.03` m/s per
component of the velocity target (the rest condition of `ψnavA`). Violations are counted before and
after the mission completes. With `complete`, the optional `OX OY OZ` offset the sample's position
at the completion tick. Every tick it checks `ψnavA` (`smpEnv`, period, `smpErr ≤ δs`) and `ψnavG`
(`inColumn` exactly on the doubles' rational values; `polyDist ≤ ρ` in double arithmetic).

`lake build nav_cex && .lake/build/bin/nav_cex START_X START_Y START_Z (none|complete) VX VY VZ`
-/

open Vehicle

/-- `Contracts.Mission.tickT`, verbatim, with `CtrlOut` as a pair. -/
def tickC (w₀ : Vehicle.World) (s : Option Vehicle.World) (smp : Vehicle.Sample) :
    Option Vehicle.World × AC_PosControl_lib.Vector3p.State × AC_PosControl_lib.Vector3f.State :=
  let wa := match s with
    | some w => w
    | none => Vehicle.takeover w₀ smp
  let r := Vehicle.tick wa smp
  (some r.1, AC_PosControl_lib.AC_PosControl.get_pos_desired_NED_m r.1.ps,
    AC_PosControl_lib.AC_PosControl.get_vel_desired_NED_ms r.1.ps)

/-- exact rational value of a finite double as (num, den) with den a power of 2 -/
def exactQ (x : Float) : Int × Nat :=
  let (neg, m, e) := decompose x
  let mi : Int := if neg then -(m : Int) else m
  if e ≥ 0 then (mi * (2 ^ e.toNat : Nat), 1) else (mi, 2 ^ (-e).toNat)

/-- x ≤ n/d exactly (d > 0) -/
def leQ (x : Float) (n : Int) (d : Nat) : Bool :=
  let (a, b) := exactQ x
  a * d ≤ n * b

def geQ (x : Float) (n : Int) (d : Nat) : Bool :=
  let (a, b) := exactQ x
  a * d ≥ n * b

def inColumnB (p : AC_PosControl_lib.Vector3p.State) : Bool :=
  leQ p.x 151 1000 && geQ p.x (-151) 1000 && leQ p.y 151 1000 && geQ p.y (-151) 1000 &&
  geQ p.z (-800) 1000 && leQ p.z 2 1000

def pts : Array (Float × Float × Float) :=
  #[(0,0,0),(0,0,-0.8),(1.25,1.25,-1.0),(0,2.5,-1.2),(-1.25,1.25,-1.4),(1.25,-1.25,-1.6),(0,-2.5,-1.4),(-1.25,-1.25,-1.1),(0,0,-0.8)]

def segDist (p a b : Float × Float × Float) : Float :=
  let (px,py,pz) := p; let (ax,ay,az) := a; let (bx,by_,bz) := b
  let (dx,dy,dz) := (bx-ax, by_-ay, bz-az)
  let l2 := dx*dx+dy*dy+dz*dz
  let t := ((px-ax)*dx+(py-ay)*dy+(pz-az)*dz)/l2
  let t := if t < 0 then 0 else if t > 1 then 1 else t
  let (qx,qy,qz) := (ax+t*dx, ay+t*dy, az+t*dz)
  Float.sqrt ((px-qx)^2+(py-qy)^2+(pz-qz)^2)

def polyDistF (p : AC_PosControl_lib.Vector3p.State) : Float := Id.run do
  let mut d := 1e9
  for i in [0:8] do
    let e := segDist (p.x,p.y,p.z) pts[i]! pts[i+1]!
    if e < d then d := e
  return d

def f32le (x : Float32) (b : Float) : Bool := x.isFinite && Float.abs x.toFloat ≤ b
def f64le (x : Float) (b : Float) : Bool := x.isFinite && Float.abs x ≤ b

def smpEnvB (s : Sample) : Bool :=
  f64le s.pos.x 11 && f64le s.pos.y 11 && f64le s.pos.z 11 &&
  f32le s.vel.x 3 && f32le s.vel.y 3 && f32le s.vel.z 3 &&
  f32le s.acc.x 23 && f32le s.acc.y 23 && f32le s.acc.z 23 &&
  f32le s.quat.q1 2 && f32le s.quat.q2 2 && f32le s.quat.q3 2 && f32le s.quat.q4 2 &&
  f32le s.gyro.x 11 && f32le s.gyro.y 11 && f32le s.gyro.z 11

def dist3 (a b : AC_PosControl_lib.Vector3p.State) : Float :=
  Float.sqrt ((a.x-b.x)^2+(a.y-b.y)^2+(a.z-b.z)^2)

def stateStr : MissionState → String
  | .STOPPED => "STOPPED" | .RUNNING => "RUNNING" | .COMPLETE => "COMPLETE"

/-- The S-curve of a straight leg from `o` to `d` with the navigator's limits in world `w`, sampled
in time: `(end position - length, max position - length, min position, largest backward step)`. -/
def scurveCheck (w : World) (o d : AC_WPNav_lib.Vector3p.State) : Float × Float × Float × Float × Float := Id.run do
  let wps := w.wps
  let inp := wpInputs w
  let sc := AC_WPNav_lib.SCurve.calculate_track wps._scurve_this_leg o d 0.0
    (inp.NE_get_max_speed_ms #[]) (inp.get_max_speed_up_ms #[]) (inp.get_max_speed_down_ms #[])
    (AC_WPNav_lib.AC_WPNav.get_wp_acceleration_mss w.wpp) (AC_WPNav_lib.AC_WPNav.get_accel_D_mss w.wpp)
    (AC_WPNav_lib.AC_WPNav.get_corner_acceleration_mss w.wpp) wps._scurve_snap_max_mssss wps._scurve_jerk_max_msss
  let L := Float.sqrt ((d.x - o.x) ^ 2 + (d.y - o.y) ^ 2 + (d.z - o.z) ^ 2)
  let tEnd := (AC_WPNav_lib.SCurve.time_end sc).toFloat
  let mut maxP : Float := -1e9
  let mut minP : Float := 1e9
  let mut back : Float := 0
  let mut prev : Float := 0
  for k in [0:40001] do
    let t : Float32 := (tEnd * k.toFloat / 40000.0).toFloat32
    let (_, _, _, P) := AC_WPNav_lib.SCurve.get_jerk_accel_vel_pos_at_time sc t 0 0 0 0
    let P := P.toFloat
    if P > maxP then maxP := P
    if P < minP then minP := P
    if prev - P > back then back := prev - P
    prev := P
  let (_, _, _, Pend) := AC_WPNav_lib.SCurve.get_jerk_accel_vel_pos_at_time sc (tEnd.toFloat32 + 1.0) 0 0 0 0
  return (Pend.toFloat - L, maxP - L, minP, back, tEnd)

def main (args : List String) : IO UInt32 := do
  let a := args.toArray
  let sx := (toF64 a[0]!).get!
  let sy := (toF64 a[1]!).get!
  let sz := (toF64 a[2]!).get!
  let mode := a[3]!
  let vx := (toF32 a[4]!).get!
  let vy := (toF32 a[5]!).get!
  let vz := (toF32 a[6]!).get!
  let ox := (toF64 (a.getD 7 "0")).get!
  let oy := (toF64 (a.getD 8 "0")).get!
  let oz := (toF64 (a.getD 9 "0")).get!
  let w ← match construct MissionData.courseLines with
    | .ok w => pure w
    | .error e => throw (IO.userError e)
  let w₀ := boot w
  if a[3]! == "scurve" then
    -- the navigator after the first tick (limits, jerk and snap set)
    let g0 : Float32 := (toF32 "-9.80665").get!
    let smp0 : Sample :=
      { pos := { x := 0, y := 0, z := 0 }, vel := { x := 0, y := 0, z := 0 }, acc := { x := 0, y := 0, z := g0 }, quat := { q1 := 1, q2 := 0, q3 := 0, q4 := 0 }, gyro := { x := 0, y := 0, z := 0 }, dt_us := 2500 }
    let (some w1, _, _) := tickC w₀ none smp0 | throw (IO.userError "no world")
    let (some w2, _, _) := tickC w₀ (some w1) smp0 | throw (IO.userError "no world")
    IO.println s!"jerk {w2.wps._scurve_jerk_max_msss} snap {w2.wps._scurve_snap_max_mssss} vmax {(wpInputs w2).NE_get_max_speed_ms #[]}"
    let pts := w2.mission
    for i in [0:7] do
      let (e, m, mn, b, te) := scurveCheck w2 pts[i]! pts[i+1]!
      IO.println s!"leg {i+1}: end-L {e} max-L {m} min {mn} back {b} T {te}"
    -- the first leg from starts in the box, and short loiter legs
    for k in [0:61] do
      let z := -0.301 + 0.302 * k.toFloat / 60.0
      for (x, y) in [(0.0, 0.0), (0.151, 0.151), (-0.151, 0.151)] do
        let (e, m, mn, b, _) := scurveCheck w2 { x := x, y := y, z := z } pts[0]!
        if m > 1e-6 || mn < 0 || b > 1e-6 then
          IO.println s!"leg 0 from ({x},{y},{z}): end-L {e} max-L {m} min {mn} back {b}"
    let mut worst : Float := -1
    for k in [1:301] do
      let l := 0.16 * k.toFloat / 300.0
      for (dx, dy, dz) in [(1.0, 0.0, 0.0), (0.6, 0.0, 0.8), (0.0, 0.0, 1.0), (0.0, 0.0, -1.0)] do
        let (e, m, mn, b, _) := scurveCheck w2 pts[7]! { x := pts[7]!.x + l * dx, y := pts[7]!.y + l * dy, z := pts[7]!.z + l * dz }
        if m > worst then worst := m
        if m > 1e-6 || mn < 0 || b > 1e-6 then
          IO.println s!"loiter leg {l} dir ({dx},{dy},{dz}): end-L {e} max-L {m} min {mn} back {b}"
    IO.println s!"loiter legs: worst max-L {worst}"
    return 0
  let g : Float32 := (toF32 "-9.80665").get!
  let mut st : Option World := none
  let mut prevT : AC_PosControl_lib.Vector3p.State := { x := sx, y := sy, z := sz }
  let mut prevV : AC_PosControl_lib.Vector3f.State := { x := 0, y := 0, z := 0 }
  let mut viol := 0
  let mut maxErr : Float := 0
  let mut envOk := true
  let mut spiked := false
  let mut prevState := MissionState.STOPPED
  let mut seed : UInt64 := (vx.toFloat.toUInt64) * 2654435761 + 12345
  let mut off : Float × Float × Float := (0, 0, 0)
  let mut violPre := 0
  let mut prevGate := false
  let mut maxPdPre : Float := 0
  for t in [0:12001] do
    -- the sample: start sample at t = 0; afterwards follow the previous target
    let mut vel := prevV
    let mut posS := prevT
    -- spike: at the tick where mission_update will complete the mission (flag set last tick,
    -- last nav cmd loaded); we detect it by predicting: reached flag set and nav_index = last
    let doSpike := mode == "complete" && !spiked && (match st with
      | some w => w.au.state == .RUNNING && AC_WPNav_lib.AC_WPNav.reached_wp_destination w.wps &&
                  w.au.nav_index + 1 == w.mission.size
      | none => false)
    if doSpike then
      vel := { x := vx, y := vy, z := vz }
      posS := { x := prevT.x + ox, y := prevT.y + oy, z := prevT.z + oz }
      spiked := true
    if mode == "fuzz" || mode == "fuzznear" then
      let rnd := fun (s : UInt64) => let s' := s * 6364136223846793005 + 1442695040888963407
        (s', (s' >>> 11).toFloat / (2.0 ^ 53) * 2.0 - 1.0)
      let (s1, r1) := rnd seed; let (s2, r2) := rnd s1; let (s3, r3) := rnd s2
      let (s4, r4) := rnd s3; let (s5, r5) := rnd s4; let (s6, r6) := rnd s5
      seed := s6
      let (ox, oy, oz) := off
      let (ox, oy, oz) := (0.95 * ox + 0.01 * r1, 0.95 * oy + 0.01 * r2, 0.95 * oz + 0.01 * r3)
      let n := Float.sqrt (ox*ox + oy*oy + oz*oz)
      let k := if n > 0.09 then 0.09 / n else 1.0
      off := (k * ox, k * oy, k * oz)
      posS := { x := prevT.x + k * ox, y := prevT.y + k * oy, z := prevT.z + k * oz }
      vel := if prevGate then
          { x := prevV.x + (0.03 * r4).toFloat32, y := prevV.y + (0.03 * r5).toFloat32, z := prevV.z + (0.03 * r6).toFloat32 }
        else if mode == "fuzznear" then
          { x := prevV.x + (0.3 * r4).toFloat32, y := prevV.y + (0.3 * r5).toFloat32, z := prevV.z + (0.3 * r6).toFloat32 }
        else { x := (3 * r4).toFloat32, y := (3 * r5).toFloat32, z := (3 * r6).toFloat32 }
    let smp : Sample :=
      if t == 0 then
        { pos := { x := sx, y := sy, z := sz }, vel := { x := 0, y := 0, z := 0 },
          acc := { x := 0, y := 0, z := g }, quat := { q1 := 1, q2 := 0, q3 := 0, q4 := 0 },
          gyro := { x := 0, y := 0, z := 0 }, dt_us := 2500 }
      else
        { pos := posS, vel := vel, acc := { x := 0, y := 0, z := g },
          quat := { q1 := 1, q2 := 0, q3 := 0, q4 := 0 }, gyro := { x := 0, y := 0, z := 0 },
          dt_us := 2500 }
    let (st', tgt, velT) := tickC w₀ st smp
    st := st'
    let e := dist3 smp.pos tgt
    if e > maxErr then maxErr := e
    -- the rest condition: target within 0.001 of w7 with velocity target at most 0.001 →
    -- sampled velocity within 0.055 of the velocity target
    let dW7 := Float.sqrt (tgt.x ^ 2 + tgt.y ^ 2 + (tgt.z + 0.8) ^ 2)
    let nV := Float.sqrt (velT.x.toFloat ^ 2 + velT.y.toFloat ^ 2 + velT.z.toFloat ^ 2)
    let eV := Float.sqrt ((smp.vel.x.toFloat - velT.x.toFloat) ^ 2 + (smp.vel.y.toFloat - velT.y.toFloat) ^ 2 +
      (smp.vel.z.toFloat - velT.z.toFloat) ^ 2)
    let gate := dW7 ≤ 0.001 && nV ≤ 0.001
    let restOk := !gate || eV ≤ 0.055
    prevGate := dW7 ≤ 0.005 && nV ≤ 0.005
    if doSpike then
      IO.println s!"tick {t}: rest gate {gate} (target {dW7} from w7, |velocity target| {nV}), sampled velocity error {eV}"
    if !(smpEnvB smp) || e > 0.096 || !restOk then
      envOk := false
      if viol < 8 then
        IO.println s!"ASSUMPTION FAILS at {t}: err {e}, rest gate {gate}, velocity error {eV}"
    let inCol := inColumnB tgt
    let pd := polyDistF tgt
    let ok := inCol || pd ≤ 0.155
    let some w := st | throw (IO.userError "no world")
    if w.au.state != prevState then
      IO.println s!"tick {t}: mission state {stateStr w.au.state}, target {tgt.x} {tgt.y} {tgt.z}"
      prevState := w.au.state
    if doSpike then
      IO.println s!"tick {t}: velocity sample ({vx}, {vy}, {vz}); target after the tick {tgt.x} {tgt.y} {tgt.z}; destination {w.wps._destination_ned_m.x} {w.wps._destination_ned_m.y} {w.wps._destination_ned_m.z}"
    if !ok then
      if viol < 8 || t % 200 == 0 then
        IO.println s!"VIOLATION tick {t}: target x={tgt.x} y={tgt.y} z={tgt.z} (exact z = {(exactQ tgt.z).1}/{(exactQ tgt.z).2}), polyDist≈{pd}, inColumn={inCol}, smpErr≈{e}"
      viol := viol + 1
    if w.au.state != .COMPLETE then
      if !ok then violPre := violPre + 1
      if !inCol && pd > maxPdPre then maxPdPre := pd
    prevT := tgt
    let vd := AC_PosControl_lib.AC_PosControl.get_vel_desired_NED_ms w.ps
    prevV := vd
  IO.println s!"violations before completion: {violPre}; max polyDist outside the column before completion {maxPdPre}"
  IO.println s!"violations: {viol}; max smpErr {maxErr}; assumptions hold: {envOk}; final target {prevT.x} {prevT.y} {prevT.z}"
  return 0
