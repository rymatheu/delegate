import Leanfc.AttitudeFilter

/-!
# EKF

Error-state (multiplicative) extended Kalman filter, a replacement for the pair AttitudeFilter +
NavFilter; the port of pyfc `ekf.py` (`/Users/ryan/Research/delegate/staging/pyfc/pyfc/ekf.py`),
operation for operation.

Nominal state: attitude q (body → NED), velocity v and position p (NED), gyro bias bg and
accelerometer bias ba (body). Error state δx = [δθ, δv, δp, δbg, δba] at offsets 0, 3, 6, 9, 12,
δθ a body-frame rotation vector with q_true = q ⊗ (1, δθ/2). Covariance P, 15 × 15, row-major
(`P[i][j]`), kept exactly symmetric.

Prediction (every tick): ω = gyro − bg, a_b = accel − ba; q ← normalize (q + ½ q ⊗ (0, ω) dt);
a_w = R(q) a_b + (0, 0, g); p ← p + v dt + a_w dt²/2; v ← v + a_w dt; P ← Φ P Φᵀ + Q with
Φ = I + F dt over the nonzero blocks of F (δθ̇ = −[ω]× δθ − δbg, δv̇ = −R [a_b]× δθ − R δba,
δṗ = δv), computed as (Φ (Φ P)ᵀ)ᵀ; then P ← (P + Pᵀ)/2 with its diagonal floored. ω also goes
through the 40 Hz low-pass for the rate loop.

Updates (fix ticks): sequential scalar updates, position north, east, down, then velocity north,
east, down, then heading. For a row h: u = P hᵀ, s = h u + var, K = u · (1/s), δx = K · residual,
P ← sym (P − K uᵀ); δx is injected at once (q ← normalize (q ⊗ (1, δθ/2)), the rest additive). The
heading arrives as (c, s) = (cos ψ, sin ψ); the residual is s ĉ − c ŝ with (ĉ, ŝ) the body x axis
projected on the horizontal and normalized, and its row is the third row of R(q).

Arithmetic: `+ - * /`, `R.sqrt`, comparisons and `max` in binary32; sums in the order of ekf.py.
The quaternion normalization multiplies by 1/‖q‖ as ekf.py does (Quat.normalize divides), so this
module has its own `normalize` and `rotRows` (ekf.py `_rot`, whose expressions differ from
`Quat.rotate`).

Deviations from ekf.py: the derived constants (Q per tick, the R variances, the low-pass
coefficient) are computed by `make` in binary32 from the binary32 parameters (ekf.py computes them
in binary64 and rounds once); the initial position variance and the gyro-bias prior after
calibration are parameters (`pos0`, `gyroBiasMin`; ekf.py has no calibration prior); the velocity
update runs whenever a velocity fix is present (ekf.py also needs `velocity` not `None`).
-/

namespace EKF

/-- A row of P (15 entries). -/
abbrev Row := Vector R 15
/-- P, row-major: `P[i][j]`. -/
abbrev Mat := Vector Row 15

/-- The parameter-file values (1σ, SI units). -/
structure Config where
  /-- rad/s per sample, gyro white noise -/
  gyroNoise : R
  /-- m/s² per sample, accelerometer white noise -/
  accelNoise : R
  /-- rad/s/√s, gyro-bias random walk -/
  gyroBiasWalk : R
  /-- m/s²/√s, accelerometer-bias random walk -/
  accelBiasWalk : R
  /-- m, position fix north/east -/
  posNE : R
  /-- m, position fix down -/
  posD : R
  /-- m/s, velocity fix per axis -/
  vel : R
  /-- rad, heading fix -/
  heading : R
  /-- rad, initial roll/pitch -/
  tilt0 : R
  /-- rad, initial yaw -/
  yaw0 : R
  /-- m/s, initial velocity -/
  vel0 : R
  /-- m, initial position -/
  pos0 : R
  /-- rad/s, initial gyro bias without calibration -/
  gyroBias0 : R
  /-- m/s², initial accelerometer bias -/
  accelBias0 : R
  /-- rad/s, floor of the gyro-bias prior after calibration -/
  gyroBiasMin : R
  /-- variance floor of every diagonal entry of P -/
  pFloor : R
  /-- Hz, low-pass of ω̂ for the rate loop -/
  cutoffHz : R
  deriving Inhabited, Repr

structure Params where
  cfg : Config
  /-- derived by `make`: dt, dt/2, dt²/2 -/
  dt : R
  halfDt : R
  halfDt2 : R
  /-- derived: Q per tick, diagonal: (σ_gyro dt)² ×3, (σ_accel dt)² ×3, 0 ×3, σ_bgw² dt ×3, σ_baw² dt ×3 -/
  qd : Row
  /-- derived: R variances -/
  rPos : Vec3
  rVel : R
  rHdg : R
  /-- derived: initial P diagonal (σ² of tilt, tilt, yaw, vel ×3, pos ×3, bg ×3, ba ×3) -/
  p0 : Row
  /-- derived: σ_gyro², and the floor σ_min² of the calibrated gyro-bias prior -/
  gyroVar : R
  gyroBiasVarMin : R
  /-- derived: a/(1+a), a = 2π cutoffHz dt -/
  lp : R
  deriving Inhabited, Repr

structure State where
  q : Quat
  v : Vec3
  p : Vec3
  bg : Vec3
  ba : Vec3
  omega : Vec3
  P : Mat
  deriving Inhabited, Repr

/-- The 15 entries `a ×3, b ×3, c ×3, d ×3, e ×3`. -/
def blocks (a b c d e : R) : Row :=
  Vector.ofFn fun i => if i.val < 3 then a else if i.val < 6 then b else if i.val < 9 then c
    else if i.val < 12 then d else e

def make (c : Config) (dt : R) : Params :=
  let sq (x : R) := x * x
  let a := AttitudeFilter.twoPi * c.cutoffHz * dt
  let halfDt := dt * 0.5
  { cfg := c, dt, halfDt, halfDt2 := halfDt * dt,
    qd := blocks (sq (c.gyroNoise * dt)) (sq (c.accelNoise * dt)) 0
      (sq c.gyroBiasWalk * dt) (sq c.accelBiasWalk * dt),
    rPos := ⟨sq c.posNE, sq c.posNE, sq c.posD⟩, rVel := sq c.vel, rHdg := sq c.heading,
    p0 := Vector.ofFn fun i =>
      if i.val < 2 then sq c.tilt0 else if i.val < 3 then sq c.yaw0 else if i.val < 6 then sq c.vel0
      else if i.val < 9 then sq c.pos0 else if i.val < 12 then sq c.gyroBias0 else sq c.accelBias0,
    gyroVar := sq c.gyroNoise, gyroBiasVarMin := sq c.gyroBiasMin,
    lp := a / (1 + a) }

/-! ## Matrix helpers -/

def transpose (M : Mat) : Mat := Vector.ofFn fun i => Vector.ofFn fun j => M[j][i]

/-- (P + Pᵀ) · 0.5, diagonal floored (ekf.py `_sym`). -/
def sym (floor : R) (P : Mat) : Mat :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    let x := (P[i][j] + P[j][i]) * 0.5
    if i = j then max x floor else x

/-- P with the diagonal entries `lo ≤ i < hi` replaced by `x`. -/
def setDiag (P : Mat) (lo hi : Nat) (x : R) : Mat :=
  Vector.ofFn fun i => Vector.ofFn fun j => if i = j ∧ lo ≤ i.val ∧ i.val < hi then x else P[i][j]

/-- The coefficients of Φ = I + F dt for one prediction: dt, ω dt, the rows of R [a_b]× dt and
of R dt. -/
structure Phi where
  dt : R
  wd : Vec3
  c0 : Vec3
  c1 : Vec3
  c2 : Vec3
  r0 : Vec3
  r1 : Vec3
  r2 : Vec3

/-- Φ M, row by row over the nonzero blocks of F (ekf.py `_phi`). -/
def Phi.apply (k : Phi) (M : Mat) : Mat :=
  let row (f : Fin 15 → R) : Row := Vector.ofFn f
  let vRow (c r : Vec3) (m : Row) : Row := row fun j =>
    m[j] - c.x * M[0][j] - c.y * M[1][j] - c.z * M[2][j] - r.x * M[12][j] - r.y * M[13][j] - r.z * M[14][j]
  let pRow (m dm : Row) : Row := row fun j => m[j] + k.dt * dm[j]
  #v[row fun j => M[0][j] + k.wd.z * M[1][j] - k.wd.y * M[2][j] - k.dt * M[9][j],
     row fun j => M[1][j] - k.wd.z * M[0][j] + k.wd.x * M[2][j] - k.dt * M[10][j],
     row fun j => M[2][j] + k.wd.y * M[0][j] - k.wd.x * M[1][j] - k.dt * M[11][j],
     vRow k.c0 k.r0 M[3], vRow k.c1 k.r1 M[4], vRow k.c2 k.r2 M[5],
     pRow M[6] M[3], pRow M[7] M[4], pRow M[8] M[5],
     M[9], M[10], M[11], M[12], M[13], M[14]]

/-! ## Quaternion helpers in ekf.py's operation order -/

/-- Rows of R(q), body → world (ekf.py `_rot`). -/
def rotRows (q : Quat) : Vec3 × Vec3 × Vec3 :=
  let xx := q.x * q.x; let yy := q.y * q.y; let zz := q.z * q.z
  let xy := q.x * q.y; let xz := q.x * q.z; let yz := q.y * q.z
  let wx := q.w * q.x; let wy := q.w * q.y; let wz := q.w * q.z
  (⟨1 - 2 * (yy + zz), 2 * (xy - wz), 2 * (xz + wy)⟩,
   ⟨2 * (xy + wz), 1 - 2 * (xx + zz), 2 * (yz - wx)⟩,
   ⟨2 * (xz - wy), 2 * (yz + wx), 1 - 2 * (xx + yy)⟩)

/-- q · (1/‖q‖) (ekf.py `_normalize`). -/
def normalize (q : Quat) : Quat :=
  let inv := 1 / R.sqrt (q.w * q.w + q.x * q.x + q.y * q.y + q.z * q.z)
  ⟨q.w * inv, q.x * inv, q.y * inv, q.z * inv⟩

/-! ## The filter -/

/-- At `p0` with attitude `q0`, zero velocity and biases, P = diag p0. -/
def init (k : Params) (p0 : Vec3) (q0 : Quat) : State :=
  { q := q0, v := Vec3.zero, p := p0, bg := Vec3.zero, ba := Vec3.zero, omega := Vec3.zero,
    P := Vector.ofFn fun i => Vector.ofFn fun j => if i = j then k.p0[i] else 0 }

/-- Gyro bias ← mean of the at-rest samples (a sum in sample order, then one division), and its
prior variance ← max (σ_gyro² / n, σ_min²), the variance of that mean. Unchanged without samples. -/
def calibrate (k : Params) (samples : Array Vec3) (st : State) : State :=
  if samples.isEmpty then st else
  let (sum, n) := samples.foldl (fun (acc : Vec3 × R) g => (acc.1 + g, acc.2 + 1)) (Vec3.zero, 0)
  { st with bg := Vec3.div sum n, P := setDiag st.P 9 12 (max (k.gyroVar / n) k.gyroBiasVarMin) }

def predict (k : Params) (st : State) (gyro accel : Vec3) : State :=
  let dt := k.dt
  let w := gyro - st.bg
  let a := accel - st.ba
  let (r0, r1, r2) := rotRows st.q
  let d := Quat.mul st.q ⟨0, w.x, w.y, w.z⟩
  let h := k.halfDt
  let q := normalize ⟨st.q.w + h * d.w, st.q.x + h * d.x, st.q.y + h * d.y, st.q.z + h * d.z⟩
  let aw : Vec3 := ⟨Vec3.dot r0 a, Vec3.dot r1 a, Vec3.dot r2 a + gravity⟩
  let p := st.p + Vec3.scale dt st.v + Vec3.scale k.halfDt2 aw
  let v := st.v + Vec3.scale dt aw
  let phi : Phi :=
    { dt, wd := Vec3.scale dt w,
      c0 := Vec3.scale dt (Vec3.cross r0 a), c1 := Vec3.scale dt (Vec3.cross r1 a),
      c2 := Vec3.scale dt (Vec3.cross r2 a),
      r0 := Vec3.scale dt r0, r1 := Vec3.scale dt r1, r2 := Vec3.scale dt r2 }
  let P := transpose (phi.apply (transpose (phi.apply st.P)))
  let P := Vector.ofFn fun i => Vector.ofFn fun j => if i = j then P[i][j] + k.qd[i] else P[i][j]
  { st with q, p, v, P := sym k.cfg.pFloor P, omega := st.omega + Vec3.scale k.lp (w - st.omega) }

/-- Scalar update with the row h (nonzero entries `(index, coefficient)`, at least one), residual
`r` and variance `var`; then injection (ekf.py `_update`). -/
def update (k : Params) (st : State) (h : List (Fin 15 × R)) (r var : R) : State :=
  let P := st.P
  let u : Row := match h with
    | [] => Vector.replicate 15 0
    | (i, c) :: rest =>
      rest.foldl (fun u (i', c') => Vector.ofFn fun m => u[m] + c' * P[m][i'])
        (Vector.ofFn fun m => c * P[m][i])
  let s := h.foldl (fun s (i, c) => s + c * u[i]) var
  let inv := 1 / s
  let kg := u.map (· * inv)
  let dx := kg.map (· * r)
  let half : R := 0.5
  { st with
    P := sym k.cfg.pFloor (Vector.ofFn fun i => Vector.ofFn fun j => P[i][j] - kg[i] * u[j]),
    q := normalize (Quat.mul st.q ⟨1, half * dx[0], half * dx[1], half * dx[2]⟩),
    v := st.v + ⟨dx[3], dx[4], dx[5]⟩, p := st.p + ⟨dx[6], dx[7], dx[8]⟩,
    bg := st.bg + ⟨dx[9], dx[10], dx[11]⟩, ba := st.ba + ⟨dx[12], dx[13], dx[14]⟩ }

/-- Heading fix (c, s) = (cos ψ, sin ψ): residual s ĉ − c ŝ, row = third row of R(q) on δθ. -/
def updateHeading (k : Params) (st : State) (c s : R) : State :=
  let (r0, r1, r2) := rotRows st.q
  let inv := 1 / R.sqrt (r0.x * r0.x + r1.x * r1.x)
  update k st [(0, r2.x), (1, r2.y), (2, r2.z)] (s * (r0.x * inv) - c * (r1.x * inv)) k.rHdg

/-- Three unit-row updates at the indices `i` (north, east, down) with fix `fix` of the estimate
`est` and variances `var`. -/
def update3 (k : Params) (st : State) (i : Fin 15 × Fin 15 × Fin 15) (fix : Vec3)
    (est : State → Vec3) (var : Vec3) : State :=
  let st := update k st [(i.1, 1)] (fix.x - (est st).x) var.x
  let st := update k st [(i.2.1, 1)] (fix.y - (est st).y) var.y
  update k st [(i.2.2, 1)] (fix.z - (est st).z) var.z

/-- One tick. Output: (q̂, ω̂ low-passed and bias-corrected, p̂, v̂). -/
def step (k : Params) (st : State) (gyro accel : Vec3) (heading : Option (R × R))
    (posFix velFix : Option Vec3) : State × (Quat × Vec3 × Vec3 × Vec3) :=
  let st := predict k st gyro accel
  let st := match posFix with
    | none => st
    | some f => update3 k st (6, 7, 8) f (·.p) k.rPos
  let st := match velFix with
    | none => st
    | some f => update3 k st (3, 4, 5) f (·.v) ⟨k.rVel, k.rVel, k.rVel⟩
  let st := match heading with
    | none => st
    | some (c, s) => updateHeading k st c s
  (st, (st.q, st.omega, st.p, st.v))

end EKF
