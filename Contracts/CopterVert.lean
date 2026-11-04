import Mathlib.Tactic

/-!
# The vertical channel of the ArduCopter hover: the exact-arithmetic recurrence and its Lyapunov
function

At a hover sample (level, at rest horizontally, horizontal targets zero, the navigator's target
fixed at the waypoint altitude), the vertical path of the ported ArduCopter stack
(`AC_PosControl.D_update_controller`, `AC_AttitudeControl_Multi.set_throttle_out`,
`AP_MotorsMulticopter.update_throttle_filter` and the linear thrust configuration) closed with the
Crazyflie plant of `Contracts.CopterPlant` is, in exact arithmetic, the linear recurrence `step` on
six real states, per 400 Hz tick:

* `ζ`: altitude error, `z - z_target` (NED, positive below the target), meters;
* `w`: vertical velocity (NED), meters per second;
* `Ev`: the error filter `_error` of the velocity PID `_pid_vel_d_m` (`AC_PID_Basic`, 5 Hz,
  `PSC_D_VEL_P = 5`, `I = D = FF = 0`), meters per second;
* `Ea`: the error filter `_error` of the acceleration PID `_pid_accel_d_m` (`AC_PID`, 20 Hz,
  `PSC_D_ACC_P = 0.05`, `PSC_D_ACC_I = 0.1`, `D = FF = 0`), meters per second squared;
* `ι`: its integrator minus the equilibrium value `I* = MOT_THST_HOVER - 1/2.25`;
* `φ`: the motors' throttle filter output (2 Hz), which is the actuator and the plant's thrust
  fraction, minus the hover thrust fraction `1/2.25`.

The stored throttle `_throttle_in` (the one-tick delay between `set_throttle_out` and the next
tick's motors output) is `4/9 + τ` with `τ = -kp Ea - ι`, a function of the state; the plant's
stored specific force is `-k (φ + 4/9)`. The derivation, every constant and the Float32 rounding
budget are in `Contracts/VerticalChannel.md`.

The gains are the exact real values of the `Float32` constants the code computes (`calc_lowpass_alpha_dt`
at `dt = float(2500) * 1e-6f`, the literals `0.05f`, `0.1f`, `5.0f`, `1.0f`): the recurrence is the
code with every `Float32` operation on the state made exact, so the only differences between the
code and `step` are the rounding errors of those operations, the sensor rounding and the constant
`GRAVITY_MSS - 9.80665`, collected in `stepN` as four perturbations `n1 … n4`.

Proved here:
* `contr`: `V (step x) ≤ (249/250) V x` for the quadratic form `V x = xᵀ P x` with the rational `P`
  of `V`, by the exact sum-of-squares identity `contr_sos` (no `nlinarith`, no `polyrith`);
* `bound_0` … `bound_5`: on `V x ≤ 1/10`, `|ζ| ≤ 1/200`, `|w| ≤ 1/100`, `|Ev| ≤ 1/20`,
  `|Ea| ≤ 13/10`, `|ι| ≤ 14/10000`, `|φ| ≤ 1/100`;
* `lyap_stepN`: the sublevel set `V ≤ 1/10` is invariant under `stepN` for perturbations
  `|n1| ≤ 10⁻⁸`, `|n2| ≤ 10⁻⁶`, `|n3| ≤ 10⁻⁹`, `|n4| ≤ 10⁻⁷` (3 to 9 times the binary32 budget);
* `vert_invariant`: along any sequence that follows `stepN` with such perturbations while it is in
  the sublevel set, the state stays in it and in the box `|ζ| ≤ 1/200`, `|w| ≤ 1/100`.

Not here (the plan is in the notes): that the `Float32` code computes `stepN` with perturbations
within those bounds (the operation-by-operation forward error analysis, as `QuadHoverVert` did for
the old controller), and the link of the rational constants to the `Float32` values in the code.
-/

namespace Contracts.CopterVert

noncomputable section

/-! ## Constants: exact values of the `Float32` constants, and the plant -/

/-- `_dt_s = float(2500) * 1.0e-6f` (`Copter.scheduler_loop`), bits `0x3B23D70A`. -/
def dtc : ℝ := 5368709 / 2147483648
/-- `calc_lowpass_alpha_dt(dt, 5)`, the velocity error filter (`PSC_D_VEL_FLTE = 5`). -/
def av : ℝ := 4886901 / 67108864
/-- `calc_lowpass_alpha_dt(dt, 20)`, the acceleration error filter (`PSC_D_ACC_FLTE = 20`). -/
def aa : ℝ := 16042859 / 67108864
/-- `calc_lowpass_alpha_dt(dt, 2)`, the motors' throttle filter
(`POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ = 2`). -/
def am : ℝ := 16352567 / 536870912
/-- `PSC_D_ACC_P = 0.05f`. -/
def kp : ℝ := 13421773 / 268435456
/-- `PSC_D_ACC_I = 0.1f`. -/
def ki : ℝ := 13421773 / 134217728
/-- `PSC_D_VEL_P = 5.0f`. -/
def kv : ℝ := 5
/-- `PSC_D_POS_P = 1.0f` (the `sqrt_controller` in its linear region). -/
def kpos : ℝ := 1
/-- The plant's period, seconds. -/
def h : ℝ := 1 / 400
/-- The plant's gravity, `9.80665`. -/
def g : ℝ := 980665 / 100000
/-- Vertical acceleration per unit thrust fraction, `thrust_to_weight · g = 2.25 g`. -/
def k : ℝ := 9 / 4 * g

/-! ## The recurrence -/

/-- The six states of the vertical channel at the start of a tick (header). -/
@[ext]
structure VX where
  ζ : ℝ
  w : ℝ
  Ev : ℝ
  Ea : ℝ
  ι : ℝ
  φ : ℝ

instance : Add VX := ⟨fun a b => ⟨a.ζ + b.ζ, a.w + b.w, a.Ev + b.Ev, a.Ea + b.Ea, a.ι + b.ι, a.φ + b.φ⟩⟩

@[simp] theorem add_ζ (a b : VX) : (a + b).ζ = a.ζ + b.ζ := rfl
@[simp] theorem add_w (a b : VX) : (a + b).w = a.w + b.w := rfl
@[simp] theorem add_Ev (a b : VX) : (a + b).Ev = a.Ev + b.Ev := rfl
@[simp] theorem add_Ea (a b : VX) : (a + b).Ea = a.Ea + b.Ea := rfl
@[simp] theorem add_ι (a b : VX) : (a + b).ι = a.ι + b.ι := rfl
@[simp] theorem add_φ (a b : VX) : (a + b).φ = a.φ + b.φ := rfl

/-- One tick in exact arithmetic, in the order of the code: the motors filter the stored throttle
(`φ'`), the velocity PID filters its error (`Ev'`), the acceleration PID filters its error against
the measured acceleration `-k φ` of the last period (`Ea'`) and integrates (`ι'`); the plant moves
with the new actuator. -/
-- <<stepVert>>
def step (x : VX) : VX :=
  let Ev' := (1 - av) * x.Ev + av * (-(kpos * x.ζ) - x.w)
  let Ea' := (1 - aa) * x.Ea + aa * (kv * Ev' + k * x.φ)
  let ι' := x.ι + ki * dtc * Ea'
  let φ' := (1 - am) * x.φ + am * (-(kp * x.Ea) - x.ι)
  ⟨x.ζ + h * x.w, x.w - k * h * φ', Ev', Ea', ι', φ'⟩
-- <</stepVert>>

/-- The four perturbations of one tick (`Contracts/VerticalChannel.md`, "Perturbations"). -/
structure VN where
  n1 : ℝ
  n2 : ℝ
  n3 : ℝ
  n4 : ℝ

/-- One tick with the perturbations added where the code assigns: `n1` to the velocity error
filter, `n2` to the acceleration error filter, `n3` to the integrator, `n4` to the throttle
filter (which carries the rounding of the stored throttle of the previous tick). -/
-- <<stepNVert>>
def stepN (x : VX) (n : VN) : VX :=
  let Ev' := (1 - av) * x.Ev + av * (-(kpos * x.ζ) - x.w) + n.n1
  let Ea' := (1 - aa) * x.Ea + aa * (kv * Ev' + k * x.φ) + n.n2
  let ι' := x.ι + ki * dtc * Ea' + n.n3
  let φ' := (1 - am) * x.φ + am * (-(kp * x.Ea) - x.ι) + n.n4
  ⟨x.ζ + h * x.w, x.w - k * h * φ', Ev', Ea', ι', φ'⟩
-- <</stepNVert>>

/-- The effect of the perturbations on the next state. -/
def pert (n : VN) : VX :=
  ⟨0, -(k * h) * n.n4, n.n1, aa * kv * n.n1 + n.n2, ki * dtc * (aa * kv * n.n1 + n.n2) + n.n3, n.n4⟩

theorem stepN_eq (x : VX) (n : VN) : stepN x n = step x + pert n := by
  ext <;> simp only [stepN, step, pert, add_ζ, add_w, add_Ev, add_Ea, add_ι, add_φ] <;> ring

/-- The hover is the equilibrium of the exact recurrence. -/
theorem step_zero : step ⟨0, 0, 0, 0, 0, 0⟩ = ⟨0, 0, 0, 0, 0, 0⟩ := by
  ext <;> simp [step]

/-! ## The Lyapunov function -/

/-- `V x = xᵀ P x` with
`P = [[9200, 3300, 300, 21, 12000, -1600], [3300, 3200, 210, 18, -1100, -2800],`
`[300, 210, 82, 27/10, 1500, -160], [21, 18, 27/10, 6/25, 46, -23],`
`[12000, -1100, 1500, 46, 160000, 13000], [-1600, -2800, -160, -23, 13000, 5600]]`
in the coordinates `(ζ, w, Ev, Ea, ι, φ)`: the solution of a discrete Lyapunov equation
(`Contracts/VerticalChannel.md`) rounded to two significant digits. -/
-- <<Vvert>>
def V (x : VX) : ℝ :=
  9200 * (x.ζ * x.ζ) +
  6600 * (x.ζ * x.w) +
  600 * (x.ζ * x.Ev) +
  42 * (x.ζ * x.Ea) +
  24000 * (x.ζ * x.ι) +
  (-3200) * (x.ζ * x.φ) +
  3200 * (x.w * x.w) +
  420 * (x.w * x.Ev) +
  36 * (x.w * x.Ea) +
  (-2200) * (x.w * x.ι) +
  (-5600) * (x.w * x.φ) +
  82 * (x.Ev * x.Ev) +
  (27 / 5) * (x.Ev * x.Ea) +
  3000 * (x.Ev * x.ι) +
  (-320) * (x.Ev * x.φ) +
  (6 / 25) * (x.Ea * x.Ea) +
  92 * (x.Ea * x.ι) +
  (-46) * (x.Ea * x.φ) +
  160000 * (x.ι * x.ι) +
  26000 * (x.ι * x.φ) +
  5600 * (x.φ * x.φ)
-- <</Vvert>>

/-- `V` is a sum of squares (the `LDLᵀ` factorization of `P`). -/
theorem V_sos (x : VX) : V x =
    9200 * (x.ζ + (33 / 92) * x.w + (3 / 92) * x.Ev + (21 / 9200) * x.Ea + (30 / 23) * x.ι + (-(4 / 23)) * x.φ) ^ 2 +
    (46375 / 23) * (x.w + (471 / 9275) * x.Ev + (963 / 185500) * x.Ea + (-(4972 / 1855)) * x.ι + (-(2048 / 1855)) * x.φ) ^ 2 +
    (124318 / 1855) * (x.Ev + (13761 / 621590) * x.Ea + (1282860 / 62159) * x.ι + (4840 / 62159) * x.φ) ^ 2 +
    (325959 / 3107950) * (x.Ea + (49864750 / 325959) * x.ι + (-(24574250 / 325959)) * x.φ) ^ 2 +
    (32225058050 / 325959) * (x.ι + (66640441 / 644501161) * x.φ) ^ 2 +
    (780213464000 / 644501161) * (x.φ) ^ 2 := by
  simp only [V]; ring

/-- The contraction certificate: `249/250 V x - V (step x)` is a sum of squares (the exact
`LDLᵀ` factorization of `ρ P - Aᵀ P A`). -/
theorem contr_sos (x : VX) : (249 / 250) * V x - V (step x) =
    (348662757151666337575230687618079290890273917695006319943892504611 / 32910091146424120843099383651147010099654717312671597266972180480) * (x.ζ + (136715468830338947404239383486401271645032784003029552051149508643 / 348662757151666337575230687618079290890273917695006319943892504611) * x.w + (3533930079390100239464550986246951171049953171020135057014820899 / 348662757151666337575230687618079290890273917695006319943892504611) * x.Ev + (615707613072125545283185768591448878336013150576904335545918816256 / 43582844643958292196903835952259911361284239711875789992986563076375) * x.Ea + (61182955223547161230826449275481478732064703143365048815571185958912 / 43582844643958292196903835952259911361284239711875789992986563076375) * x.ι + (-(102742528581481623830671175432503527661456478561082335291471681814528 / 217914223219791460984519179761299556806421198559378949964932815381875)) * x.φ) ^ 2 +
    (1298473828647024348323822281318244569970070342182984015058083779441463 / 557860411442666140120369100188926865424438268312010111910228007377600) * (x.w + (35584523070939361499062935643123564809563039916827037547361534050736 / 1298473828647024348323822281318244569970070342182984015058083779441463) * x.Ev + (24998738720243400116729820397961804365628697067980112200713702013760831974548948397943309 / 9212544001331326234607445912521992938025383044985588747752330378744568663563414095790080000) * x.Ea + (-(973265928581761581696862914201469120045798055181573817081758127353539105596273070771 / 446152210300070200301322329278237775692082865479635647389219309850332858511523840000)) * x.ι + (-(581417958534057592969170595783730798250802726984459183773967393062709884071302664883 / 446152210300070200301322329278237775692082865479635647389219309850332858511523840000)) * x.φ) ^ 2 +
    (733996568371403115833726796003632470881037747355065398623099392691787947 / 162309228580878043540477785164780571246258792772873001882260472430182875) * (x.Ev + (31467820596367839105579696522735854210515874050833129070839901326085344034884901602166955997 / 13539846847728328140925915796708543404102007915695037345970827462405843176108164858723172352000) * x.Ea + (26375507596840667466215577775180673091686059165698529460591803851858688428491180171089 / 50439860104502469826213701802151439354203670902904262192438645148299050242111700992000) * x.ι + (7298303814140569602926464237223373547588598346367652863027700302996337245024746299217 / 50439860104502469826213701802151439354203670902904262192438645148299050242111700992000) * x.φ) ^ 2 +
    (8511145016048397438893969282764558262109595558292486243112615640693132522996958428929379407430645857241411366021770423 / 499532179194534981718044774232805310475832865719266469165454434870109139288496061176017365796629816670016241664000000000) * (x.Ea + (-(115075289436608494876092851807387156673948185428048100581525556236277304482370931696893272514487425733611634863581954048 / 2837048338682799146297989760921519420703198519430828747704205213564377507665652809643126469143548619080470455340590141)) * x.ι + (-(51226852117752700513154159581566893909664501787110036240240382725197532034162687194298223431078906117121053738718461952 / 14185241693413995731489948804607597103515992597154143738521026067821887538328264048215632345717743095402352276702950705)) * x.φ) ^ 2 +
    (262770277523907465953011350903588004465130120362059735879487442762268408096586039752124382726803206663730695334826217394228 / 2955258686127915777393739334293249396565831791073779945525213764129559903818388343378256738691196478208823390979781396875) * (x.ι + (382268244216904848229660405097117227070152404792808025719408319980904845527746485537634441966076781040107515023276702425229 / 65692569380976866488252837725897001116282530090514933969871860690567102024146509938031095681700801665932673833706554348557000) * x.φ) ^ 2 +
    (5565464554301909504204965120227870730519077157936982045678821140536223299754830214486440937560994150374024133960374892866228422979243053 / 26277027752390746595301135090358800446513012036205973587948744276226840809658603975212438272680320666373069533482621739422800000000000) * (x.φ) ^ 2 := by
  simp only [V, step, av, aa, am, kp, ki, dtc, kv, kpos, h, g, k]; ring

theorem V_sos_0 (x : VX) : V x =
    3200 * ((33 / 32) * x.ζ + x.w + (21 / 320) * x.Ev + (9 / 1600) * x.Ea + (-(11 / 32)) * x.ι + (-(7 / 8)) * x.φ) ^ 2 +
    (2183 / 32) * ((2670 / 2183) * x.ζ + x.Ev + (243 / 10915) * x.Ea + (50310 / 2183) * x.ι + (760 / 2183) * x.φ) ^ 2 +
    (5727 / 54575) * ((10550 / 1909) * x.ζ + x.Ea + (937925 / 5727) * x.ι + (-(424525 / 5727)) * x.φ) ^ 2 +
    (690528625 / 5727) * ((2546562 / 27621145) * x.ζ + x.ι + (2923999 / 27621145) * x.φ) ^ 2 +
    (6705853160 / 5524229) * ((17213587 / 167646329) * x.ζ + x.φ) ^ 2 +
    (780213464000 / 167646329) * x.ζ ^ 2 := by
  simp only [V]; ring

theorem bound_0 {x : VX} (hV : V x ≤ (1 / 10)) : |x.ζ| ≤ (1 / 200) := by
  have e := V_sos_0 x
  have hs : 0 ≤ 3200 * ((33 / 32) * x.ζ + x.w + (21 / 320) * x.Ev + (9 / 1600) * x.Ea + (-(11 / 32)) * x.ι + (-(7 / 8)) * x.φ) ^ 2 + (2183 / 32) * ((2670 / 2183) * x.ζ + x.Ev + (243 / 10915) * x.Ea + (50310 / 2183) * x.ι + (760 / 2183) * x.φ) ^ 2 + (5727 / 54575) * ((10550 / 1909) * x.ζ + x.Ea + (937925 / 5727) * x.ι + (-(424525 / 5727)) * x.φ) ^ 2 + (690528625 / 5727) * ((2546562 / 27621145) * x.ζ + x.ι + (2923999 / 27621145) * x.φ) ^ 2 + (6705853160 / 5524229) * ((17213587 / 167646329) * x.ζ + x.φ) ^ 2 := by positivity
  have h2 : x.ζ ^ 2 ≤ (1 / 200) ^ 2 := by nlinarith [sq_nonneg x.ζ]
  exact abs_le.2 (abs_le_of_sq_le_sq' h2 (by norm_num))

theorem V_sos_1 (x : VX) : V x =
    9200 * (x.ζ + (33 / 92) * x.w + (3 / 92) * x.Ev + (21 / 9200) * x.Ea + (30 / 23) * x.ι + (-(4 / 23)) * x.φ) ^ 2 +
    (1661 / 23) * ((2355 / 1661) * x.w + x.Ev + (927 / 33220) * x.Ea + (25500 / 1661) * x.ι + (-(2480 / 1661)) * x.φ) ^ 2 +
    (45123 / 332200) * ((842700 / 15041) * x.w + x.Ea + (-(4095800 / 45123)) * x.ι + (-(5427800 / 45123)) * x.φ) ^ 2 +
    (5694873800 / 45123) * ((-(2836209 / 56948738)) * x.w + x.ι + (312974 / 2588579) * x.φ) ^ 2 +
    (3495671000 / 2588579) * ((-(2059655 / 6991342)) * x.w + x.φ) ^ 2 +
    (39010673200 / 38452381) * x.w ^ 2 := by
  simp only [V]; ring

theorem bound_1 {x : VX} (hV : V x ≤ (1 / 10)) : |x.w| ≤ (1 / 100) := by
  have e := V_sos_1 x
  have hs : 0 ≤ 9200 * (x.ζ + (33 / 92) * x.w + (3 / 92) * x.Ev + (21 / 9200) * x.Ea + (30 / 23) * x.ι + (-(4 / 23)) * x.φ) ^ 2 + (1661 / 23) * ((2355 / 1661) * x.w + x.Ev + (927 / 33220) * x.Ea + (25500 / 1661) * x.ι + (-(2480 / 1661)) * x.φ) ^ 2 + (45123 / 332200) * ((842700 / 15041) * x.w + x.Ea + (-(4095800 / 45123)) * x.ι + (-(5427800 / 45123)) * x.φ) ^ 2 + (5694873800 / 45123) * ((-(2836209 / 56948738)) * x.w + x.ι + (312974 / 2588579) * x.φ) ^ 2 + (3495671000 / 2588579) * ((-(2059655 / 6991342)) * x.w + x.φ) ^ 2 := by positivity
  have h2 : x.w ^ 2 ≤ (1 / 100) ^ 2 := by nlinarith [sq_nonneg x.w]
  exact abs_le.2 (abs_le_of_sq_le_sq' h2 (by norm_num))

theorem V_sos_2 (x : VX) : V x =
    9200 * (x.ζ + (33 / 92) * x.w + (3 / 92) * x.Ev + (21 / 9200) * x.Ea + (30 / 23) * x.ι + (-(4 / 23)) * x.φ) ^ 2 +
    (46375 / 23) * (x.w + (471 / 9275) * x.Ev + (963 / 185500) * x.Ea + (-(4972 / 1855)) * x.ι + (-(2048 / 1855)) * x.φ) ^ 2 +
    (6387 / 46375) * ((22935 / 2129) * x.Ev + x.Ea + (2164075 / 6387) * x.ι + (-(361325 / 6387)) * x.φ) ^ 2 +
    (728445425 / 6387) * ((1124667 / 145689085) * x.Ev + x.ι + (3004505 / 29137817) * x.φ) ^ 2 +
    (35275108800 / 29137817) * ((-(297311 / 220469430)) * x.Ev + x.φ) ^ 2 +
    (975266830 / 22046943) * x.Ev ^ 2 := by
  simp only [V]; ring

theorem bound_2 {x : VX} (hV : V x ≤ (1 / 10)) : |x.Ev| ≤ (1 / 20) := by
  have e := V_sos_2 x
  have hs : 0 ≤ 9200 * (x.ζ + (33 / 92) * x.w + (3 / 92) * x.Ev + (21 / 9200) * x.Ea + (30 / 23) * x.ι + (-(4 / 23)) * x.φ) ^ 2 + (46375 / 23) * (x.w + (471 / 9275) * x.Ev + (963 / 185500) * x.Ea + (-(4972 / 1855)) * x.ι + (-(2048 / 1855)) * x.φ) ^ 2 + (6387 / 46375) * ((22935 / 2129) * x.Ev + x.Ea + (2164075 / 6387) * x.ι + (-(361325 / 6387)) * x.φ) ^ 2 + (728445425 / 6387) * ((1124667 / 145689085) * x.Ev + x.ι + (3004505 / 29137817) * x.φ) ^ 2 + (35275108800 / 29137817) * ((-(297311 / 220469430)) * x.Ev + x.φ) ^ 2 := by positivity
  have h2 : x.Ev ^ 2 ≤ (1 / 20) ^ 2 := by nlinarith [sq_nonneg x.Ev]
  exact abs_le.2 (abs_le_of_sq_le_sq' h2 (by norm_num))

theorem V_sos_3 (x : VX) : V x =
    9200 * (x.ζ + (33 / 92) * x.w + (3 / 92) * x.Ev + (21 / 9200) * x.Ea + (30 / 23) * x.ι + (-(4 / 23)) * x.φ) ^ 2 +
    (46375 / 23) * (x.w + (471 / 9275) * x.Ev + (963 / 185500) * x.Ea + (-(4972 / 1855)) * x.ι + (-(2048 / 1855)) * x.φ) ^ 2 +
    (124318 / 1855) * (x.Ev + (13761 / 621590) * x.Ea + (1282860 / 62159) * x.ι + (4840 / 62159) * x.φ) ^ 2 +
    (6297746800 / 62159) * ((199459 / 1259549360) * x.Ea + x.ι + (2801079 / 31488734) * x.φ) ^ 2 +
    (32463610500 / 15744367) * ((-(58783901 / 12985444200)) * x.Ea + x.φ) ^ 2 +
    (97526683 / 1623180525) * x.Ea ^ 2 := by
  simp only [V]; ring

theorem bound_3 {x : VX} (hV : V x ≤ (1 / 10)) : |x.Ea| ≤ (13 / 10) := by
  have e := V_sos_3 x
  have hs : 0 ≤ 9200 * (x.ζ + (33 / 92) * x.w + (3 / 92) * x.Ev + (21 / 9200) * x.Ea + (30 / 23) * x.ι + (-(4 / 23)) * x.φ) ^ 2 + (46375 / 23) * (x.w + (471 / 9275) * x.Ev + (963 / 185500) * x.Ea + (-(4972 / 1855)) * x.ι + (-(2048 / 1855)) * x.φ) ^ 2 + (124318 / 1855) * (x.Ev + (13761 / 621590) * x.Ea + (1282860 / 62159) * x.ι + (4840 / 62159) * x.φ) ^ 2 + (6297746800 / 62159) * ((199459 / 1259549360) * x.Ea + x.ι + (2801079 / 31488734) * x.φ) ^ 2 + (32463610500 / 15744367) * ((-(58783901 / 12985444200)) * x.Ea + x.φ) ^ 2 := by positivity
  have h2 : x.Ea ^ 2 ≤ (13 / 10) ^ 2 := by nlinarith [sq_nonneg x.Ea]
  exact abs_le.2 (abs_le_of_sq_le_sq' h2 (by norm_num))

theorem V_sos_4 (x : VX) : V x =
    9200 * (x.ζ + (33 / 92) * x.w + (3 / 92) * x.Ev + (21 / 9200) * x.Ea + (30 / 23) * x.ι + (-(4 / 23)) * x.φ) ^ 2 +
    (46375 / 23) * (x.w + (471 / 9275) * x.Ev + (963 / 185500) * x.Ea + (-(4972 / 1855)) * x.ι + (-(2048 / 1855)) * x.φ) ^ 2 +
    (124318 / 1855) * (x.Ev + (13761 / 621590) * x.Ea + (1282860 / 62159) * x.ι + (4840 / 62159) * x.φ) ^ 2 +
    (325959 / 3107950) * (x.Ea + (49864750 / 325959) * x.ι + (-(24574250 / 325959)) * x.φ) ^ 2 +
    (739122050 / 325959) * ((66640441 / 14782441) * x.ι + x.φ) ^ 2 +
    (780213464000 / 14782441) * x.ι ^ 2 := by
  simp only [V]; ring

theorem bound_4 {x : VX} (hV : V x ≤ (1 / 10)) : |x.ι| ≤ (7 / 5000) := by
  have e := V_sos_4 x
  have hs : 0 ≤ 9200 * (x.ζ + (33 / 92) * x.w + (3 / 92) * x.Ev + (21 / 9200) * x.Ea + (30 / 23) * x.ι + (-(4 / 23)) * x.φ) ^ 2 + (46375 / 23) * (x.w + (471 / 9275) * x.Ev + (963 / 185500) * x.Ea + (-(4972 / 1855)) * x.ι + (-(2048 / 1855)) * x.φ) ^ 2 + (124318 / 1855) * (x.Ev + (13761 / 621590) * x.Ea + (1282860 / 62159) * x.ι + (4840 / 62159) * x.φ) ^ 2 + (325959 / 3107950) * (x.Ea + (49864750 / 325959) * x.ι + (-(24574250 / 325959)) * x.φ) ^ 2 + (739122050 / 325959) * ((66640441 / 14782441) * x.ι + x.φ) ^ 2 := by positivity
  have h2 : x.ι ^ 2 ≤ (7 / 5000) ^ 2 := by nlinarith [sq_nonneg x.ι]
  exact abs_le.2 (abs_le_of_sq_le_sq' h2 (by norm_num))

theorem V_sos_5 (x : VX) : V x =
    9200 * (x.ζ + (33 / 92) * x.w + (3 / 92) * x.Ev + (21 / 9200) * x.Ea + (30 / 23) * x.ι + (-(4 / 23)) * x.φ) ^ 2 +
    (46375 / 23) * (x.w + (471 / 9275) * x.Ev + (963 / 185500) * x.Ea + (-(4972 / 1855)) * x.ι + (-(2048 / 1855)) * x.φ) ^ 2 +
    (124318 / 1855) * (x.Ev + (13761 / 621590) * x.Ea + (1282860 / 62159) * x.ι + (4840 / 62159) * x.φ) ^ 2 +
    (325959 / 3107950) * (x.Ea + (49864750 / 325959) * x.ι + (-(24574250 / 325959)) * x.φ) ^ 2 +
    (32225058050 / 325959) * (x.ι + (66640441 / 644501161) * x.φ) ^ 2 +
    (780213464000 / 644501161) * x.φ ^ 2 := by
  simp only [V]; ring

theorem bound_5 {x : VX} (hV : V x ≤ (1 / 10)) : |x.φ| ≤ (1 / 100) := by
  have e := V_sos_5 x
  have hs : 0 ≤ 9200 * (x.ζ + (33 / 92) * x.w + (3 / 92) * x.Ev + (21 / 9200) * x.Ea + (30 / 23) * x.ι + (-(4 / 23)) * x.φ) ^ 2 + (46375 / 23) * (x.w + (471 / 9275) * x.Ev + (963 / 185500) * x.Ea + (-(4972 / 1855)) * x.ι + (-(2048 / 1855)) * x.φ) ^ 2 + (124318 / 1855) * (x.Ev + (13761 / 621590) * x.Ea + (1282860 / 62159) * x.ι + (4840 / 62159) * x.φ) ^ 2 + (325959 / 3107950) * (x.Ea + (49864750 / 325959) * x.ι + (-(24574250 / 325959)) * x.φ) ^ 2 + (32225058050 / 325959) * (x.ι + (66640441 / 644501161) * x.φ) ^ 2 := by positivity
  have h2 : x.φ ^ 2 ≤ (1 / 100) ^ 2 := by nlinarith [sq_nonneg x.φ]
  exact abs_le.2 (abs_le_of_sq_le_sq' h2 (by norm_num))

theorem V_nonneg (x : VX) : 0 ≤ V x := by
  rw [V_sos]; positivity

/-- **Contraction.** The exact recurrence contracts `V` by `249/250` per tick. -/
-- <<contrVert>>
theorem contr (x : VX) : V (step x) ≤ 249 / 250 * V x := by
  have e := contr_sos x
  have : 0 ≤ 249 / 250 * V x - V (step x) := by rw [e]; positivity
  linarith
-- <</contrVert>>

/-! ## Perturbations -/

/-- `V (y + m) ≤ (1 + 1/500) V y + 501 V m`: the identity
`(501/500) V y + 501 V m - V (y + m) = 500 V (y/500 - m)`. -/
theorem V_pert (y m : VX) : V (y + m) ≤ 501 / 500 * V y + 501 * V m := by
  have hn := V_nonneg ⟨y.ζ / 500 - m.ζ, y.w / 500 - m.w, y.Ev / 500 - m.Ev, y.Ea / 500 - m.Ea,
    y.ι / 500 - m.ι, y.φ / 500 - m.φ⟩
  have e : 501 / 500 * V y + 501 * V m - V (y + m) =
      500 * V ⟨y.ζ / 500 - m.ζ, y.w / 500 - m.w, y.Ev / 500 - m.Ev, y.Ea / 500 - m.Ea,
        y.ι / 500 - m.ι, y.φ / 500 - m.φ⟩ := by
    simp only [V, add_ζ, add_w, add_Ev, add_Ea, add_ι, add_φ]; ring
  linarith

theorem term_le_pos {a b A B : ℝ} (c : ℝ) (hc : 0 ≤ c) (ha : |a| ≤ A) (hb : |b| ≤ B) :
    c * (a * b) ≤ c * (A * B) := by
  have h1 : a * b ≤ |a| * |b| := by rw [← abs_mul]; exact le_abs_self _
  have h2 : |a| * |b| ≤ A * B := mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)
  exact mul_le_mul_of_nonneg_left (h1.trans h2) hc

theorem term_le_neg {a b A B : ℝ} (c : ℝ) (hc : c ≤ 0) (ha : |a| ≤ A) (hb : |b| ≤ B) :
    c * (a * b) ≤ -c * (A * B) := by
  have h1 : -(a * b) ≤ |a| * |b| := by rw [← abs_mul]; exact neg_le_abs _
  have h2 : |a| * |b| ≤ A * B := mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)
  have := mul_le_mul_of_nonneg_left (h1.trans h2) (neg_nonneg.2 hc)
  linarith

theorem V_small (m : VX) (hζ : |m.ζ| ≤ 0) (hw : |m.w| ≤ (1 / 100000000)) (hEv : |m.Ev| ≤ (1 / 100000000)) (hEa : |m.Ea| ≤ (3 / 2500000)) (hι : |m.ι| ≤ (1 / 500000000)) (hφ : |m.φ| ≤ (1 / 10000000)) :
    V m ≤ (1 / 10000000000) := by
  have t0 := term_le_pos (c := 9200) (by norm_num) hζ hζ
  have t1 := term_le_pos (c := 6600) (by norm_num) hζ hw
  have t2 := term_le_pos (c := 600) (by norm_num) hζ hEv
  have t3 := term_le_pos (c := 42) (by norm_num) hζ hEa
  have t4 := term_le_pos (c := 24000) (by norm_num) hζ hι
  have t5 := term_le_neg (c := (-3200)) (by norm_num) hζ hφ
  have t6 := term_le_pos (c := 3200) (by norm_num) hw hw
  have t7 := term_le_pos (c := 420) (by norm_num) hw hEv
  have t8 := term_le_pos (c := 36) (by norm_num) hw hEa
  have t9 := term_le_neg (c := (-2200)) (by norm_num) hw hι
  have t10 := term_le_neg (c := (-5600)) (by norm_num) hw hφ
  have t11 := term_le_pos (c := 82) (by norm_num) hEv hEv
  have t12 := term_le_pos (c := (27 / 5)) (by norm_num) hEv hEa
  have t13 := term_le_pos (c := 3000) (by norm_num) hEv hι
  have t14 := term_le_neg (c := (-320)) (by norm_num) hEv hφ
  have t15 := term_le_pos (c := (6 / 25)) (by norm_num) hEa hEa
  have t16 := term_le_pos (c := 92) (by norm_num) hEa hι
  have t17 := term_le_neg (c := (-46)) (by norm_num) hEa hφ
  have t18 := term_le_pos (c := 160000) (by norm_num) hι hι
  have t19 := term_le_pos (c := 26000) (by norm_num) hι hφ
  have t20 := term_le_pos (c := 5600) (by norm_num) hφ hφ
  simp only [V]
  norm_num at *
  linarith


/-- The perturbation bounds (`Contracts/VerticalChannel.md`: each is 3 to 9 times the binary32 budget). -/
-- <<NBound>>
structure NBound (n : VN) : Prop where
  b1 : |n.n1| ≤ (1 / 100000000)
  b2 : |n.n2| ≤ (1 / 1000000)
  b3 : |n.n3| ≤ (1 / 1000000000)
  b4 : |n.n4| ≤ (1 / 10000000)
-- <</NBound>>

theorem abs_lin {c a A : ℝ} (ha : |a| ≤ A) : |c * a| ≤ |c| * A := by
  rw [abs_mul]; exact mul_le_mul_of_nonneg_left ha (abs_nonneg _)

theorem pert_small (n : VN) (hn : NBound n) :
    |(pert n).ζ| ≤ 0 ∧ |(pert n).w| ≤ (1 / 100000000) ∧ |(pert n).Ev| ≤ (1 / 100000000) ∧
      |(pert n).Ea| ≤ (3 / 2500000) ∧ |(pert n).ι| ≤ (1 / 500000000) ∧
      |(pert n).φ| ≤ (1 / 10000000) := by
  obtain ⟨b1, b2, b3, b4⟩ := hn
  have hkh : |-(k * h)| = 9 / 4 * (980665 / 100000) * (1 / 400) := by
    rw [abs_neg, abs_of_pos (by norm_num [k, g, h])]; norm_num [k, g, h]
  have hakv : |aa * kv| = 16042859 / 67108864 * 5 := by
    rw [abs_of_pos (by norm_num [aa, kv])]; norm_num [aa, kv]
  have hkd : |ki * dtc| = 13421773 / 134217728 * (5368709 / 2147483648) := by
    rw [abs_of_pos (by norm_num [ki, dtc])]; norm_num [ki, dtc]
  have hEa : |aa * kv * n.n1 + n.n2| ≤ (3 / 2500000) := by
    have := (abs_add_le (aa * kv * n.n1) n.n2).trans (add_le_add (abs_lin (c := aa * kv) b1) b2)
    rw [hakv] at this; linarith
  refine ⟨by simp [pert], ?_, b1, hEa, ?_, b4⟩
  · have := abs_lin (c := -(k * h)) b4
    rw [hkh] at this; simp only [pert]; linarith
  · have := (abs_add_le (ki * dtc * (aa * kv * n.n1 + n.n2)) n.n3).trans
      (add_le_add (abs_lin (c := ki * dtc) hEa) b3)
    rw [hkd] at this; simp only [pert]; linarith

/-- **Invariance.** The sublevel set `V ≤ 1/10` is invariant under the perturbed recurrence. -/
-- <<lyapStepNVert>>
theorem lyap_stepN {x : VX} (hV : V x ≤ 1 / 10) {n : VN} (hn : NBound n) :
    V (stepN x n) ≤ 1 / 10 := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := pert_small n hn
  have h1 := contr x
  have h2 := V_pert (step x) (pert n)
  have h3 := V_small (pert n) p1 p2 p3 p4 p5 p6
  rw [stepN_eq]
  linarith
-- <</lyapStepNVert>>

/-- The box of the sublevel set. -/
theorem box_of_V {x : VX} (hV : V x ≤ 1 / 10) : |x.ζ| ≤ 1 / 200 ∧ |x.w| ≤ 1 / 100 :=
  ⟨bound_0 hV, bound_1 hV⟩

/-- **The vertical channel stays in the box.** A sequence that starts in the sublevel set and, at
every tick where it is in the sublevel set, follows the perturbed recurrence with perturbations
within `NBound`, stays in the sublevel set; in particular within `5 mm` of the target altitude and
`1 cm/s` of rest. -/
-- <<vertInvariant>>
theorem vert_invariant (x : ℕ → VX) (h0 : V (x 0) ≤ 1 / 10)
    (hstep : ∀ t, V (x t) ≤ 1 / 10 → ∃ n : VN, NBound n ∧ x (t + 1) = stepN (x t) n) :
    ∀ t, V (x t) ≤ 1 / 10 ∧ |(x t).ζ| ≤ 1 / 200 ∧ |(x t).w| ≤ 1 / 100 := by
  have hV : ∀ t, V (x t) ≤ 1 / 10 := by
    intro t
    induction t with
    | zero => exact h0
    | succ t ih =>
      obtain ⟨n, hn, hx⟩ := hstep t ih
      rw [hx]; exact lyap_stepN ih hn
  exact fun t => ⟨hV t, box_of_V (hV t)⟩
-- <</vertInvariant>>

end

end Contracts.CopterVert
