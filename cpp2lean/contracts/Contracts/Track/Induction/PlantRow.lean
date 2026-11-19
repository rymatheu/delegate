import Contracts.Track.Induction.Horiz
import Contracts.Plant.Sharp

/-!
# M9: the plant's horizontal position row (P4)

`prow_le`: over one period, the position row against the realized mean acceleration,
`p' - p - h v - (h²/2) aReal`, is at most `1.8·10⁻⁷` per horizontal axis, from a unit quaternion
with body rates at most `2` rad/s and any actuators. From the plant's sharp step
(`Plant.step_pv_sharp`):

`p' - p - h v - (h/2)(v' - v) = a h³ ḋ / 12 + r_p - (h/2) r_v`,

with `|ḋ| ≤ √2 Ω₀` (`abs_dnDot_le`), `|r_p| ≤ a Cd h⁴/24`, `|r_v| ≤ a Cd h³/6`, `a ≤ 22.066`,
`Ω = wTA 2 alphaMax ≤ 3.7`, `Cd ≤ 900`: `8.2·10⁻⁸ + 9.7·10⁻⁸ ≤ 1.8·10⁻⁷`.

`qnorm_one`: the quaternion of every behavior from `Atakeoff` is a unit quaternion.
-/

namespace Contracts.Track.Induction

open Contracts Contracts.STL Contracts.Mission

noncomputable section

/-- `wB 2 ≤ 10`: the energy box of one period from rates at most `2` rad/s. -/
theorem wB_two_le : Plant.wB 2 ≤ 10 := by
  rw [Plant.wB, Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  have he := Real.exp_one_lt_d9
  have hc : Plant.ctau = (2 * Plant.lever * (Plant.thrust2weight * Plant.grav * Plant.mass / 4)) ^ 2 /
      Plant.Jx + (2 * Plant.lever * (Plant.thrust2weight * Plant.grav * Plant.mass / 4)) ^ 2 / Plant.Jy +
      (2 * Plant.kmkf * (Plant.thrust2weight * Plant.grav * Plant.mass / 4)) ^ 2 / Plant.Jz := by
    rw [Plant.ctau, Plant.fmax_eq]
  rw [hc, div_le_iff₀ Plant.Jx_pos]
  have hpos : 0 ≤ (Plant.Jx + Plant.Jy + Plant.Jz) * 2 ^ 2 +
      ((2 * Plant.lever * (Plant.thrust2weight * Plant.grav * Plant.mass / 4)) ^ 2 / Plant.Jx +
      (2 * Plant.lever * (Plant.thrust2weight * Plant.grav * Plant.mass / 4)) ^ 2 / Plant.Jy +
      (2 * Plant.kmkf * (Plant.thrust2weight * Plant.grav * Plant.mass / 4)) ^ 2 / Plant.Jz) *
        Plant.h ^ 2 := by
    norm_num [Plant.Jx, Plant.Jy, Plant.Jz, Plant.lever, Plant.thrust2weight, Plant.grav, Plant.mass,
      Plant.kmkf, Plant.km, Plant.kf, Plant.h]
  calc _ ≤ ((Plant.Jx + Plant.Jy + Plant.Jz) * 2 ^ 2 +
      ((2 * Plant.lever * (Plant.thrust2weight * Plant.grav * Plant.mass / 4)) ^ 2 / Plant.Jx +
      (2 * Plant.lever * (Plant.thrust2weight * Plant.grav * Plant.mass / 4)) ^ 2 / Plant.Jy +
      (2 * Plant.kmkf * (Plant.thrust2weight * Plant.grav * Plant.mass / 4)) ^ 2 / Plant.Jz) *
        Plant.h ^ 2) * 2.7182818286 := mul_le_mul_of_nonneg_left he.le hpos
    _ ≤ _ := by
      norm_num [Plant.Jx, Plant.Jy, Plant.Jz, Plant.lever, Plant.thrust2weight, Plant.grav,
        Plant.mass, Plant.kmkf, Plant.km, Plant.kf, Plant.h]

/-- The rate bound over one period at `W = 2` rad/s under the full torque. -/
theorem wTA_two_le : Plant.wTA 2 Plant.alphaMax ≤ 37 / 10 := by
  have hw := wB_two_le
  have hw0 : 0 ≤ Plant.wB 2 := Real.sqrt_nonneg _
  have : Plant.wB 2 ^ 2 ≤ 100 := by nlinarith
  have ha := Plant.alphaMax_le_num
  unfold Plant.wTA; norm_num [Plant.h, Plant.gyro] at *; nlinarith

theorem Cd_two_le : Plant.Cd Plant.alphaMax (37 / 10) ≤ 900 := by
  refine (Plant.Cd_mono Plant.alphaMax_pos.le Plant.alphaMax_le_num (by norm_num) le_rfl).trans ?_
  rw [Plant.Cd, Real.sqrt_le_iff]; norm_num

/-- **The position row of one period.** -/
theorem prow_step (y : Plant.X) (u : Fin 4 → ℝ) (hq : Plant.qnormSq y = 1) (hW : Plant.WBd y 2)
    (j : Fin 3) :
    |Plant.step y u (Plant.pI j) - y (Plant.pI j) - Plant.h * y (Plant.vI j) -
      Plant.h ^ 2 / 2 * ((Plant.step y u (Plant.vI j) - y (Plant.vI j)) / Plant.h)| ≤ 18 / 10 ^ 8 := by
  obtain ⟨hv, hp⟩ := Plant.step_pv_sharp hq hW (Plant.torqueBd_alphaMax u) wTA_two_le j
  have hd := Plant.abs_dnDot_le hq hW j
  have ha0 := Plant.accel_nonneg u
  have ha1 := (Plant.accel_le u).trans Plant.amax_le_num
  have hC := Cd_two_le
  have hC0 := Plant.Cd_nonneg Plant.alphaMax (37 / 10)
  have hs2 : Real.sqrt 2 ≤ 14143 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hh : Plant.h = 1 / 400 := rfl
  set a := Plant.accel u
  set D := Plant.dnDot y j
  set G := Plant.grav * Plant.ez j - a * Plant.dn y j
  set rv := Plant.step y u (Plant.vI j) - (y (Plant.vI j) + Plant.h * G - a * (Plant.h ^ 2 / 2) * D)
  set rp := Plant.step y u (Plant.pI j) - (y (Plant.pI j) + Plant.h * y (Plant.vI j) +
    Plant.h ^ 2 / 2 * G - a * (Plant.h ^ 3 / 6) * D)
  have e : Plant.step y u (Plant.pI j) - y (Plant.pI j) - Plant.h * y (Plant.vI j) -
      Plant.h ^ 2 / 2 * ((Plant.step y u (Plant.vI j) - y (Plant.vI j)) / Plant.h) =
      a * Plant.h ^ 3 / 12 * D + rp - Plant.h / 2 * rv := by
    simp only [rv, rp]; rw [hh]; field_simp; ring
  rw [e]
  have hD : |D| ≤ 14143 / 10000 * 2 := hd.trans (by nlinarith)
  have hCa : a * Plant.Cd Plant.alphaMax (37 / 10) ≤ 22066 / 1000 * 900 := by nlinarith
  have t1 : |a * Plant.h ^ 3 / 12 * D| ≤ 22066 / 1000 * (1 / 400) ^ 3 / 12 * (14143 / 10000 * 2) := by
    rw [abs_mul, abs_of_nonneg (by rw [hh]; positivity), hh]
    exact mul_le_mul (by gcongr) hD (abs_nonneg _) (by positivity)
  have t2 : |rp| ≤ 22066 / 1000 * 900 * (1 / 400) ^ 4 / 24 := by
    refine hp.trans ?_; rw [hh]; nlinarith
  have t3 : |Plant.h / 2 * rv| ≤ (1 / 400) / 2 * (22066 / 1000 * 900 * (1 / 400) ^ 3 / 6) := by
    rw [abs_mul, abs_of_nonneg (by rw [hh]; positivity), hh]
    exact mul_le_mul_of_nonneg_left (hv.trans (by rw [hh]; nlinarith)) (by norm_num)
  calc |a * Plant.h ^ 3 / 12 * D + rp - Plant.h / 2 * rv|
      ≤ |a * Plant.h ^ 3 / 12 * D| + |rp| + |Plant.h / 2 * rv| := by
        have := abs_sub (a * Plant.h ^ 3 / 12 * D + rp) (Plant.h / 2 * rv)
        have := abs_add_le (a * Plant.h ^ 3 / 12 * D) rp
        linarith
    _ ≤ _ := by linarith

/-- The quaternion of every behavior of the plant from `Atakeoff` is a unit quaternion. -/
theorem qnorm_one {sense32 : ℝ → Float32} {senseP : ℝ → Float} {x : ℕ → Mission.X}
    (hx : x ∈ Mplant sense32 senseP) (hA : x ∈ Atakeoff) (t : ℕ) :
    Plant.qnormSq (x t).phys.x = 1 := by
  induction t with
  | zero =>
    obtain ⟨p, ψ, -, h0⟩ := hA
    rw [h0]
    simp only [startP, startState, yawQuat, Plant.qnormSq, Plant.State.toX]
    simp
  | succ t ih =>
    rw [(mem_Mplant.1 hx t).1]
    simp only [Plant.next, Plant.nextR]
    rw [Plant.qnormSq_step]; exact ih

/-- **`prow_le`**: the horizontal position row of every tick with body rates at most `2`. -/
theorem prow_le {sense32 : ℝ → Float32} {senseP : ℝ → Float} {x : ℕ → Mission.X}
    (hx : x ∈ Mplant sense32 senseP) (hA : x ∈ Atakeoff) (t : ℕ)
    (hw : |ph x t 10| ≤ 2 ∧ |ph x t 11| ≤ 2 ∧ |ph x t 12| ≤ 7 / 5) (a : Fin 2) :
    |prow x t a| ≤ 18 / 10 ^ 8 := by
  have hW : Plant.WBd (x t).phys.x 2 := ⟨hw.1, hw.2.1, hw.2.2.trans (by norm_num)⟩
  have h := prow_step (x t).phys.x (Plant.act (x t).out.act) (qnorm_one hx hA t) hW a.castSucc
  have hn := (mem_Mplant.1 hx t).1
  simp only [prow, aReal, ph, hn, Plant.next, Plant.nextR]
  rw [show pIx a.castSucc = Plant.pI a.castSucc from rfl,
    show vIx a.castSucc = Plant.vI a.castSucc from rfl]
  exact h

end

end Contracts.Track.Induction
