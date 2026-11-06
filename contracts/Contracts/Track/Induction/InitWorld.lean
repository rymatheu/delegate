import FloatModel.Lit
import Contracts.Track.Integrators

/-!
# M9: the M2 invariant of the mission's initial world (`init_world`)

`intOK_missionWorld`: the booted world of the course files satisfies `IntOK`. The PID limits are
the `kimax` fields of `MissionParams` (`0.5` for the three rate PIDs, `10` for the vertical
velocity PID, `0.8` for the vertical acceleration PID), which are proper limits (`KOK`). The
integrators are those of the controllers' `init` (`construct`), untouched by `boot`, and they
are `0`.
-/

namespace Contracts.Track.Induction

open Contracts.Mission Float.Model UnpackedFloat Contracts.Track.Att Contracts.Track.Pos

theorem unpack_lit_ten :
    (10 : Float32).toModel.unpack = .finite .positive 10485760 (-20) (by decide) := by f32_unpack
theorem unpack_lit_0_8 :
    (0.8 : Float32).toModel.unpack = .finite .positive 13421773 (-24) (by decide) := by f32_unpack

theorem kok_of {k : Float32} {s : Sign} {m : ℕ} {e : ℤ} {hm : 0 < m}
    (h : k.toModel.unpack = .finite s m e hm) (h0 : 0 ≤ k.toReal) (h1 : k.toReal ≤ 10) : KOK k :=
  ⟨Float32.isFinite_of_unpack h, h0, h1.trans (by rw [maxFinite32]; norm_num)⟩

theorem toReal_lit_ten : (10 : Float32).toReal = 10 := by
  rw [Float32.toReal_of_unpack unpack_lit_ten]; simp [Sign.apply]; norm_num

theorem toReal_lit_0_8 : (0.8 : Float32).toReal = 13421773 / 16777216 := by
  rw [Float32.toReal_of_unpack unpack_lit_0_8]; simp [Sign.apply]; norm_num

theorem kok_half : KOK (0.5 : Float32) :=
  kok_of Float32.unpack_lit_half (by simp) (by simp; norm_num)
theorem kok_ten : KOK (10 : Float32) :=
  kok_of unpack_lit_ten (by rw [toReal_lit_ten]; norm_num) (by rw [toReal_lit_ten])
theorem kok_0_8 : KOK (0.8 : Float32) :=
  kok_of unpack_lit_0_8 (by rw [toReal_lit_0_8]; norm_num) (by rw [toReal_lit_0_8]; norm_num)

/-- The controllers' states of a constructed world are their `init` states. -/
theorem construct_as_ps (lines : List String) (w : Vehicle.World)
    (h : Vehicle.construct lines = .ok w) :
    w.as = AC_Attitude_lib.AC_AttitudeControl_Multi.init.2 ∧
      w.ps = AC_PosControl_lib.AC_PosControl.init.2 := by
  unfold Vehicle.construct at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    rw [← h]
    exact ⟨rfl, rfl⟩

theorem init_rr : AC_Attitude_lib.AC_AttitudeControl_Multi.init.2._pid_rate_roll._integrator =
    (0.0 : Float32) := by with_unfolding_all rfl
theorem init_rp : AC_Attitude_lib.AC_AttitudeControl_Multi.init.2._pid_rate_pitch._integrator =
    (0.0 : Float32) := by with_unfolding_all rfl
theorem init_ry : AC_Attitude_lib.AC_AttitudeControl_Multi.init.2._pid_rate_yaw._integrator =
    (0.0 : Float32) := by with_unfolding_all rfl
theorem init_ad : AC_PosControl_lib.AC_PosControl.init.2._pid_accel_d_m._integrator =
    (0.0 : Float32) := by with_unfolding_all rfl
theorem init_vd : AC_PosControl_lib.AC_PosControl.init.2._pid_vel_d_m._integrator =
    (0.0 : Float32) := by with_unfolding_all rfl

theorem ib_zero {k : Float32} (hk : 0 ≤ k.toReal) : IB k (0.0 : Float32) :=
  ⟨Float32.isFinite_lit_zero, by simpa using hk⟩

/-- **`init_world`**: the mission's initial world satisfies the M2 invariant. -/
theorem intOK_missionWorld {w₀ : Vehicle.World} (hM : MissionWorld w₀) : IntOK w₀ := by
  have P := hM.params
  obtain ⟨w, hw, rfl⟩ := hM.built
  obtain ⟨has, hps⟩ := construct_as_ps _ w hw
  have e1 : (Vehicle.boot w).as = w.as := rfl
  have e2 : (Vehicle.boot w).ps = w.ps := rfl
  have h08 : (0 : ℝ) ≤ (0.8 : Float32).toReal := by rw [toReal_lit_0_8]; norm_num
  have hKA : 0 ≤ KA (Vehicle.boot w) := by
    rw [KA, P.kimax_ad]; exact h08.trans (le_max_left _ _)
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [P.kimax_rr]; exact kok_half
  · rw [P.kimax_rp]; exact kok_half
  · rw [P.kimax_ry]; exact kok_half
  · rw [P.kimax_rr, e1, has, init_rr]; exact ib_zero (by simp)
  · rw [P.kimax_rp, e1, has, init_rp]; exact ib_zero (by simp)
  · rw [P.kimax_ry, e1, has, init_ry]; exact ib_zero (by simp)
  · rw [P.kimax_ad]; exact kok_0_8
  · exact le_max_left _ _
  · rw [P.kimax_vd]; exact kok_ten
  · rw [e2, hps, init_ad]; exact ⟨Float32.isFinite_lit_zero, by simpa using hKA⟩
  · rw [P.kimax_vd, e2, hps, init_vd]; exact ib_zero (by rw [toReal_lit_ten]; norm_num)

end Contracts.Track.Induction
