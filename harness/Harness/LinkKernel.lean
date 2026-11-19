import Harness.LinkCheck

/-! # The range checker's comparisons are decided by the kernel

The atoms below are those `harness link ap_ctl` reads off two of `ap_ctl`'s obligations (the
bits are the contracts' binary32 literals as the compiled declarations hold them; the kernel
cannot compute them itself, since `Float32.ofScientific` is opaque). `decide` runs the checker's
code on them in the kernel: the bound comparison is exact integer arithmetic on the bit
patterns (values scaled by 2^149), with no float operation and no `native_decide`.

* `rate_c.roll_signals_bounded`, `|target_x| ≤ 1e4 ∧ |gyro_x| ≤ 1e4`: after the first tick
  from `attitude.targets_bounded` (`|target_x| ≤ 10000`, the tick before) and
  `assume.gyro_bounded` (`|gyro_x| ≤ 35`); at the first tick `target_x` is the `prev` wire's
  initial value 0.
* `position.ac_lean_range`: at the first tick from the attitude stage's `withInit` values
  (0.17453292 and 0.5235988), afterwards from `attitude.lean_limits` the tick before. -/

namespace Harness.Link

-- 1e4 = 0x461c4000 = 1176256512, 35 = 0x420c0000 = 1108082688
example : proveAtom [⟨.cout 4 0 1, .f32, .absle, 1176256512⟩, ⟨.cin 0 0, .f32, .absle, 1108082688⟩]
    ⟨.cout 4 0 1, .f32, .absle, 1176256512⟩ = true := by decide
example : proveAtom [⟨.cout 4 0 1, .f32, .absle, 1176256512⟩, ⟨.cin 0 0, .f32, .absle, 1108082688⟩]
    ⟨.cin 0 0, .f32, .absle, 1176256512⟩ = true := by decide
example : constHolds ⟨.const 0, .f32, .absle, 1176256512⟩ = true := by decide

-- 0.17453292 = 1043511490, 0.5235988 = 1057360530, 1.3962634 = 1068677314, 1.5707964 = 1070141403
example : constHolds ⟨.const 1043511490, .f32, .ge, 1043511490⟩ = true := by decide
example : constHolds ⟨.const 1043511490, .f32, .le, 1070141403⟩ = true := by decide
example : constHolds ⟨.const 1057360530, .f32, .ge, 1043511490⟩ = true := by decide
example : constHolds ⟨.const 1057360530, .f32, .le, 1068677314⟩ = true := by decide

-- the checker refuses what does not follow: |x| ≤ 1e4 does not give |x| ≤ 35
example : proveAtom [⟨.cin 0 0, .f32, .absle, 1176256512⟩]
    ⟨.cin 0 0, .f32, .absle, 1108082688⟩ = false := by decide
-- nor a bound on another signal
example : proveAtom [⟨.cin 3 0, .f32, .absle, 1108082688⟩]
    ⟨.cin 0 0, .f32, .absle, 1176256512⟩ = false := by decide

end Harness.Link
