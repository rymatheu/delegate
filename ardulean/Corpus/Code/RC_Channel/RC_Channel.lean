import ArduLean.Vehicle
import Corpus.Machine.Int

/-!
# RC_Channel: `RC_Channel.cpp`, `RC_Channels.cpp`, ArduCopter's `RC_Channel_Copter.h`

Channel lookup (null beyond 16 channels; the `nonnull` variant never null), the first-read table, the names of the
switch positions.
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.dupNamespace false

namespace Corpus.RC_Channel

/-! ## Channels (`RC_Channel_Copter.h`, `RC_Channels.cpp`) -/

theorem RC_Channels_Copter.channel_eq (this : UInt64) (chan : UInt8) :
    Vehicle_lib.RC_Channels_Copter.channel this chan = pure (Vehicle_lib.RC_Channels_Copter.channel.pure' this chan) :=
  rfl

/-- Case: a channel index from 16 on gives the null pointer (`RC_Channel_Copter.h:39-44`, 16 channels of 56 bytes). -/
theorem RC_Channels_Copter.channel_of_ge (this : UInt64) {chan : UInt8} (h : 16 ≤ chan.toNat) :
    Id.run (Vehicle_lib.RC_Channels_Copter.channel.pure' this chan) = 0 := by
  have k : 16 ≤ (UInt8.toUInt64 chan).toNat := by simpa using h
  unfold Vehicle_lib.RC_Channels_Copter.channel.pure'
  simp only [Id.run]
  rw [if_pos (by simp only [decide_eq_true_eq, ge_iff_le, UInt64.le_iff_toNat_le]; exact k)]; rfl

/-- Meaning: below 16, the channel object `this + 48 + 56·chan` (modulo `2^64`). -/
theorem RC_Channels_Copter.channel_toNat (this : UInt64) {chan : UInt8} (h : chan.toNat < 16) :
    (Id.run (Vehicle_lib.RC_Channels_Copter.channel.pure' this chan)).toNat =
      (this.toNat + 48 + 56 * chan.toNat) % 2 ^ 64 := by
  have k : ¬ 16 ≤ (UInt8.toUInt64 chan).toNat := by simp; omega
  have m : ∀ c : UInt8, ((c.toUInt64.toInt64 * 56).toUInt64).toNat = 56 * c.toNat := by decide +kernel
  unfold Vehicle_lib.RC_Channels_Copter.channel.pure'
  simp only [Id.run]
  rw [if_neg (by simp only [decide_eq_true_eq, ge_iff_le, UInt64.le_iff_toNat_le]; exact k)]
  show ((this + 48) + ((chan.toUInt64.toInt64 * 56).toUInt64)).toNat = _
  rw [UInt64.toNat_add, UInt64.toNat_add, m]; simp <;> omega

theorem RC_Channels.get_rcmap_channel_nonnull_eq (this : UInt64) (n : UInt8) :
    Vehicle_lib.RC_Channels.get_rcmap_channel_nonnull this n =
      pure (Vehicle_lib.RC_Channels.get_rcmap_channel_nonnull.pure' this n) := rfl

/-- Safety: never the null pointer: the mapped channel, or the dummy channel (`RC_Channels.cpp:394-401`). -/
theorem RC_Channels.get_rcmap_channel_nonnull_ne_zero (this : UInt64) (n : UInt8) :
    Id.run (Vehicle_lib.RC_Channels.get_rcmap_channel_nonnull.pure' this n) ≠ 0 := by
  unfold Vehicle_lib.RC_Channels.get_rcmap_channel_nonnull.pure'
  simp only [Id.run, bind, pure]
  split
  · next h => simpa using h
  · decide

/-- Case: when the mapped channel exists, it is the result. -/
theorem RC_Channels.get_rcmap_channel_nonnull_of_ne (this : UInt64) (n : UInt8)
    (h : Id.run (Vehicle_lib.RC_Channels_Copter.channel.pure' this (Int8.toUInt8 (Int32.toInt8
      (UInt32.toInt32 (UInt8.toUInt32 n) - 1)))) ≠ 0) :
    Id.run (Vehicle_lib.RC_Channels.get_rcmap_channel_nonnull.pure' this n) =
      Id.run (Vehicle_lib.RC_Channels_Copter.channel.pure' this (Int8.toUInt8 (Int32.toInt8
        (UInt32.toInt32 (UInt8.toUInt32 n) - 1)))) := by
  unfold Vehicle_lib.RC_Channels.get_rcmap_channel_nonnull.pure'
  simp only [Id.run, bind, pure]
  rw [if_pos (by simp only [bne_iff_ne, ne_eq]; exact h)]

theorem RC_Channels.get_rcmap_channel_nonnull'2_eq (this : UInt64) (n : UInt8) :
    Vehicle_lib.RC_Channels.get_rcmap_channel_nonnull'2 this n =
      pure (Vehicle_lib.RC_Channels.get_rcmap_channel_nonnull'2.pure' this n) := rfl

/-- Safety: the `const` overload is never null either (`RC_Channels.cpp:386-393`). -/
theorem RC_Channels.get_rcmap_channel_nonnull'2_ne_zero (this : UInt64) (n : UInt8) :
    Id.run (Vehicle_lib.RC_Channels.get_rcmap_channel_nonnull'2.pure' this n) ≠ 0 := by
  unfold Vehicle_lib.RC_Channels.get_rcmap_channel_nonnull'2.pure'
  simp only [Id.run, bind, pure]
  split
  · next h => simpa using h
  · decide

/-- Order: the two overloads agree. -/
theorem RC_Channels.get_rcmap_channel_nonnull'2_pure_eq (this : UInt64) (n : UInt8) :
    Id.run (Vehicle_lib.RC_Channels.get_rcmap_channel_nonnull'2.pure' this n) =
      Id.run (Vehicle_lib.RC_Channels.get_rcmap_channel_nonnull.pure' this n) := rfl

/-! ## Auxiliary switches (`RC_Channel.cpp`) -/

theorem RC_Channel.init_position_on_first_radio_read_eq (this : UInt64) (f : Int32) :
    Vehicle_lib.RC_Channel.init_position_on_first_radio_read this f =
      pure (Vehicle_lib.RC_Channel.init_position_on_first_radio_read.pure' this f) := rfl

/-- Protocol: the auxiliary functions whose position is taken on the first radio read (`RC_Channel.cpp:1051-1068`). -/
theorem RC_Channel.init_position_on_first_radio_read_table (this : UInt64) (f : Int32) :
    Id.run (Vehicle_lib.RC_Channel.init_position_on_first_radio_read.pure' this f) = true ↔
      f.toInt ∈ ([154, 153, 165] : List Int) := by
  unfold Vehicle_lib.RC_Channel.init_position_on_first_radio_read.pure'; table_tac

theorem RC_Channel.string_for_aux_pos_eq (this : UInt64) (pos : UInt8) :
    Vehicle_lib.RC_Channel.string_for_aux_pos this pos = pure (Vehicle_lib.RC_Channel.string_for_aux_pos.pure' this pos) :=
  rfl

/-- Protocol: the name of a switch position, as the address of its string (`RC_Channel.cpp:979-990`): `"HIGH"` for 2,
`"MIDDLE"` for 1, `"LOW"` for 0, `""` otherwise. -/
theorem RC_Channel.string_for_aux_pos_table (this : UInt64) (pos : UInt8) :
    Id.run (Vehicle_lib.RC_Channel.string_for_aux_pos.pure' this pos) =
      if pos = 2 then 0x18e42 else if pos = 1 then 0x18e47 else if pos = 0 then 0x18e4e else 0x14223 := by
  revert pos; unfold Vehicle_lib.RC_Channel.string_for_aux_pos.pure'; decide +kernel

end Corpus.RC_Channel
