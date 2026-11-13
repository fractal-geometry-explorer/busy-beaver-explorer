import Macro

/-!
# The third epoch survives

The third epoch has a wall of 227,097 ones; at its end `K = (seq 227097).1`, a number of 132,845 bits, is odd, so
the machine does not halt there and starts a fourth epoch, whose wall `epochs 3` has 39,991 decimal digits.  Checked
with `native_decide` (227,097 big-number steps of `g`).
-/

namespace H155226

theorem epoch3_odd : (seq 227097).1 % 2 = 1 := by native_decide

theorem epoch3_survives : (epochs 3).isSome = true := by native_decide

/-- If the machine halts from blank tape, it does so at the end of the fourth epoch or later. -/
theorem halts_late (h : HaltsFromBlank) : ∃ i A, 3 ≤ i ∧ epochs i = some A ∧ (seq A).1 % 2 = 0 := by
  obtain ⟨i, A, h1, h2⟩ := halts_iff.1 h
  refine ⟨i, A, ?_, h1, h2⟩
  have e1 : epochs 1 = some 25 := epochs_small.1
  have e2 : epochs 2 = some 227097 := epochs_small.2
  have s0 : (seq 3).1 % 2 = 1 := by decide
  have s1 : (seq 25).1 % 2 = 1 := by decide
  match i, h1 with
  | 0, h1 => cases h1; rw [s0] at h2; cases h2
  | 1, h1 => rw [e1] at h1; cases h1; rw [s1] at h2; cases h2
  | 2, h1 => rw [e2] at h1; cases h1; rw [epoch3_odd] at h2; cases h2
  | i + 3, _ => omega

end H155226
