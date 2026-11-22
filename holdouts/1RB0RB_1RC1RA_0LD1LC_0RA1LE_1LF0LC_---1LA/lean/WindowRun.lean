import Shield
import Window

/-!
# 1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA: no halt in the first 9.0e+40 steps, by windows of the cascade

`Window.lean` (machine-independent): the first `m` cells of the word, fed the block's three letters, are run once
per cell, twice when the cell's bit is not back (`wfold`); what leaves them covers `3 · 2^d` sweeps, `d` the number
of cells that needed two passes, and is then run through the rest of the word (`window_of_check`).  Unlike
`Shield.lean`, nothing is assumed about the block: the whole word is run.

* `window_runs` (compiled evaluation): at zone step 3 · 10^7, cut after 138 cells, the window has `d = 66` and
  nothing leaves the word: no halt and no reset for `3 · 2^66` more sweeps;
* `blank_runs_window`: with `corb_quiet_t` of `Shield.lean`, **no halt in the first 90000000000000000000000000000000000000000 steps from blank
  tape**.
-/

namespace H25821

open TM hiding rep run
open XS

/-- What compiled evaluation checks at zone step 3 · 10^7. -/
def wgood : Option (Nat × CS) → Bool
  | some (_, .rt n Z) => windowCheck n 138 66 Z
  | _ => false

theorem window_runs : wgood (H25821.crun 30000000 (3, .rt 0 [])) = true := by native_decide

/-- **No halt in the first 90000000000000000000000000000000000000000 steps from blank tape.** -/
theorem blank_runs_window : ∃ c, steps 90000000000000000000000000000000000000000 init = some c := by
  have hz := window_runs
  rw [← corb_eq_crun] at hz
  cases hc : corb 30000000 with
  | none => rw [hc] at hz; simp [wgood] at hz
  | some p =>
    obtain ⟨t, s⟩ := p
    cases s with
    | raw c => rw [hc] at hz; simp [wgood] at hz
    | rt n Z =>
      rw [hc] at hz
      have hw : windowCheck n 138 66 Z = true := hz
      have hq := window_of_check hw (3 * 2 ^ 66) (Nat.le_refl _)
      obtain ⟨t', ht', hle⟩ := corb_quiet_t hc _ hq
      have hs := (corb_sound _ _ _ ht').1
      have hbig : 90000000000000000000000000000000000000000 ≤ t' := by
        have e1 : 3 * 2 ^ 66 = 221360928884514619392 := rfl
        have e2 : 221360928884514619392 * 221360928884514619392 = 49000660836615138738725943470174622449664 := rfl
        rw [e1, e2] at hle
        omega
      rw [show t' = 90000000000000000000000000000000000000000 + (t' - 90000000000000000000000000000000000000000) by omega] at hs
      exact steps_le trans hs

end H25821
