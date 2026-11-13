import Machine

/-! # 1RB1RD_1LC0RE_1LD1LC_1RA0LE_1LC0RF_0RD---: proved rules

Shift rules (the head crossing a run of copies of a word in one go) found in the run and proved for every count and every tape around them by `tools/py/bbtools/symtm.py` (the folder's `py/rules.py` rewrites this file). -/

namespace H139727

open TM

/-- Shift rule: in state D the head crosses n copies of 01 rightward, 2 steps per copy, leaving 11 behind. -/
theorem shift_r_D_01 (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨L, rep (n) [false, true] (R), .D⟩ = some ⟨rep (n) [true, true] (L), R, .D⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .D⟩ = some ⟨app [] (app [true, true] L), R, .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨L, rep (n) [false, true] (R), .D⟩ = some ⟨rep (n) [true, true] (L), R, .D⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- Shift rule: in state C the head crosses n copies of 1 leftward, 1 steps per copy, leaving 1 behind (the word 1 next to the head travels along). -/
theorem shift_l_C_1 (n : Nat) (L R : Tape) :
    steps (n) ⟨rep (n) [true] (L), cons true (R), .C⟩ = some ⟨L, cons true (rep (n) [true] (R)), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [true] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [true] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨rep (n) [true] (L), cons true (R), .C⟩ = some ⟨L, cons true (rep (n) [true] (R)), .C⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)

end H139727
