import Machine

/-! # 1RB0LC_1RC1RA_1RD0RF_0LE---_1LA1LE_0RA1LD: proved rules

Shift rules (the head crossing a run of copies of a word in one go) found in the run and proved for every count and every tape around them by `tools/py/bbtools/symtm.py` (the folder's `py/rules.py` rewrites this file). -/

namespace H126068

open TM

/-- Shift rule: in state A the head crosses n copies of 100 leftward, 5 steps per copy, leaving 110 behind (the word 1 next to the head travels along). -/
theorem shift_l_A_100 (n : Nat) (L R : Tape) :
    steps (5 * n) ⟨rep (n) [false, false, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [true, true, false] (R)), .A⟩ := by
  have c0 : ∀ L R : Tape, steps 5 ⟨app [false, false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, true, false] R), .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 5) ⟨rep (n) [false, false, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [true, true, false] (R)), .A⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 5) (by omega) (h0)

/-- Shift rule: in state A the head crosses n copies of 01 rightward, 2 steps per copy, leaving 11 behind. -/
theorem shift_r_A_01 (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨L, rep (n) [false, true] (R), .A⟩ = some ⟨rep (n) [true, true] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [true, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨L, rep (n) [false, true] (R), .A⟩ = some ⟨rep (n) [true, true] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

end H126068
