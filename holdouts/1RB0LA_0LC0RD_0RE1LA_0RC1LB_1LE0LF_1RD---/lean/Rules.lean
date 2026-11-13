import Machine

/-! # 1RB0LA_0LC0RD_0RE1LA_0RC1LB_1LE0LF_1RD---: proved rules

Shift rules (the head crossing a run of copies of a word in one go) found in the run and proved for every count and every tape around them by `tools/py/bbtools/symtm.py` (the folder's `py/rules.py` rewrites this file). -/

namespace H110152

open TM

/-- Shift rule: in state C the head crosses n copies of 10 rightward, 4 steps per copy, leaving 10 behind (the word 0 next to the head travels along). -/
theorem shift_r_C_10 (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨cons false (L), rep (n) [true, false] (R), .C⟩ = some ⟨cons false (rep (n) [false, true] (L)), R, .C⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [false] L, app [true, false] R, .C⟩ = some ⟨app [false] (app [false, true] L), R, .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨cons false (L), rep (n) [true, false] (R), .C⟩ = some ⟨cons false (rep (n) [false, true] (L)), R, .C⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

/-- Shift rule: in state A the head crosses n copies of 10 leftward, 4 steps per copy, leaving 10 behind (the word 1 next to the head travels along). -/
theorem shift_l_A_10 (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨rep (n) [false, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [true, false] (R)), .A⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨rep (n) [false, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [true, false] (R)), .A⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

/-- Shift rule: in state A the head crosses n copies of 01 leftward, 4 steps per copy, leaving 10 behind (the word 00 next to the head travels along). -/
theorem shift_l_A_01 (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨rep (n) [true, false] (L), cons false (cons false (R)), .A⟩ = some ⟨L, cons false (cons false (rep (n) [true, false] (R))), .A⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [true, false] L, app [false, false] R, .A⟩ = some ⟨L, app [false, false] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨rep (n) [true, false] (L), cons false (cons false (R)), .A⟩ = some ⟨L, cons false (cons false (rep (n) [true, false] (R))), .A⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

/-- Shift rule: in state C the head crosses n copies of 01 leftward, 4 steps per copy, leaving 01 behind (the word 1 next to the head travels along). -/
theorem shift_l_C_01 (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨rep (n) [true, false] (L), cons true (R), .C⟩ = some ⟨L, cons true (rep (n) [false, true] (R)), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [true, false] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [false, true] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨rep (n) [true, false] (L), cons true (R), .C⟩ = some ⟨L, cons true (rep (n) [false, true] (R)), .C⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

end H110152
