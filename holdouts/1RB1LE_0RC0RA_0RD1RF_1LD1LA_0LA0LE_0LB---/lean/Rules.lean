import Machine

/-! # 1RB1LE_0RC0RA_0RD1RF_1LD1LA_0LA0LE_0LB---: proved rules

Shift rules (the head crossing a run of copies of a word in one go) found in the run and proved for every count and every tape around them by `tools/py/bbtools/symtm.py` (the folder's `py/rules.py` rewrites this file). -/

namespace H103399

open TM

/-- Shift rule: in state A the head crosses n copies of 10 leftward, 2 steps per copy, leaving 01 behind (the word 1 next to the head travels along). -/
theorem shift_l_A_10 (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [false, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [false, true] (R)), .A⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [false, true] R), .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [false, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [false, true] (R)), .A⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- Shift rule: in state B the head crosses n copies of 10 rightward, 2 steps per copy, leaving 01 behind. -/
theorem shift_r_B_10 (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨L, rep (n) [true, false] (R), .B⟩ = some ⟨rep (n) [true, false] (L), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .B⟩ = some ⟨app [] (app [true, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨L, rep (n) [true, false] (R), .B⟩ = some ⟨rep (n) [true, false] (L), R, .B⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- Shift rule: in state E the head crosses n copies of 01 leftward, 2 steps per copy, leaving 10 behind (the word 0 next to the head travels along). -/
theorem shift_l_E_01 (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [true, false] (L), cons false (R), .E⟩ = some ⟨L, cons false (rep (n) [true, false] (R)), .E⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .E⟩ = some ⟨L, app [false] (app [true, false] R), .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [true, false] (L), cons false (R), .E⟩ = some ⟨L, cons false (rep (n) [true, false] (R)), .E⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

end H103399
