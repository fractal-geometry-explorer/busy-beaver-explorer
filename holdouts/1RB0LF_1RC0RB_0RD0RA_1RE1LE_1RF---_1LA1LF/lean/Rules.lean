import Machine

/-! # 1RB0LF_1RC0RB_0RD0RA_1RE1LE_1RF---_1LA1LF: proved rules

Shift rules (the head crossing a run of copies of a word in one go) found in the run and proved for every count and every tape around them by `tools/py/bbtools/symtm.py` (the folder's `py/rules.py` rewrites this file). -/

namespace H129932

open TM

/-- Shift rule: in state A the head crosses n copies of 10 leftward, 2 steps per copy, leaving 10 behind (the word 1 next to the head travels along). -/
theorem shift_l_A_10 (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [false, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [true, false] (R)), .A⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [false, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [true, false] (R)), .A⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- Shift rule: in state F the head crosses n copies of 01 leftward, 2 steps per copy, leaving 01 behind (the word 0 next to the head travels along). -/
theorem shift_l_F_01 (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [true, false] (L), cons false (R), .F⟩ = some ⟨L, cons false (rep (n) [false, true] (R)), .F⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .F⟩ = some ⟨L, app [false] (app [false, true] R), .F⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [true, false] (L), cons false (R), .F⟩ = some ⟨L, cons false (rep (n) [false, true] (R)), .F⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

end H129932
