import Machine

/-! # 1RB0RA_1RC0RF_0RD1LE_0LE---_1LF1LE_1RA0LC: proved rules

Shift rules (the head crossing a run of copies of a word in one go) found in the run and proved for every count and every tape around them by `tools/py/bbtools/symtm.py` (the folder's `py/rules.py` rewrites this file). -/

namespace H28668

open TM

/-- Shift rule: in state F the head crosses n copies of 10 leftward, 4 steps per copy, leaving 10 behind (the word 1 next to the head travels along). -/
theorem shift_l_F_10 (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨rep (n) [false, true] (L), cons true (R), .F⟩ = some ⟨L, cons true (rep (n) [true, false] (R)), .F⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [false, true] L, app [true] R, .F⟩ = some ⟨L, app [true] (app [true, false] R), .F⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨rep (n) [false, true] (L), cons true (R), .F⟩ = some ⟨L, cons true (rep (n) [true, false] (R)), .F⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

/-- Shift rule: in state E the head crosses n copies of 01 leftward, 4 steps per copy, leaving 01 behind (the word 0 next to the head travels along). -/
theorem shift_l_E_01 (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨rep (n) [true, false] (L), cons false (R), .E⟩ = some ⟨L, cons false (rep (n) [false, true] (R)), .E⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [true, false] L, app [false] R, .E⟩ = some ⟨L, app [false] (app [false, true] R), .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨rep (n) [true, false] (L), cons false (R), .E⟩ = some ⟨L, cons false (rep (n) [false, true] (R)), .E⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

/-- Shift rule: in state C the head crosses n copies of 01 leftward, 4 steps per copy, leaving 10 behind (the word 00 next to the head travels along). -/
theorem shift_l_C_01 (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨rep (n) [true, false] (L), cons false (cons false (R)), .C⟩ = some ⟨L, cons false (cons false (rep (n) [true, false] (R))), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [true, false] L, app [false, false] R, .C⟩ = some ⟨L, app [false, false] (app [true, false] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨rep (n) [true, false] (L), cons false (cons false (R)), .C⟩ = some ⟨L, cons false (cons false (rep (n) [true, false] (R))), .C⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

end H28668
