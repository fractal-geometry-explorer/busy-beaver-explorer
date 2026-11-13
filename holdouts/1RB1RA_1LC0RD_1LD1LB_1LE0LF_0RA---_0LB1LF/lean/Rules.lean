import Machine

/-! # 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB1LF: proved rules

Shift rules (the head crossing a run of copies of a word in one go) found in the run and proved for every count and every tape around them by `tools/py/bbtools/symtm.py` (the folder's `py/rules.py` rewrites this file). -/

namespace H99431

open TM

/-- Shift rule: in state B the head crosses n copies of 01 leftward, 2 steps per copy, leaving 11 behind (the word 0 next to the head travels along). -/
theorem shift_l_B_01 (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [true, false] (L), cons false (R), .B⟩ = some ⟨L, cons false (rep (n) [true, true] (R)), .B⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [true, true] R), .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [true, false] (L), cons false (R), .B⟩ = some ⟨L, cons false (rep (n) [true, true] (R)), .B⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- Shift rule: in state B the head crosses n copies of 011 leftward, 5 steps per copy, leaving 001 behind (the word 0 next to the head travels along). -/
theorem shift_l_B_011 (n : Nat) (L R : Tape) :
    steps (5 * n) ⟨rep (n) [true, true, false] (L), cons false (R), .B⟩ = some ⟨L, cons false (rep (n) [false, false, true] (R)), .B⟩ := by
  have c0 : ∀ L R : Tape, steps 5 ⟨app [true, true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [false, false, true] R), .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 5) ⟨rep (n) [true, true, false] (L), cons false (R), .B⟩ = some ⟨L, cons false (rep (n) [false, false, true] (R)), .B⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 5) (by omega) (h0)

end H99431
