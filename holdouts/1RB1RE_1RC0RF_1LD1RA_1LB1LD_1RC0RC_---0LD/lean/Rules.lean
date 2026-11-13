import Machine

/-! # 1RB1RE_1RC0RF_1LD1RA_1LB1LD_1RC0RC_---0LD: proved rules

Shift rules (the head crossing a run of copies of a word in one go) found in the run and proved for every count and every tape around them by `tools/py/bbtools/symtm.py` (the folder's `py/rules.py` rewrites this file). -/

namespace H167030

open TM

/-- Shift rule: in state D the head crosses n copies of 1 leftward, 3 steps per copy, leaving 0 behind (the word 0 next to the head travels along). -/
theorem shift_l_D_1 (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨rep (n) [true] (L), cons false (R), .D⟩ = some ⟨L, cons false (rep (n) [false] (R)), .D⟩ := by
  have c0 : ∀ L R : Tape, steps 3 ⟨app [true] L, app [false] R, .D⟩ = some ⟨L, app [false] (app [false] R), .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨rep (n) [true] (L), cons false (R), .D⟩ = some ⟨L, cons false (rep (n) [false] (R)), .D⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 3) (by omega) (h0)

/-- Shift rule: in state B the head crosses n copies of 1 leftward, 3 steps per copy, leaving 0 behind (the word 11 next to the head travels along). -/
theorem shift_l_B_1 (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨rep (n) [true] (L), cons true (cons true (R)), .B⟩ = some ⟨L, cons true (cons true (rep (n) [false] (R))), .B⟩ := by
  have c0 : ∀ L R : Tape, steps 3 ⟨app [true] L, app [true, true] R, .B⟩ = some ⟨L, app [true, true] (app [false] R), .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨rep (n) [true] (L), cons true (cons true (R)), .B⟩ = some ⟨L, cons true (cons true (rep (n) [false] (R))), .B⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 3) (by omega) (h0)

end H167030
