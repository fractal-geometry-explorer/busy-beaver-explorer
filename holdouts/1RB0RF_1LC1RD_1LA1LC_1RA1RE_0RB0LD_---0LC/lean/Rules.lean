import Machine

/-! # 1RB0RF_1LC1RD_1LA1LC_1RA1RE_0RB0LD_---0LC: proved rules

Shift rules (the head crossing a run of copies of a word in one go) found in the run and proved for every count and every tape around them by `tools/py/bbtools/symtm.py` (the folder's `py/rules.py` rewrites this file). -/

namespace H73584

open TM

/-- Shift rule: in state C the head crosses n copies of 1 leftward, 3 steps per copy, leaving 0 behind (the word 0 next to the head travels along). -/
theorem shift_l_C_1 (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨rep (n) [true] (L), cons false (R), .C⟩ = some ⟨L, cons false (rep (n) [false] (R)), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 3 ⟨app [true] L, app [false] R, .C⟩ = some ⟨L, app [false] (app [false] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨rep (n) [true] (L), cons false (R), .C⟩ = some ⟨L, cons false (rep (n) [false] (R)), .C⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 3) (by omega) (h0)

end H73584
