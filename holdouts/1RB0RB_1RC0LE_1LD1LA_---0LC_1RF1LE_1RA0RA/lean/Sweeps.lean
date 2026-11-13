import Machine

/-! Shift rules of 1RB0RB_1RC0LE_1LD1LA_---0LC_1RF1LE_1RA0RA, found and proved by `tools/py/bbtools/symtm.py` (driven by the README's sweep search): a state crossing n copies of a word of the background in one sweep, for every n and every tape around. They are the building blocks of the sweeps described in the README; they do not by themselves decide halting. -/

namespace H25221

open TM

/-- D moving left across n copies of 10 (reading 1) leaves n copies of 10 (2 steps each). -/
theorem sweep_lD_10_1 (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [false, true] (L), cons true (R), .D⟩ = some ⟨L, cons true (rep (n) [true, false] (R)), .D⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .D⟩ = some ⟨L, app [true] (app [true, false] R), .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [false, true] (L), cons true (R), .D⟩ = some ⟨L, cons true (rep (n) [true, false] (R)), .D⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- C moving left across n copies of 01 (reading 0) leaves n copies of 01 (2 steps each). -/
theorem sweep_lC_01_0 (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [true, false] (L), cons false (R), .C⟩ = some ⟨L, cons false (rep (n) [false, true] (R)), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .C⟩ = some ⟨L, app [false] (app [false, true] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [true, false] (L), cons false (R), .C⟩ = some ⟨L, cons false (rep (n) [false, true] (R)), .C⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

end H25221
