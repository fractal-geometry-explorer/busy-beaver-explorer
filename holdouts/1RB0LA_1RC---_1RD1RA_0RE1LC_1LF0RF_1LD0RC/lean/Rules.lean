import Machine

/-!
# 1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC: shift rules


Each theorem is written by `tools/py/bbtools/symtm.py` (`prove`) from a symbolic run and holds for every count
and every tape `L`, `R` beyond the cells shown.
-/

namespace H76289

open TM

/-- Moving right, C rewrites each word `0 0 1 1` as `1 0 0 0`. -/
theorem cconv (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨L, rep (n) [false, false, true, true] (R), .C⟩ = some ⟨rep (n) [false, false, false, true] (L), R, .C⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, false, true, true] R, .C⟩ = some ⟨app [] (app [false, false, false, true] L), R, .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨L, rep (n) [false, false, true, true] (R), .C⟩ = some ⟨rep (n) [false, false, false, true] (L), R, .C⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

/-- Moving right, A fills each `0 0 1` into `1 1 1`. -/
theorem afill (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨L, rep (n) [false, false, true] (R), .A⟩ = some ⟨rep (n) [true, true, true] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 3 ⟨app [] L, app [false, false, true] R, .A⟩ = some ⟨app [] (app [true, true, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨L, rep (n) [false, false, true] (R), .A⟩ = some ⟨rep (n) [true, true, true] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 3) (by omega) (h0)

/-- Moving left, A erases a block of 1s. -/
theorem aerase (n : Nat) (L R : Tape) :
    steps (n) ⟨rep (n) [true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [false] (R)), .A⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [false] R), .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨rep (n) [true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [false] (R)), .A⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)

/-- F crosses 0s to the right, three steps a cell. -/
theorem fzero (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨cons false (L), rep (n) [false] (R), .F⟩ = some ⟨cons false (rep (n) [false] (L)), R, .F⟩ := by
  have c0 : ∀ L R : Tape, steps 3 ⟨app [false] L, app [false] R, .F⟩ = some ⟨app [false] (app [false] L), R, .F⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨cons false (L), rep (n) [false] (R), .F⟩ = some ⟨cons false (rep (n) [false] (L)), R, .F⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 3) (by omega) (h0)

end H76289
