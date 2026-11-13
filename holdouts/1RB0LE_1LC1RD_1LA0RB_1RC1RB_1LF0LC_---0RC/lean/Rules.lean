import Machine

/-!
# 1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC: shift rules


Each theorem is written by `tools/py/bbtools/symtm.py` (`prove`) from a symbolic run and holds for every count
and every tape `L`, `R` beyond the cells shown.
-/

namespace H101395

open TM

/-- Moving right, B rewrites each copy of the word `1101101101` as `1011110110`, twelve steps a word. -/
theorem bword (n : Nat) (L R : Tape) :
    steps (12 * n) ⟨L, rep (n) [true, true, false, true, true, false, true, true, false, true] (R), .B⟩ = some ⟨rep (n) [false, true, true, false, true, true, true, true, false, true] (L), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 12 ⟨app [] L, app [true, true, false, true, true, false, true, true, false, true] R, .B⟩ = some ⟨app [] (app [false, true, true, false, true, true, true, true, false, true] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 12) ⟨L, rep (n) [true, true, false, true, true, false, true, true, false, true] (R), .B⟩ = some ⟨rep (n) [false, true, true, false, true, true, true, true, false, true] (L), R, .B⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 12) (by omega) (h0)

/-- Moving left, C turns each copy of `0101111011` (a rotation of the word B leaves behind) back into `0110110111` (a rotation of `1101101101`), 58 steps a word. -/
theorem cback (n : Nat) (L R : Tape) :
    steps (58 * n) ⟨rep (n) [true, true, false, true, true, true, true, false, true, false] (L), cons false (cons false (R)), .C⟩ = some ⟨L, cons false (cons false (rep (n) [false, true, true, false, true, true, false, true, true, true] (R))), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 58 ⟨app [true, true, false, true, true, true, true, false, true, false] L, app [false, false] R, .C⟩ = some ⟨L, app [false, false] (app [false, true, true, false, true, true, false, true, true, true] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 58) ⟨rep (n) [true, true, false, true, true, true, true, false, true, false] (L), cons false (cons false (R)), .C⟩ = some ⟨L, cons false (cons false (rep (n) [false, true, true, false, true, true, false, true, true, true] (R))), .C⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 58) (by omega) (h0)

/-- B crosses pairs of 1s to the right. -/
theorem bright (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨L, rep (n) [true, true] (R), .B⟩ = some ⟨rep (n) [true, true] (L), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .B⟩ = some ⟨app [] (app [true, true] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨L, rep (n) [true, true] (R), .B⟩ = some ⟨rep (n) [true, true] (L), R, .B⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- Moving right, D swaps each pair `1 0` into `0 1`. -/
theorem dright (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨L, rep (n) [true, false] (R), .D⟩ = some ⟨rep (n) [true, false] (L), R, .D⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [] L, app [true, false] R, .D⟩ = some ⟨app [] (app [true, false] L), R, .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨L, rep (n) [true, false] (R), .D⟩ = some ⟨rep (n) [true, false] (L), R, .D⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

/-- Moving left, C turns each word `0 1 1` into `0 0 1`. -/
theorem cleft (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨rep (n) [true, true, false] (L), cons false (R), .C⟩ = some ⟨L, cons false (rep (n) [false, false, true] (R)), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 3 ⟨app [true, true, false] L, app [false] R, .C⟩ = some ⟨L, app [false] (app [false, false, true] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨rep (n) [true, true, false] (L), cons false (R), .C⟩ = some ⟨L, cons false (rep (n) [false, false, true] (R)), .C⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 3) (by omega) (h0)

/-- Moving left, A turns each word `1 0 1` into `1 0 0`. -/
theorem aleft (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨rep (n) [true, false, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [true, false, false] (R)), .A⟩ := by
  have c0 : ∀ L R : Tape, steps 3 ⟨app [true, false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false, false] R), .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨rep (n) [true, false, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [true, false, false] (R)), .A⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 3) (by omega) (h0)

end H101395
