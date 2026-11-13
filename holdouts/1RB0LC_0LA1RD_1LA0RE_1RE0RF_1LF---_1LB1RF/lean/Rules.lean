import Machine

/-!
# 1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LF---_1LB1RF: shift rules


Each theorem is written by `tools/py/bbtools/symtm.py` (`prove`) from a symbolic run and holds for every count
and every tape `L`, `R` beyond the cells shown.
-/

namespace H31128

open TM

/-- F crosses 1s to the right. -/
theorem fright (n : Nat) (L R : Tape) :
    steps (n) ⟨L, rep (n) [true] (R), .F⟩ = some ⟨rep (n) [true] (L), R, .F⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .F⟩ = some ⟨app [] (app [true] L), R, .F⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨L, rep (n) [true] (R), .F⟩ = some ⟨rep (n) [true] (L), R, .F⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)

/-- F crosses `1 0` pairs to the right, four steps a pair. -/
theorem fright10 (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨L, rep (n) [true, false] (R), .F⟩ = some ⟨rep (n) [false, true] (L), R, .F⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [] L, app [true, false] R, .F⟩ = some ⟨app [] (app [false, true] L), R, .F⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨L, rep (n) [true, false] (R), .F⟩ = some ⟨rep (n) [false, true] (L), R, .F⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

/-- Moving left, A shifts the pairs `1 0` one cell (two steps a pair). -/
theorem aleft (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [false, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [true, false] (R)), .A⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [false, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [true, false] (R)), .A⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- Moving left, C shifts the pairs `0 1` one cell. -/
theorem cleft (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [true, false] (L), cons false (R), .C⟩ = some ⟨L, cons false (rep (n) [false, true] (R)), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .C⟩ = some ⟨L, app [false] (app [false, true] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [true, false] (L), cons false (R), .C⟩ = some ⟨L, cons false (rep (n) [false, true] (R)), .C⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- Moving left, B shifts the words `0 1 1` one cell. -/
theorem bleft (n : Nat) (L R : Tape) :
    steps (5 * n) ⟨rep (n) [true, true, false] (L), cons false (R), .B⟩ = some ⟨L, cons false (rep (n) [true, true, false] (R)), .B⟩ := by
  have c0 : ∀ L R : Tape, steps 5 ⟨app [true, true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [true, true, false] R), .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 5) ⟨rep (n) [true, true, false] (L), cons false (R), .B⟩ = some ⟨L, cons false (rep (n) [true, true, false] (R)), .B⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 5) (by omega) (h0)

end H31128
