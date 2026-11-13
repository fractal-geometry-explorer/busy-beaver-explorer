import Machine

/-!
# 1RB0LE_1RC1RA_1RD0RF_1RE0RA_1LA1LD_1RA---: shift rules


Each theorem is written by `tools/py/bbtools/symtm.py` (`prove`) from a symbolic run and holds for every count
and every tape `L`, `R` beyond the cells shown.
-/

namespace H10690

open TM

/-- Moving right, A turns each `0 0 1 0 0 1` into the block `1 1 0 1 1 1`, twelve steps a block. -/
theorem aword (n : Nat) (L R : Tape) :
    steps (6 * n) ⟨L, rep (n) [false, false, true, false, false, true] (R), .A⟩ = some ⟨rep (n) [true, true, true, false, true, true] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 6 ⟨app [] L, app [false, false, true, false, false, true] R, .A⟩ = some ⟨app [] (app [true, true, true, false, true, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 6) ⟨L, rep (n) [false, false, true, false, false, true] (R), .A⟩ = some ⟨rep (n) [true, true, true, false, true, true] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 6) (by omega) (h0)

/-- Moving right, C turns each `1 0 0 1 0 0` into `0 1 1 1 1 1`. -/
theorem cword (n : Nat) (L R : Tape) :
    steps (6 * n) ⟨L, rep (n) [true, false, false, true, false, false] (R), .C⟩ = some ⟨rep (n) [true, true, true, true, true, false] (L), R, .C⟩ := by
  have c0 : ∀ L R : Tape, steps 6 ⟨app [] L, app [true, false, false, true, false, false] R, .C⟩ = some ⟨app [] (app [true, true, true, true, true, false] L), R, .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 6) ⟨L, rep (n) [true, false, false, true, false, false] (R), .C⟩ = some ⟨rep (n) [true, true, true, true, true, false] (L), R, .C⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 6) (by omega) (h0)

/-- Moving right, B turns each `1 0 0 1 0 0` into `1 1 1 0 1 1`. -/
theorem bword (n : Nat) (L R : Tape) :
    steps (6 * n) ⟨L, rep (n) [true, false, false, true, false, false] (R), .B⟩ = some ⟨rep (n) [true, true, false, true, true, true] (L), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 6 ⟨app [] L, app [true, false, false, true, false, false] R, .B⟩ = some ⟨app [] (app [true, true, false, true, true, true] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 6) ⟨L, rep (n) [true, false, false, true, false, false] (R), .B⟩ = some ⟨rep (n) [true, true, false, true, true, true] (L), R, .B⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 6) (by omega) (h0)

/-- Moving right, A fills `0 1` pairs into `1 1`. -/
theorem afill (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨L, rep (n) [false, true] (R), .A⟩ = some ⟨rep (n) [true, true] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [true, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨L, rep (n) [false, true] (R), .A⟩ = some ⟨rep (n) [true, true] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- Moving right, B fills `1 0` pairs into `1 1`. -/
theorem bfill (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨L, rep (n) [true, false] (R), .B⟩ = some ⟨rep (n) [true, true] (L), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .B⟩ = some ⟨app [] (app [true, true] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨L, rep (n) [true, false] (R), .B⟩ = some ⟨rep (n) [true, true] (L), R, .B⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- E crosses `0 1` pairs to the left. -/
theorem eleft (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [true, false] (L), cons false (R), .E⟩ = some ⟨L, cons false (rep (n) [false, true] (R)), .E⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .E⟩ = some ⟨L, app [false] (app [false, true] R), .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [true, false] (L), cons false (R), .E⟩ = some ⟨L, cons false (rep (n) [false, true] (R)), .E⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- A crosses `1 0` pairs to the left. -/
theorem aleft (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [false, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [true, false] (R)), .A⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [false, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [true, false] (R)), .A⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- Moving right, F turns each `0 0 1 0 0 1` into `1 1 1 1 1 0`. -/
theorem fword (n : Nat) (L R : Tape) :
    steps (6 * n) ⟨L, rep (n) [false, false, true, false, false, true] (R), .F⟩ = some ⟨rep (n) [false, true, true, true, true, true] (L), R, .F⟩ := by
  have c0 : ∀ L R : Tape, steps 6 ⟨app [] L, app [false, false, true, false, false, true] R, .F⟩ = some ⟨app [] (app [false, true, true, true, true, true] L), R, .F⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 6) ⟨L, rep (n) [false, false, true, false, false, true] (R), .F⟩ = some ⟨rep (n) [false, true, true, true, true, true] (L), R, .F⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 6) (by omega) (h0)

end H10690
