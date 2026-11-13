import Machine

/-!
# 1RB0LD_0RC1RA_1LD1RC_1LE0RF_---1LA_1LF0LA: shift rules


Each theorem is written by `tools/py/bbtools/symtm.py` (`prove`) from a symbolic run and holds for every count
and every tape `L`, `R` beyond the cells shown.
-/

namespace H137602

open TM

set_option maxRecDepth 20000 in
/-- Moving left, D rewrites each copy of the 51-cell word (in this rotation) into the code seen at the left end, 201 steps a word. -/
theorem dword (n : Nat) (L R : Tape) :
    steps (201 * n) ⟨rep (n) [true, true, false, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, false, true, true, true, false] (L), cons false (cons false (cons false (R))), .D⟩ = some ⟨L, cons false (cons false (cons false (rep (n) [true, true, false, true, true, true, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, true, true, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, false, false, true, true, true, true, false, true, true, false, true, true, true] (R)))), .D⟩ := by
  have c0 : ∀ L R : Tape, steps 201 ⟨app [true, true, false, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, false, true, true, true, false] L, app [false, false, false] R, .D⟩ = some ⟨L, app [false, false, false] (app [true, true, false, true, true, true, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, true, true, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, false, false, true, true, true, true, false, true, true, false, true, true, true] R), .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 201) ⟨rep (n) [true, true, false, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, false, true, true, true, false] (L), cons false (cons false (cons false (R))), .D⟩ = some ⟨L, cons false (cons false (cons false (rep (n) [true, true, false, true, true, true, false, true, true, false, true, true, true, true, true, true, true, true, true, false, false, true, true, false, true, true, true, true, false, true, true, false, false, true, true, true, true, true, false, false, true, true, true, true, false, true, true, false, true, true, true] (R)))), .D⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 201) (by omega) (h0)

/-- Moving left, F turns 0s into 1s. -/
theorem ffill (n : Nat) (L R : Tape) :
    steps (n) ⟨rep (n) [false] (L), cons false (R), .F⟩ = some ⟨L, cons false (rep (n) [true] (R)), .F⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [false] L, app [false] R, .F⟩ = some ⟨L, app [false] (app [true] R), .F⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨rep (n) [false] (L), cons false (R), .F⟩ = some ⟨L, cons false (rep (n) [true] (R)), .F⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)

/-- C crosses 1s to the right. -/
theorem cright (n : Nat) (L R : Tape) :
    steps (n) ⟨L, rep (n) [true] (R), .C⟩ = some ⟨rep (n) [true] (L), R, .C⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .C⟩ = some ⟨app [] (app [true] L), R, .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨L, rep (n) [true] (R), .C⟩ = some ⟨rep (n) [true] (L), R, .C⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)

/-- C crosses `1 0` pairs to the right, six steps a pair (through D, F, A, B). -/
theorem cright10 (n : Nat) (L R : Tape) :
    steps (6 * n) ⟨L, rep (n) [true, false] (R), .C⟩ = some ⟨rep (n) [false, true] (L), R, .C⟩ := by
  have c0 : ∀ L R : Tape, steps 6 ⟨app [] L, app [true, false] R, .C⟩ = some ⟨app [] (app [false, true] L), R, .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 6) ⟨L, rep (n) [true, false] (R), .C⟩ = some ⟨rep (n) [false, true] (L), R, .C⟩ :=
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

end H137602
