import Machine

/-! # Shift rules of 1RB0LA_1RC---_1RD1RA_1LE1RF_1LC1LE_0RC0RD

Proved from symbolic traces by `bbtools.symtm.prove` (written by `py/leanfiles.py`); each holds for every value of the counts and every tape in the contexts. -/

namespace H44966

open TM

/-- A crosses n+1 copies of `001` (rightwards): `A> (001)^n+1` becomes `(111)^n+1 A>`. -/
theorem a_right_001 (n : Nat) (L R : Tape) :
    steps (3 * n + 3) ⟨L, rep (n + 1) [false, false, true] (R), .A⟩ = some ⟨rep (n + 1) [true, true, true] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 3 ⟨app [] L, app [false, false, true] R, .A⟩ = some ⟨app [] (app [true, true, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n + 1) * 3) ⟨L, rep (n + 1) [false, false, true] (R), .A⟩ = some ⟨rep (n + 1) [true, true, true] (L), R, .A⟩ :=
    cross_r trans c0 (n + 1) (L) (R)
  exact steps_congr trans (a := (n + 1) * 3) (by omega) (h0)

/-- B crosses n+1 copies of `001` (rightwards): `B> (001)^n+1` becomes `1 1 1 (011)^n F>`. -/
theorem b_right_001 (n : Nat) (L R : Tape) :
    steps (3 * n + 3) ⟨L, rep (n + 1) [false, false, true] (R), .B⟩ = some ⟨rep (n) [true, true, false] (cons true (cons true (cons true (L)))), R, .F⟩ := by
  have h0 : steps 3 ⟨L, rep (n + 1) [false, false, true] (R), .B⟩ = some ⟨cons true (cons true (cons true (L))), rep (n) [false, false, true] (R), .F⟩ := rfl
  have c1 : ∀ L R : Tape, steps 3 ⟨app [] L, app [false, false, true] R, .F⟩ = some ⟨app [] (app [true, true, false] L), R, .F⟩ := fun _ _ => rfl
  have h1 : steps ((n) * 3) ⟨cons true (cons true (cons true (L))), rep (n) [false, false, true] (R), .F⟩ = some ⟨rep (n) [true, true, false] (cons true (cons true (cons true (L)))), R, .F⟩ :=
    cross_r trans c1 (n) (cons true (cons true (cons true (L)))) (R)
  exact steps_congr trans (a := 3 + ((n) * 3)) (by omega) (steps_seq trans h0 (h1))

/-- C crosses n+1 copies of `100` (rightwards): `C> (100)^n+1` becomes `(111)^n+1 C>`. -/
theorem c_right_100 (n : Nat) (L R : Tape) :
    steps (3 * n + 3) ⟨L, rep (n + 1) [true, false, false] (R), .C⟩ = some ⟨rep (n + 1) [true, true, true] (L), R, .C⟩ := by
  have c0 : ∀ L R : Tape, steps 3 ⟨app [] L, app [true, false, false] R, .C⟩ = some ⟨app [] (app [true, true, true] L), R, .C⟩ := fun _ _ => rfl
  have h0 : steps ((n + 1) * 3) ⟨L, rep (n + 1) [true, false, false] (R), .C⟩ = some ⟨rep (n + 1) [true, true, true] (L), R, .C⟩ :=
    cross_r trans c0 (n + 1) (L) (R)
  exact steps_congr trans (a := (n + 1) * 3) (by omega) (h0)

/-- D crosses n+1 copies of `11` (rightwards): `D> (11)^n+1` becomes `(10)^n+1 D>`. -/
theorem d_right_11 (n : Nat) (L R : Tape) :
    steps (2 * n + 2) ⟨L, rep (n + 1) [true, true] (R), .D⟩ = some ⟨rep (n + 1) [false, true] (L), R, .D⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .D⟩ = some ⟨app [] (app [false, true] L), R, .D⟩ := fun _ _ => rfl
  have h0 : steps ((n + 1) * 2) ⟨L, rep (n + 1) [true, true] (R), .D⟩ = some ⟨rep (n + 1) [false, true] (L), R, .D⟩ :=
    cross_r trans c0 (n + 1) (L) (R)
  exact steps_congr trans (a := (n + 1) * 2) (by omega) (h0)

/-- D crosses n+1 copies of `100` (rightwards): `D> (100)^n+1` becomes `(101)^n+1 D>`. -/
theorem d_right_100 (n : Nat) (L R : Tape) :
    steps (3 * n + 3) ⟨L, rep (n + 1) [true, false, false] (R), .D⟩ = some ⟨rep (n + 1) [true, false, true] (L), R, .D⟩ := by
  have c0 : ∀ L R : Tape, steps 3 ⟨app [] L, app [true, false, false] R, .D⟩ = some ⟨app [] (app [true, false, true] L), R, .D⟩ := fun _ _ => rfl
  have h0 : steps ((n + 1) * 3) ⟨L, rep (n + 1) [true, false, false] (R), .D⟩ = some ⟨rep (n + 1) [true, false, true] (L), R, .D⟩ :=
    cross_r trans c0 (n + 1) (L) (R)
  exact steps_congr trans (a := (n + 1) * 3) (by omega) (h0)

/-- F crosses n+1 copies of `11` (rightwards): `F> (11)^n+1` becomes `(01)^n+1 F>`. -/
theorem f_right_11 (n : Nat) (L R : Tape) :
    steps (2 * n + 2) ⟨L, rep (n + 1) [true, true] (R), .F⟩ = some ⟨rep (n + 1) [true, false] (L), R, .F⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, true] R, .F⟩ = some ⟨app [] (app [true, false] L), R, .F⟩ := fun _ _ => rfl
  have h0 : steps ((n + 1) * 2) ⟨L, rep (n + 1) [true, true] (R), .F⟩ = some ⟨rep (n + 1) [true, false] (L), R, .F⟩ :=
    cross_r trans c0 (n + 1) (L) (R)
  exact steps_congr trans (a := (n + 1) * 2) (by omega) (h0)

/-- F crosses n+1 copies of `001` (rightwards): `F> (001)^n+1` becomes `(011)^n+1 F>`. -/
theorem f_right_001 (n : Nat) (L R : Tape) :
    steps (3 * n + 3) ⟨L, rep (n + 1) [false, false, true] (R), .F⟩ = some ⟨rep (n + 1) [true, true, false] (L), R, .F⟩ := by
  have c0 : ∀ L R : Tape, steps 3 ⟨app [] L, app [false, false, true] R, .F⟩ = some ⟨app [] (app [true, true, false] L), R, .F⟩ := fun _ _ => rfl
  have h0 : steps ((n + 1) * 3) ⟨L, rep (n + 1) [false, false, true] (R), .F⟩ = some ⟨rep (n + 1) [true, true, false] (L), R, .F⟩ :=
    cross_r trans c0 (n + 1) (L) (R)
  exact steps_congr trans (a := (n + 1) * 3) (by omega) (h0)

end H44966
