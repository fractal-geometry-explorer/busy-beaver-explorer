import Machine

/-! # Shift rules of 1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---

Proved from symbolic traces by `bbtools.symtm.prove` (written by `py/leanfiles.py`); each holds for every value of the counts and every tape in the contexts. -/

namespace H66280

open TM

/-- A crosses n+1 copies of `01` (rightwards): `A> (01)^n+1` becomes `1 (01)^n 0 E>`. -/
theorem a_right_01 (n : Nat) (L R : Tape) :
    steps (4 * n + 2) ⟨L, rep (n + 1) [false, true] (R), .A⟩ = some ⟨cons false (rep (n) [true, false] (cons true (L))), R, .E⟩ := by
  have h0 : steps 2 ⟨L, rep (n + 1) [false, true] (R), .A⟩ = some ⟨cons false (cons true (L)), rep (n) [false, true] (R), .E⟩ := rfl
  have c1 : ∀ L R : Tape, steps 4 ⟨app [false] L, app [false, true] R, .E⟩ = some ⟨app [false] (app [true, false] L), R, .E⟩ := fun _ _ => rfl
  have h1 : steps ((n) * 4) ⟨cons false (cons true (L)), rep (n) [false, true] (R), .E⟩ = some ⟨cons false (rep (n) [true, false] (cons true (L))), R, .E⟩ :=
    cross_r trans c1 (n) (cons true (L)) (R)
  exact steps_congr trans (a := 2 + ((n) * 4)) (by omega) (steps_seq trans h0 (h1))

/-- A crosses n+1 copies of `011` (rightwards): `A> (011)^n+1` becomes `(100)^n+1 A>`. -/
theorem a_right_011 (n : Nat) (L R : Tape) :
    steps (3 * n + 3) ⟨L, rep (n + 1) [false, true, true] (R), .A⟩ = some ⟨rep (n + 1) [false, false, true] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 3 ⟨app [] L, app [false, true, true] R, .A⟩ = some ⟨app [] (app [false, false, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n + 1) * 3) ⟨L, rep (n + 1) [false, true, true] (R), .A⟩ = some ⟨rep (n + 1) [false, false, true] (L), R, .A⟩ :=
    cross_r trans c0 (n + 1) (L) (R)
  exact steps_congr trans (a := (n + 1) * 3) (by omega) (h0)

/-- B crosses n+1 copies of `10` (rightwards): `B> (10)^n+1` becomes `(01)^n+1 B>`. -/
theorem b_right_10 (n : Nat) (L R : Tape) :
    steps (4 * n + 4) ⟨L, rep (n + 1) [true, false] (R), .B⟩ = some ⟨rep (n + 1) [true, false] (L), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [] L, app [true, false] R, .B⟩ = some ⟨app [] (app [true, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n + 1) * 4) ⟨L, rep (n + 1) [true, false] (R), .B⟩ = some ⟨rep (n + 1) [true, false] (L), R, .B⟩ :=
    cross_r trans c0 (n + 1) (L) (R)
  exact steps_congr trans (a := (n + 1) * 4) (by omega) (h0)

/-- B crosses n+1 copies of `110` (rightwards): `B> (110)^n+1` becomes `(001)^n+1 B>`. -/
theorem b_right_110 (n : Nat) (L R : Tape) :
    steps (3 * n + 3) ⟨L, rep (n + 1) [true, true, false] (R), .B⟩ = some ⟨rep (n + 1) [true, false, false] (L), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 3 ⟨app [] L, app [true, true, false] R, .B⟩ = some ⟨app [] (app [true, false, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n + 1) * 3) ⟨L, rep (n + 1) [true, true, false] (R), .B⟩ = some ⟨rep (n + 1) [true, false, false] (L), R, .B⟩ :=
    cross_r trans c0 (n + 1) (L) (R)
  exact steps_congr trans (a := (n + 1) * 3) (by omega) (h0)

/-- E crosses n+1 copies of `10` (rightwards): `E> (10)^n+1` becomes `0 1 (01)^n B>`. -/
theorem e_right_10 (n : Nat) (L R : Tape) :
    steps (4 * n + 2) ⟨L, rep (n + 1) [true, false] (R), .E⟩ = some ⟨rep (n) [true, false] (cons true (cons false (L))), R, .B⟩ := by
  have h0 : steps 2 ⟨L, rep (n + 1) [true, false] (R), .E⟩ = some ⟨cons true (cons false (L)), rep (n) [true, false] (R), .B⟩ := rfl
  have c1 : ∀ L R : Tape, steps 4 ⟨app [] L, app [true, false] R, .B⟩ = some ⟨app [] (app [true, false] L), R, .B⟩ := fun _ _ => rfl
  have h1 : steps ((n) * 4) ⟨cons true (cons false (L)), rep (n) [true, false] (R), .B⟩ = some ⟨rep (n) [true, false] (cons true (cons false (L))), R, .B⟩ :=
    cross_r trans c1 (n) (cons true (cons false (L))) (R)
  exact steps_congr trans (a := 2 + ((n) * 4)) (by omega) (steps_seq trans h0 (h1))

end H66280
