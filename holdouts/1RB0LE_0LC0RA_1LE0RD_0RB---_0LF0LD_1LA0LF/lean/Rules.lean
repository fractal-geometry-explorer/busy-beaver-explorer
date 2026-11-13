import Machine

/-! # Shift rules of 1RB0LE_0LC0RA_1LE0RD_0RB---_0LF0LD_1LA0LF

Proved from symbolic traces by `bbtools.symtm.prove` (written by `py/leanfiles.py`); each holds for every value of the counts and every tape in the contexts. -/

namespace H36869

open TM

/-- A crosses n+1 copies of `01` (rightwards): `A> (01)^n+1` becomes `(10)^n+1 A>`. -/
theorem a_right_01 (n : Nat) (L R : Tape) :
    steps (2 * n + 2) ⟨L, rep (n + 1) [false, true] (R), .A⟩ = some ⟨rep (n + 1) [false, true] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n + 1) * 2) ⟨L, rep (n + 1) [false, true] (R), .A⟩ = some ⟨rep (n + 1) [false, true] (L), R, .A⟩ :=
    cross_r trans c0 (n + 1) (L) (R)
  exact steps_congr trans (a := (n + 1) * 2) (by omega) (h0)

/-- A crosses n+1 copies of `001` (rightwards): `A> (001)^n+1` becomes `(000)^n+1 A>`. -/
theorem a_right_001 (n : Nat) (L R : Tape) :
    steps (5 * n + 5) ⟨L, rep (n + 1) [false, false, true] (R), .A⟩ = some ⟨rep (n + 1) [false, false, false] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 5 ⟨app [] L, app [false, false, true] R, .A⟩ = some ⟨app [] (app [false, false, false] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n + 1) * 5) ⟨L, rep (n + 1) [false, false, true] (R), .A⟩ = some ⟨rep (n + 1) [false, false, false] (L), R, .A⟩ :=
    cross_r trans c0 (n + 1) (L) (R)
  exact steps_congr trans (a := (n + 1) * 5) (by omega) (h0)

/-- B crosses n+1 copies of `10` (rightwards): `B> (10)^n+1` becomes `(01)^n+1 B>`. -/
theorem b_right_10 (n : Nat) (L R : Tape) :
    steps (2 * n + 2) ⟨L, rep (n + 1) [true, false] (R), .B⟩ = some ⟨rep (n + 1) [true, false] (L), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .B⟩ = some ⟨app [] (app [true, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n + 1) * 2) ⟨L, rep (n + 1) [true, false] (R), .B⟩ = some ⟨rep (n + 1) [true, false] (L), R, .B⟩ :=
    cross_r trans c0 (n + 1) (L) (R)
  exact steps_congr trans (a := (n + 1) * 2) (by omega) (h0)

/-- B crosses n+1 copies of `100` (rightwards): `B> (100)^n+1` becomes `(000)^n+1 B>`. -/
theorem b_right_100 (n : Nat) (L R : Tape) :
    steps (5 * n + 5) ⟨L, rep (n + 1) [true, false, false] (R), .B⟩ = some ⟨rep (n + 1) [false, false, false] (L), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 5 ⟨app [] L, app [true, false, false] R, .B⟩ = some ⟨app [] (app [false, false, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n + 1) * 5) ⟨L, rep (n + 1) [true, false, false] (R), .B⟩ = some ⟨rep (n + 1) [false, false, false] (L), R, .B⟩ :=
    cross_r trans c0 (n + 1) (L) (R)
  exact steps_congr trans (a := (n + 1) * 5) (by omega) (h0)

/-- C crosses n+1 copies of `10` (rightwards): `C> (10)^n+1` becomes `0 0 (01)^n B>`. -/
theorem c_right_10 (n : Nat) (L R : Tape) :
    steps (2 * n + 2) ⟨L, rep (n + 1) [true, false] (R), .C⟩ = some ⟨rep (n) [true, false] (cons false (cons false (L))), R, .B⟩ := by
  have h0 : steps 2 ⟨L, rep (n + 1) [true, false] (R), .C⟩ = some ⟨cons false (cons false (L)), rep (n) [true, false] (R), .B⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .B⟩ = some ⟨app [] (app [true, false] L), R, .B⟩ := fun _ _ => rfl
  have h1 : steps ((n) * 2) ⟨cons false (cons false (L)), rep (n) [true, false] (R), .B⟩ = some ⟨rep (n) [true, false] (cons false (cons false (L))), R, .B⟩ :=
    cross_r trans c1 (n) (cons false (cons false (L))) (R)
  exact steps_congr trans (a := 2 + ((n) * 2)) (by omega) (steps_seq trans h0 (h1))

/-- D crosses n+1 copies of `01` (rightwards): `D> (01)^n+1` becomes `0 0 (10)^n A>`. -/
theorem d_right_01 (n : Nat) (L R : Tape) :
    steps (2 * n + 2) ⟨L, rep (n + 1) [false, true] (R), .D⟩ = some ⟨rep (n) [false, true] (cons false (cons false (L))), R, .A⟩ := by
  have h0 : steps 2 ⟨L, rep (n + 1) [false, true] (R), .D⟩ = some ⟨cons false (cons false (L)), rep (n) [false, true] (R), .A⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h1 : steps ((n) * 2) ⟨cons false (cons false (L)), rep (n) [false, true] (R), .A⟩ = some ⟨rep (n) [false, true] (cons false (cons false (L))), R, .A⟩ :=
    cross_r trans c1 (n) (cons false (cons false (L))) (R)
  exact steps_congr trans (a := 2 + ((n) * 2)) (by omega) (steps_seq trans h0 (h1))

end H36869
