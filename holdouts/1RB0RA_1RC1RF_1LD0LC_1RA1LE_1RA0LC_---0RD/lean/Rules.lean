import Machine

/-! # Crossing rules of 1RB0RA_1RC1RF_1LD0LC_1RA1LE_1RA0LC_---0RD

Right of a short control word, the tape is the four-cell word 1101 in its rotations. Moving right, A, F and B cross whole runs of it, each shifting it by one cell.

Written by `bbtools.symtm.prove` (the trace of a symbolic run, checked by the kernel). -/

namespace H125786

open TM

/-- A crosses copies of `0111`, leaving `1110`. -/
theorem a_cross (n : Nat) (L R : Tape) :
    steps (6 * n) ⟨L, rep (n) [false, true, true, true] (R), .A⟩ = some ⟨rep (n) [false, true, true, true] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 6 ⟨app [] L, app [false, true, true, true] R, .A⟩ = some ⟨app [] (app [false, true, true, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 6) ⟨L, rep (n) [false, true, true, true] (R), .A⟩ = some ⟨rep (n) [false, true, true, true] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 6) (by omega) (h0)


/-- F crosses copies of `1101`, leaving `1011`. -/
theorem f_cross (n : Nat) (L R : Tape) :
    steps (6 * n) ⟨L, rep (n) [true, true, false, true] (R), .F⟩ = some ⟨rep (n) [true, true, false, true] (L), R, .F⟩ := by
  have c0 : ∀ L R : Tape, steps 6 ⟨app [] L, app [true, true, false, true] R, .F⟩ = some ⟨app [] (app [true, true, false, true] L), R, .F⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 6) ⟨L, rep (n) [true, true, false, true] (R), .F⟩ = some ⟨rep (n) [true, true, false, true] (L), R, .F⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 6) (by omega) (h0)


/-- B crosses copies of `1110`, leaving `1101`. -/
theorem b_cross (n : Nat) (L R : Tape) :
    steps (6 * n) ⟨L, rep (n) [true, true, true, false] (R), .B⟩ = some ⟨rep (n) [true, false, true, true] (L), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 6 ⟨app [] L, app [true, true, true, false] R, .B⟩ = some ⟨app [] (app [true, false, true, true] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 6) ⟨L, rep (n) [true, true, true, false] (R), .B⟩ = some ⟨rep (n) [true, false, true, true] (L), R, .B⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 6) (by omega) (h0)


end H125786
