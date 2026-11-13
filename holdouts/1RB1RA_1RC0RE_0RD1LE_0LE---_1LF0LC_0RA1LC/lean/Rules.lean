import Machine

/-! # Crossing rules of 1RB1RA_1RC0RE_0RD1LE_0LE---_1LF0LC_0RA1LC

The left part of the tape is made of the six-cell word 010111 in its rotations. Moving right, A crosses any number of copies at once and turns each into a word with five 1s (the extra 1 is the trace of the crossing); B does the same on 101110.

Written by `bbtools.symtm.prove` (the trace of a symbolic run, checked by the kernel). -/

namespace H23160

open TM

/-- A crosses copies of `010111`, leaving `101111`. -/
theorem a_cross_p (n : Nat) (L R : Tape) :
    steps (8 * n) ⟨L, rep (n) [false, true, false, true, true, true] (R), .A⟩ = some ⟨rep (n) [true, true, true, true, false, true] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 8 ⟨app [] L, app [false, true, false, true, true, true] R, .A⟩ = some ⟨app [] (app [true, true, true, true, false, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 8) ⟨L, rep (n) [false, true, false, true, true, true] (R), .A⟩ = some ⟨rep (n) [true, true, true, true, false, true] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 8) (by omega) (h0)


/-- A crosses copies of `101011`, leaving `110111`. -/
theorem a_cross_q (n : Nat) (L R : Tape) :
    steps (8 * n) ⟨L, rep (n) [true, false, true, false, true, true] (R), .A⟩ = some ⟨rep (n) [true, true, true, false, true, true] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 8 ⟨app [] L, app [true, false, true, false, true, true] R, .A⟩ = some ⟨app [] (app [true, true, true, false, true, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 8) ⟨L, rep (n) [true, false, true, false, true, true] (R), .A⟩ = some ⟨rep (n) [true, true, true, false, true, true] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 8) (by omega) (h0)


/-- A crosses copies of `110101`, leaving `111011`. -/
theorem a_cross_r (n : Nat) (L R : Tape) :
    steps (8 * n) ⟨L, rep (n) [true, true, false, true, false, true] (R), .A⟩ = some ⟨rep (n) [true, true, false, true, true, true] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 8 ⟨app [] L, app [true, true, false, true, false, true] R, .A⟩ = some ⟨app [] (app [true, true, false, true, true, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 8) ⟨L, rep (n) [true, true, false, true, false, true] (R), .A⟩ = some ⟨rep (n) [true, true, false, true, true, true] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 8) (by omega) (h0)


/-- A crosses copies of `111010`, leaving `111101`. -/
theorem a_cross_s (n : Nat) (L R : Tape) :
    steps (8 * n) ⟨L, rep (n) [true, true, true, false, true, false] (R), .A⟩ = some ⟨rep (n) [true, false, true, true, true, true] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 8 ⟨app [] L, app [true, true, true, false, true, false] R, .A⟩ = some ⟨app [] (app [true, false, true, true, true, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 8) ⟨L, rep (n) [true, true, true, false, true, false] (R), .A⟩ = some ⟨rep (n) [true, false, true, true, true, true] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 8) (by omega) (h0)


/-- B crosses copies of `101110`, leaving `011111`. -/
theorem b_cross (n : Nat) (L R : Tape) :
    steps (8 * n) ⟨L, rep (n) [true, false, true, true, true, false] (R), .B⟩ = some ⟨rep (n) [true, true, true, true, true, false] (L), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 8 ⟨app [] L, app [true, false, true, true, true, false] R, .B⟩ = some ⟨app [] (app [true, true, true, true, true, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 8) ⟨L, rep (n) [true, false, true, true, true, false] (R), .B⟩ = some ⟨rep (n) [true, true, true, true, true, false] (L), R, .B⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 8) (by omega) (h0)


end H23160
