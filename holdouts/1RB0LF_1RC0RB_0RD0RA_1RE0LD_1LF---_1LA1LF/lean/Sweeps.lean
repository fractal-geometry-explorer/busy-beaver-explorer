import Machine

/-! Shift rules of 1RB0LF_1RC0RB_0RD0RA_1RE0LD_1LF---_1LA1LF, found and proved by `tools/py/bbtools/symtm.py` (driven by the README's sweep search): a state crossing n copies of a word of the background in one sweep, for every n and every tape around. They are the building blocks of the sweeps described in the README; they do not by themselves decide halting. -/

namespace H51276

open TM

/-- A moving left across n copies of 10 (reading 1) leaves n copies of 10 (2 steps each). -/
theorem sweep_lA_10_1 (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [false, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [true, false] (R)), .A⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false] R), .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [false, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [true, false] (R)), .A⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- F moving left across n copies of 01 (reading 0) leaves n copies of 01 (2 steps each). -/
theorem sweep_lF_01_0 (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨rep (n) [true, false] (L), cons false (R), .F⟩ = some ⟨L, cons false (rep (n) [false, true] (R)), .F⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [true, false] L, app [false] R, .F⟩ = some ⟨L, app [false] (app [false, true] R), .F⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨rep (n) [true, false] (L), cons false (R), .F⟩ = some ⟨L, cons false (rep (n) [false, true] (R)), .F⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- A moving left across n copies of 1010 (reading 1) leaves n copies of 1010 (4 steps each). -/
theorem sweep_lA_1010_1 (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨rep (n) [false, true, false, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [true, false, true, false] (R)), .A⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [false, true, false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false, true, false] R), .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨rep (n) [false, true, false, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [true, false, true, false] (R)), .A⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

/-- B moving right across n copies of 1010 leaves n copies of 0101 (4 steps each). -/
theorem sweep_rB_1010 (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨L, rep (n) [true, false, true, false] (R), .B⟩ = some ⟨rep (n) [true, false, true, false] (L), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [] L, app [true, false, true, false] R, .B⟩ = some ⟨app [] (app [true, false, true, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨L, rep (n) [true, false, true, false] (R), .B⟩ = some ⟨rep (n) [true, false, true, false] (L), R, .B⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

/-- C moving right across n copies of 1010 leaves n copies of 0101 (4 steps each). -/
theorem sweep_rC_1010 (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨L, rep (n) [true, false, true, false] (R), .C⟩ = some ⟨rep (n) [true, false, true, false] (L), R, .C⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [] L, app [true, false, true, false] R, .C⟩ = some ⟨app [] (app [true, false, true, false] L), R, .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨L, rep (n) [true, false, true, false] (R), .C⟩ = some ⟨rep (n) [true, false, true, false] (L), R, .C⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

/-- A moving right across n copies of 0101 leaves n copies of 1010 (4 steps each). -/
theorem sweep_rA_0101 (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨L, rep (n) [false, true, false, true] (R), .A⟩ = some ⟨rep (n) [false, true, false, true] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true, false, true] R, .A⟩ = some ⟨app [] (app [false, true, false, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨L, rep (n) [false, true, false, true] (R), .A⟩ = some ⟨rep (n) [false, true, false, true] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

/-- B moving right across n copies of 0101 leaves n copies of 1010 (4 steps each). -/
theorem sweep_rB_0101 (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨L, rep (n) [false, true, false, true] (R), .B⟩ = some ⟨rep (n) [false, true, false, true] (L), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true, false, true] R, .B⟩ = some ⟨app [] (app [false, true, false, true] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨L, rep (n) [false, true, false, true] (R), .B⟩ = some ⟨rep (n) [false, true, false, true] (L), R, .B⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

/-- F moving left across n copies of 0101 (reading 0) leaves n copies of 0101 (4 steps each). -/
theorem sweep_lF_0101_0 (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨rep (n) [true, false, true, false] (L), cons false (R), .F⟩ = some ⟨L, cons false (rep (n) [false, true, false, true] (R)), .F⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [true, false, true, false] L, app [false] R, .F⟩ = some ⟨L, app [false] (app [false, true, false, true] R), .F⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨rep (n) [true, false, true, false] (L), cons false (R), .F⟩ = some ⟨L, cons false (rep (n) [false, true, false, true] (R)), .F⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

end H51276
