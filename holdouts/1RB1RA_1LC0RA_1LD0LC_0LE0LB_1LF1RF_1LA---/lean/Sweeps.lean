import Machine

/-! Shift rules of 1RB1RA_1LC0RA_1LD0LC_0LE0LB_1LF1RF_1LA---, found and proved by `tools/py/bbtools/symtm.py` (driven by the README's sweep search): a state crossing n copies of a word of the background in one sweep, for every n and every tape around. They are the building blocks of the sweeps described in the README; they do not by themselves decide halting. -/

namespace H25733

open TM

/-- B moving right across n copies of 10 leaves n copies of 01 (2 steps each). -/
theorem sweep_rB_10 (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨L, rep (n) [true, false] (R), .B⟩ = some ⟨rep (n) [true, false] (L), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .B⟩ = some ⟨app [] (app [true, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨L, rep (n) [true, false] (R), .B⟩ = some ⟨rep (n) [true, false] (L), R, .B⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- A moving right across n copies of 01 leaves n copies of 10 (2 steps each). -/
theorem sweep_rA_01 (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨L, rep (n) [false, true] (R), .A⟩ = some ⟨rep (n) [false, true] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .A⟩ = some ⟨app [] (app [false, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨L, rep (n) [false, true] (R), .A⟩ = some ⟨rep (n) [false, true] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 2) (by omega) (h0)

/-- B moving right across n copies of 1010 leaves n copies of 0101 (4 steps each). -/
theorem sweep_rB_1010 (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨L, rep (n) [true, false, true, false] (R), .B⟩ = some ⟨rep (n) [true, false, true, false] (L), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [] L, app [true, false, true, false] R, .B⟩ = some ⟨app [] (app [true, false, true, false] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨L, rep (n) [true, false, true, false] (R), .B⟩ = some ⟨rep (n) [true, false, true, false] (L), R, .B⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

/-- C moving left across n copies of 1010 (reading 1) leaves n copies of 1010 (4 steps each). -/
theorem sweep_lC_1010_1 (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨rep (n) [false, true, false, true] (L), cons true (R), .C⟩ = some ⟨L, cons true (rep (n) [true, false, true, false] (R)), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [false, true, false, true] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [true, false, true, false] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨rep (n) [false, true, false, true] (L), cons true (R), .C⟩ = some ⟨L, cons true (rep (n) [true, false, true, false] (R)), .C⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

/-- D moving left across n copies of 1010 (reading 1) leaves n copies of 1010 (4 steps each). -/
theorem sweep_lD_1010_1 (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨rep (n) [false, true, false, true] (L), cons true (R), .D⟩ = some ⟨L, cons true (rep (n) [true, false, true, false] (R)), .D⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [false, true, false, true] L, app [true] R, .D⟩ = some ⟨L, app [true] (app [true, false, true, false] R), .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨rep (n) [false, true, false, true] (L), cons true (R), .D⟩ = some ⟨L, cons true (rep (n) [true, false, true, false] (R)), .D⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

/-- A moving right across n copies of 0101 leaves n copies of 1010 (4 steps each). -/
theorem sweep_rA_0101 (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨L, rep (n) [false, true, false, true] (R), .A⟩ = some ⟨rep (n) [false, true, false, true] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, true, false, true] R, .A⟩ = some ⟨app [] (app [false, true, false, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨L, rep (n) [false, true, false, true] (R), .A⟩ = some ⟨rep (n) [false, true, false, true] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

/-- B moving left across n copies of 0101 (reading 0) leaves n copies of 0101 (4 steps each). -/
theorem sweep_lB_0101_0 (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨rep (n) [true, false, true, false] (L), cons false (R), .B⟩ = some ⟨L, cons false (rep (n) [false, true, false, true] (R)), .B⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [true, false, true, false] L, app [false] R, .B⟩ = some ⟨L, app [false] (app [false, true, false, true] R), .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨rep (n) [true, false, true, false] (L), cons false (R), .B⟩ = some ⟨L, cons false (rep (n) [false, true, false, true] (R)), .B⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

/-- C moving left across n copies of 0101 (reading 0) leaves n copies of 0101 (4 steps each). -/
theorem sweep_lC_0101_0 (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨rep (n) [true, false, true, false] (L), cons false (R), .C⟩ = some ⟨L, cons false (rep (n) [false, true, false, true] (R)), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 4 ⟨app [true, false, true, false] L, app [false] R, .C⟩ = some ⟨L, app [false] (app [false, true, false, true] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨rep (n) [true, false, true, false] (L), cons false (R), .C⟩ = some ⟨L, cons false (rep (n) [false, true, false, true] (R)), .C⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 4) (by omega) (h0)

end H25733
