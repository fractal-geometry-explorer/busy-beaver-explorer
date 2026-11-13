import Machine

/-! Shift rules of 1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD---, found and proved by `tools/py/bbtools/symtm.py` (driven by the README's sweep search): a state crossing n copies of a word of the background in one sweep, for every n and every tape around. They are the building blocks of the sweeps described in the README; they do not by themselves decide halting. -/

namespace H178401

open TM

/-- A moving right across n copies of 110101010 leaves n copies of 001111111 (11 steps each). -/
theorem sweep_rA_110101010 (n : Nat) (L R : Tape) :
    steps (11 * n) ⟨L, rep (n) [true, true, false, true, false, true, false, true, false] (R), .A⟩ = some ⟨rep (n) [true, true, true, true, true, true, true, false, false] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 11 ⟨app [] L, app [true, true, false, true, false, true, false, true, false] R, .A⟩ = some ⟨app [] (app [true, true, true, true, true, true, true, false, false] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 11) ⟨L, rep (n) [true, true, false, true, false, true, false, true, false] (R), .A⟩ = some ⟨rep (n) [true, true, true, true, true, true, true, false, false] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 11) (by omega) (h0)

/-- B moving right across n copies of 110101010 leaves n copies of 101001111 (33 steps each). -/
theorem sweep_rB_110101010 (n : Nat) (L R : Tape) :
    steps (33 * n) ⟨L, rep (n) [true, true, false, true, false, true, false, true, false] (R), .B⟩ = some ⟨rep (n) [true, true, true, true, false, false, true, false, true] (L), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 33 ⟨app [] L, app [true, true, false, true, false, true, false, true, false] R, .B⟩ = some ⟨app [] (app [true, true, true, true, false, false, true, false, true] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 33) ⟨L, rep (n) [true, true, false, true, false, true, false, true, false] (R), .B⟩ = some ⟨rep (n) [true, true, true, true, false, false, true, false, true] (L), R, .B⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 33) (by omega) (h0)

/-- C moving left across n copies of 110101010 (reading 1) leaves n copies of 110111011 (9 steps each). -/
theorem sweep_lC_110101010_1 (n : Nat) (L R : Tape) :
    steps (9 * n) ⟨rep (n) [false, true, false, true, false, true, false, true, true] (L), cons true (R), .C⟩ = some ⟨L, cons true (rep (n) [true, true, false, true, true, true, false, true, true] (R)), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 9 ⟨app [false, true, false, true, false, true, false, true, true] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [true, true, false, true, true, true, false, true, true] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 9) ⟨rep (n) [false, true, false, true, false, true, false, true, true] (L), cons true (R), .C⟩ = some ⟨L, cons true (rep (n) [true, true, false, true, true, true, false, true, true] (R)), .C⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 9) (by omega) (h0)

/-- A moving right across n copies of 101010110 leaves n copies of 111111001 (11 steps each). -/
theorem sweep_rA_101010110 (n : Nat) (L R : Tape) :
    steps (11 * n) ⟨L, rep (n) [true, false, true, false, true, false, true, true, false] (R), .A⟩ = some ⟨rep (n) [true, false, false, true, true, true, true, true, true] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 11 ⟨app [] L, app [true, false, true, false, true, false, true, true, false] R, .A⟩ = some ⟨app [] (app [true, false, false, true, true, true, true, true, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 11) ⟨L, rep (n) [true, false, true, false, true, false, true, true, false] (R), .A⟩ = some ⟨rep (n) [true, false, false, true, true, true, true, true, true] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 11) (by omega) (h0)

/-- D moving left across n copies of 101010110 (reading 1) leaves n copies of 111011110 (9 steps each). -/
theorem sweep_lD_101010110_1 (n : Nat) (L R : Tape) :
    steps (9 * n) ⟨rep (n) [false, true, true, false, true, false, true, false, true] (L), cons true (R), .D⟩ = some ⟨L, cons true (rep (n) [true, true, true, false, true, true, true, true, false] (R)), .D⟩ := by
  have c0 : ∀ L R : Tape, steps 9 ⟨app [false, true, true, false, true, false, true, false, true] L, app [true] R, .D⟩ = some ⟨L, app [true] (app [true, true, true, false, true, true, true, true, false] R), .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 9) ⟨rep (n) [false, true, true, false, true, false, true, false, true] (L), cons true (R), .D⟩ = some ⟨L, cons true (rep (n) [true, true, true, false, true, true, true, true, false] (R)), .D⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 9) (by omega) (h0)

/-- A moving right across n copies of 011010101 leaves n copies of 110100111 (33 steps each). -/
theorem sweep_rA_011010101 (n : Nat) (L R : Tape) :
    steps (33 * n) ⟨L, rep (n) [false, true, true, false, true, false, true, false, true] (R), .A⟩ = some ⟨rep (n) [true, true, true, false, false, true, false, true, true] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 33 ⟨app [] L, app [false, true, true, false, true, false, true, false, true] R, .A⟩ = some ⟨app [] (app [true, true, true, false, false, true, false, true, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 33) ⟨L, rep (n) [false, true, true, false, true, false, true, false, true] (R), .A⟩ = some ⟨rep (n) [true, true, true, false, false, true, false, true, true] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 33) (by omega) (h0)

/-- C moving left across n copies of 011010101 (reading 0) leaves n copies of 111011101 (9 steps each). -/
theorem sweep_lC_011010101_0 (n : Nat) (L R : Tape) :
    steps (9 * n) ⟨rep (n) [true, false, true, false, true, false, true, true, false] (L), cons false (R), .C⟩ = some ⟨L, cons false (rep (n) [true, true, true, false, true, true, true, false, true] (R)), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 9 ⟨app [true, false, true, false, true, false, true, true, false] L, app [false] R, .C⟩ = some ⟨L, app [false] (app [true, true, true, false, true, true, true, false, true] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 9) ⟨rep (n) [true, false, true, false, true, false, true, true, false] (L), cons false (R), .C⟩ = some ⟨L, cons false (rep (n) [true, true, true, false, true, true, true, false, true] (R)), .C⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 9) (by omega) (h0)

/-- D moving right across n copies of 011010101 leaves n copies of 100111111 (11 steps each). -/
theorem sweep_rD_011010101 (n : Nat) (L R : Tape) :
    steps (11 * n) ⟨L, rep (n) [false, true, true, false, true, false, true, false, true] (R), .D⟩ = some ⟨rep (n) [true, true, true, true, true, true, false, false, true] (L), R, .D⟩ := by
  have c0 : ∀ L R : Tape, steps 11 ⟨app [] L, app [false, true, true, false, true, false, true, false, true] R, .D⟩ = some ⟨app [] (app [true, true, true, true, true, true, false, false, true] L), R, .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 11) ⟨L, rep (n) [false, true, true, false, true, false, true, false, true] (R), .D⟩ = some ⟨rep (n) [true, true, true, true, true, true, false, false, true] (L), R, .D⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 11) (by omega) (h0)

end H178401
