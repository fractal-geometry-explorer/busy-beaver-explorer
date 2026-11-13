import Machine

/-! Shift rules of 1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF, found and proved by `tools/py/bbtools/symtm.py` (driven by the README's sweep search): a state crossing n copies of a word of the background in one sweep, for every n and every tape around. They are the building blocks of the sweeps described in the README; they do not by themselves decide halting. -/

namespace H50436

open TM

/-- A moving right across n copies of 110101010 leaves n copies of 001111111 (11 steps each). -/
theorem sweep_rA_110101010 (n : Nat) (L R : Tape) :
    steps (11 * n) ⟨L, rep (n) [true, true, false, true, false, true, false, true, false] (R), .A⟩ = some ⟨rep (n) [true, true, true, true, true, true, true, false, false] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 11 ⟨app [] L, app [true, true, false, true, false, true, false, true, false] R, .A⟩ = some ⟨app [] (app [true, true, true, true, true, true, true, false, false] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 11) ⟨L, rep (n) [true, true, false, true, false, true, false, true, false] (R), .A⟩ = some ⟨rep (n) [true, true, true, true, true, true, true, false, false] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 11) (by omega) (h0)

/-- B moving right across n copies of 110101010 leaves n copies of 101001111 (39 steps each). -/
theorem sweep_rB_110101010 (n : Nat) (L R : Tape) :
    steps (39 * n) ⟨L, rep (n) [true, true, false, true, false, true, false, true, false] (R), .B⟩ = some ⟨rep (n) [true, true, true, true, false, false, true, false, true] (L), R, .B⟩ := by
  have c0 : ∀ L R : Tape, steps 39 ⟨app [] L, app [true, true, false, true, false, true, false, true, false] R, .B⟩ = some ⟨app [] (app [true, true, true, true, false, false, true, false, true] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 39) ⟨L, rep (n) [true, true, false, true, false, true, false, true, false] (R), .B⟩ = some ⟨rep (n) [true, true, true, true, false, false, true, false, true] (L), R, .B⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 39) (by omega) (h0)

/-- D moving left across n copies of 110101010 (reading 1) leaves n copies of 110111011 (13 steps each). -/
theorem sweep_lD_110101010_1 (n : Nat) (L R : Tape) :
    steps (13 * n) ⟨rep (n) [false, true, false, true, false, true, false, true, true] (L), cons true (R), .D⟩ = some ⟨L, cons true (rep (n) [true, true, false, true, true, true, false, true, true] (R)), .D⟩ := by
  have c0 : ∀ L R : Tape, steps 13 ⟨app [false, true, false, true, false, true, false, true, true] L, app [true] R, .D⟩ = some ⟨L, app [true] (app [true, true, false, true, true, true, false, true, true] R), .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 13) ⟨rep (n) [false, true, false, true, false, true, false, true, true] (L), cons true (R), .D⟩ = some ⟨L, cons true (rep (n) [true, true, false, true, true, true, false, true, true] (R)), .D⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 13) (by omega) (h0)

/-- A moving right across n copies of 101010110 leaves n copies of 111111001 (11 steps each). -/
theorem sweep_rA_101010110 (n : Nat) (L R : Tape) :
    steps (11 * n) ⟨L, rep (n) [true, false, true, false, true, false, true, true, false] (R), .A⟩ = some ⟨rep (n) [true, false, false, true, true, true, true, true, true] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 11 ⟨app [] L, app [true, false, true, false, true, false, true, true, false] R, .A⟩ = some ⟨app [] (app [true, false, false, true, true, true, true, true, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 11) ⟨L, rep (n) [true, false, true, false, true, false, true, true, false] (R), .A⟩ = some ⟨rep (n) [true, false, false, true, true, true, true, true, true] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 11) (by omega) (h0)

/-- E moving left across n copies of 101010110 (reading 1) leaves n copies of 111011110 (13 steps each). -/
theorem sweep_lE_101010110_1 (n : Nat) (L R : Tape) :
    steps (13 * n) ⟨rep (n) [false, true, true, false, true, false, true, false, true] (L), cons true (R), .E⟩ = some ⟨L, cons true (rep (n) [true, true, true, false, true, true, true, true, false] (R)), .E⟩ := by
  have c0 : ∀ L R : Tape, steps 13 ⟨app [false, true, true, false, true, false, true, false, true] L, app [true] R, .E⟩ = some ⟨L, app [true] (app [true, true, true, false, true, true, true, true, false] R), .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 13) ⟨rep (n) [false, true, true, false, true, false, true, false, true] (L), cons true (R), .E⟩ = some ⟨L, cons true (rep (n) [true, true, true, false, true, true, true, true, false] (R)), .E⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 13) (by omega) (h0)

/-- A moving right across n copies of 011010101 leaves n copies of 110100111 (39 steps each). -/
theorem sweep_rA_011010101 (n : Nat) (L R : Tape) :
    steps (39 * n) ⟨L, rep (n) [false, true, true, false, true, false, true, false, true] (R), .A⟩ = some ⟨rep (n) [true, true, true, false, false, true, false, true, true] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 39 ⟨app [] L, app [false, true, true, false, true, false, true, false, true] R, .A⟩ = some ⟨app [] (app [true, true, true, false, false, true, false, true, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 39) ⟨L, rep (n) [false, true, true, false, true, false, true, false, true] (R), .A⟩ = some ⟨rep (n) [true, true, true, false, false, true, false, true, true] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 39) (by omega) (h0)

/-- D moving left across n copies of 011010101 (reading 0) leaves n copies of 111011101 (13 steps each). -/
theorem sweep_lD_011010101_0 (n : Nat) (L R : Tape) :
    steps (13 * n) ⟨rep (n) [true, false, true, false, true, false, true, true, false] (L), cons false (R), .D⟩ = some ⟨L, cons false (rep (n) [true, true, true, false, true, true, true, false, true] (R)), .D⟩ := by
  have c0 : ∀ L R : Tape, steps 13 ⟨app [true, false, true, false, true, false, true, true, false] L, app [false] R, .D⟩ = some ⟨L, app [false] (app [true, true, true, false, true, true, true, false, true] R), .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 13) ⟨rep (n) [true, false, true, false, true, false, true, true, false] (L), cons false (R), .D⟩ = some ⟨L, cons false (rep (n) [true, true, true, false, true, true, true, false, true] (R)), .D⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 13) (by omega) (h0)

/-- E moving right across n copies of 011010101 leaves n copies of 100111111 (11 steps each). -/
theorem sweep_rE_011010101 (n : Nat) (L R : Tape) :
    steps (11 * n) ⟨L, rep (n) [false, true, true, false, true, false, true, false, true] (R), .E⟩ = some ⟨rep (n) [true, true, true, true, true, true, false, false, true] (L), R, .E⟩ := by
  have c0 : ∀ L R : Tape, steps 11 ⟨app [] L, app [false, true, true, false, true, false, true, false, true] R, .E⟩ = some ⟨app [] (app [true, true, true, true, true, true, false, false, true] L), R, .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 11) ⟨L, rep (n) [false, true, true, false, true, false, true, false, true] (R), .E⟩ = some ⟨rep (n) [true, true, true, true, true, true, false, false, true] (L), R, .E⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 11) (by omega) (h0)

end H50436
