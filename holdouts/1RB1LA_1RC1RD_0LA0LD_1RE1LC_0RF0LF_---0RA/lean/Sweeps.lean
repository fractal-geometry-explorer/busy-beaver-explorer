import Machine

/-! Shift rules of 1RB1LA_1RC1RD_0LA0LD_1RE1LC_0RF0LF_---0RA, found and proved by `tools/py/bbtools/symtm.py` (driven by the README's sweep search): a state crossing n copies of a word of the background in one sweep, for every n and every tape around. They are the building blocks of the sweeps described in the README; they do not by themselves decide halting. -/

namespace H100124

open TM

/-- D moving left across n copies of 11100 (reading 1) leaves n copies of 01010 (9 steps each). -/
theorem sweep_lD_11100_1 (n : Nat) (L R : Tape) :
    steps (9 * n) ⟨rep (n) [false, false, true, true, true] (L), cons true (R), .D⟩ = some ⟨L, cons true (rep (n) [false, true, false, true, false] (R)), .D⟩ := by
  have c0 : ∀ L R : Tape, steps 9 ⟨app [false, false, true, true, true] L, app [true] R, .D⟩ = some ⟨L, app [true] (app [false, true, false, true, false] R), .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 9) ⟨rep (n) [false, false, true, true, true] (L), cons true (R), .D⟩ = some ⟨L, cons true (rep (n) [false, true, false, true, false] (R)), .D⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 9) (by omega) (h0)

/-- D moving left across n copies of 01110 (reading 1) leaves n copies of 01101 (9 steps each). -/
theorem sweep_lD_01110_1 (n : Nat) (L R : Tape) :
    steps (9 * n) ⟨rep (n) [false, true, true, true, false] (L), cons true (R), .D⟩ = some ⟨L, cons true (rep (n) [false, true, true, false, true] (R)), .D⟩ := by
  have c0 : ∀ L R : Tape, steps 9 ⟨app [false, true, true, true, false] L, app [true] R, .D⟩ = some ⟨L, app [true] (app [false, true, true, false, true] R), .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 9) ⟨rep (n) [false, true, true, true, false] (L), cons true (R), .D⟩ = some ⟨L, cons true (rep (n) [false, true, true, false, true] (R)), .D⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 9) (by omega) (h0)

/-- C moving left across n copies of 00111 (reading 0) leaves n copies of 10110 (9 steps each). -/
theorem sweep_lC_00111_0 (n : Nat) (L R : Tape) :
    steps (9 * n) ⟨rep (n) [true, true, true, false, false] (L), cons false (R), .C⟩ = some ⟨L, cons false (rep (n) [true, false, true, true, false] (R)), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 9 ⟨app [true, true, true, false, false] L, app [false] R, .C⟩ = some ⟨L, app [false] (app [true, false, true, true, false] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 9) ⟨rep (n) [true, true, true, false, false] (L), cons false (R), .C⟩ = some ⟨L, cons false (rep (n) [true, false, true, true, false] (R)), .C⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 9) (by omega) (h0)

/-- C moving left across n copies of 00111 (reading 1) leaves n copies of 10010 (9 steps each). -/
theorem sweep_lC_00111_1 (n : Nat) (L R : Tape) :
    steps (9 * n) ⟨rep (n) [true, true, true, false, false] (L), cons true (R), .C⟩ = some ⟨L, cons true (rep (n) [true, false, false, true, false] (R)), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 9 ⟨app [true, true, true, false, false] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [true, false, false, true, false] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 9) ⟨rep (n) [true, true, true, false, false] (L), cons true (R), .C⟩ = some ⟨L, cons true (rep (n) [true, false, false, true, false] (R)), .C⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 9) (by omega) (h0)

/-- A moving left across n copies of 10011 (reading 1) leaves n copies of 01011 (9 steps each). -/
theorem sweep_lA_10011_1 (n : Nat) (L R : Tape) :
    steps (9 * n) ⟨rep (n) [true, true, false, false, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [false, true, false, true, true] (R)), .A⟩ := by
  have c0 : ∀ L R : Tape, steps 9 ⟨app [true, true, false, false, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [false, true, false, true, true] R), .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 9) ⟨rep (n) [true, true, false, false, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [false, true, false, true, true] (R)), .A⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 9) (by omega) (h0)

/-- D moving left across n copies of 10011 (reading 1) leaves n copies of 01001 (9 steps each). -/
theorem sweep_lD_10011_1 (n : Nat) (L R : Tape) :
    steps (9 * n) ⟨rep (n) [true, true, false, false, true] (L), cons true (R), .D⟩ = some ⟨L, cons true (rep (n) [false, true, false, false, true] (R)), .D⟩ := by
  have c0 : ∀ L R : Tape, steps 9 ⟨app [true, true, false, false, true] L, app [true] R, .D⟩ = some ⟨L, app [true] (app [false, true, false, false, true] R), .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 9) ⟨rep (n) [true, true, false, false, true] (L), cons true (R), .D⟩ = some ⟨L, cons true (rep (n) [false, true, false, false, true] (R)), .D⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 9) (by omega) (h0)

/-- A moving left across n copies of 11001 (reading 1) leaves n copies of 10101 (9 steps each). -/
theorem sweep_lA_11001_1 (n : Nat) (L R : Tape) :
    steps (9 * n) ⟨rep (n) [true, false, false, true, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [true, false, true, false, true] (R)), .A⟩ := by
  have c0 : ∀ L R : Tape, steps 9 ⟨app [true, false, false, true, true] L, app [true] R, .A⟩ = some ⟨L, app [true] (app [true, false, true, false, true] R), .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 9) ⟨rep (n) [true, false, false, true, true] (L), cons true (R), .A⟩ = some ⟨L, cons true (rep (n) [true, false, true, false, true] (R)), .A⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 9) (by omega) (h0)

/-- C moving left across n copies of 11001 (reading 1) leaves n copies of 10100 (9 steps each). -/
theorem sweep_lC_11001_1 (n : Nat) (L R : Tape) :
    steps (9 * n) ⟨rep (n) [true, false, false, true, true] (L), cons true (R), .C⟩ = some ⟨L, cons true (rep (n) [true, false, true, false, false] (R)), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 9 ⟨app [true, false, false, true, true] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [true, false, true, false, false] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 9) ⟨rep (n) [true, false, false, true, true] (L), cons true (R), .C⟩ = some ⟨L, cons true (rep (n) [true, false, true, false, false] (R)), .C⟩ :=
    cross_l trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 9) (by omega) (h0)

end H100124
