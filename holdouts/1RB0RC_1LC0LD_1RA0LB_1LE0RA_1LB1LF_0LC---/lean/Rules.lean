import Machine

/-! Shift rules of 1RB0RC_1LC0LD_1RA0LB_1LE0RA_1LB1LF_0LC---, found and proved by `bbtools.symtm` for every n and every tape around (L, R); the left tape is listed from the head outward in Lean. -/

namespace H95984

open TM

/-- Going right in A, each 10 of a block becomes 01: `A> (10)^n` becomes `(01)^n A>` in 2n steps (the block moves one cell left). -/
theorem right_A (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨L, rep (n) [true, false] (R), .A⟩ = some ⟨rep (n) [true, false] (L), R, .A⟩ := by
  have hn : (n) * 2 = 2 * n := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .A⟩ = some ⟨app [] (app [true, false] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨L, rep (n) [true, false] (R), .A⟩ = some ⟨rep (n) [true, false] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans hn (h0)

/-- Going right in C, each 01 becomes 10: `C> (01)^n` becomes `(10)^n C>` in 2n steps. -/
theorem right_C (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨L, rep (n) [false, true] (R), .C⟩ = some ⟨rep (n) [false, true] (L), R, .C⟩ := by
  have hn : (n) * 2 = 2 * n := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .C⟩ = some ⟨app [] (app [false, true] L), R, .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨L, rep (n) [false, true] (R), .C⟩ = some ⟨rep (n) [false, true] (L), R, .C⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans hn (h0)

end H95984
