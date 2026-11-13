import Machine

/-! Shift rules of 1RB0RC_1LC1RF_1RE0LD_1LC1LA_---1RD_0RB0RA, found and proved by `bbtools.symtm` for every n and every tape around (L, R); the left tape is listed from the head outward in Lean. -/

namespace H132224

open TM

/-- B crosses a block (10)^n to the right unchanged. -/
theorem right_B_a (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨L, rep (n) [true, false] (R), .B⟩ = some ⟨rep (n) [false, true] (L), R, .B⟩ := by
  have hn : (n) * 2 = 2 * n := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [true, false] R, .B⟩ = some ⟨app [] (app [false, true] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨L, rep (n) [true, false] (R), .B⟩ = some ⟨rep (n) [false, true] (L), R, .B⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans hn (h0)

/-- F crosses (01)^n to the right unchanged (the d-form 010 010 ... read with a shifted frame). -/
theorem right_F_d (n : Nat) (L R : Tape) :
    steps (2 * n) ⟨L, rep (n) [false, true] (R), .F⟩ = some ⟨rep (n) [true, false] (L), R, .F⟩ := by
  have hn : (n) * 2 = 2 * n := by omega
  have c0 : ∀ L R : Tape, steps 2 ⟨app [] L, app [false, true] R, .F⟩ = some ⟨app [] (app [true, false] L), R, .F⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 2) ⟨L, rep (n) [false, true] (R), .F⟩ = some ⟨rep (n) [true, false] (L), R, .F⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans hn (h0)

/-- Going right in A, each 011 becomes 110. -/
theorem right_A_011 (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨L, rep (n) [false, true, true] (R), .A⟩ = some ⟨rep (n) [false, true, true] (L), R, .A⟩ := by
  have hn : (n) * 3 = 3 * n := by omega
  have c0 : ∀ L R : Tape, steps 3 ⟨app [] L, app [false, true, true] R, .A⟩ = some ⟨app [] (app [false, true, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨L, rep (n) [false, true, true] (R), .A⟩ = some ⟨rep (n) [false, true, true] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans hn (h0)

/-- Going right in B, each 110 becomes 101. -/
theorem right_B_110 (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨L, rep (n) [true, true, false] (R), .B⟩ = some ⟨rep (n) [true, false, true] (L), R, .B⟩ := by
  have hn : (n) * 3 = 3 * n := by omega
  have c0 : ∀ L R : Tape, steps 3 ⟨app [] L, app [true, true, false] R, .B⟩ = some ⟨app [] (app [true, false, true] L), R, .B⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨L, rep (n) [true, true, false] (R), .B⟩ = some ⟨rep (n) [true, false, true] (L), R, .B⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans hn (h0)

end H132224
