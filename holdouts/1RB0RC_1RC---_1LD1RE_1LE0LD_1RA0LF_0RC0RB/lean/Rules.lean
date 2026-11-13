import Machine

/-! Shift rules of 1RB0RC_1RC---_1LD1RE_1LE0LD_1RA0LF_0RC0RB, found and proved by `bbtools.symtm` for every n and every tape around (L, R); the left tape is listed from the head outward in Lean. -/

namespace H16925

open TM

/-- Going right in A, each 110 becomes 011. -/
theorem right_A (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨L, rep (n) [true, true, false] (R), .A⟩ = some ⟨rep (n) [true, true, false] (L), R, .A⟩ := by
  have hn : (n) * 3 = 3 * n := by omega
  have c0 : ∀ L R : Tape, steps 3 ⟨app [] L, app [true, true, false] R, .A⟩ = some ⟨app [] (app [true, true, false] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨L, rep (n) [true, true, false] (R), .A⟩ = some ⟨rep (n) [true, true, false] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans hn (h0)

/-- Going right in E, each 011 becomes 101. -/
theorem right_E (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨L, rep (n) [false, true, true] (R), .E⟩ = some ⟨rep (n) [true, false, true] (L), R, .E⟩ := by
  have hn : (n) * 3 = 3 * n := by omega
  have c0 : ∀ L R : Tape, steps 3 ⟨app [] L, app [false, true, true] R, .E⟩ = some ⟨app [] (app [true, false, true] L), R, .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨L, rep (n) [false, true, true] (R), .E⟩ = some ⟨rep (n) [true, false, true] (L), R, .E⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans hn (h0)

/-- Going right in C, each 1010 becomes 0101 (a block of 10 shifted by a cell). -/
theorem right_C_10 (n : Nat) (L R : Tape) :
    steps (12 * n) ⟨L, rep (n) [true, false, true, false] (R), .C⟩ = some ⟨rep (n) [true, false, true, false] (L), R, .C⟩ := by
  have hn : (n) * 12 = 12 * n := by omega
  have c0 : ∀ L R : Tape, steps 12 ⟨app [] L, app [true, false, true, false] R, .C⟩ = some ⟨app [] (app [true, false, true, false] L), R, .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 12) ⟨L, rep (n) [true, false, true, false] (R), .C⟩ = some ⟨rep (n) [true, false, true, false] (L), R, .C⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans hn (h0)

/-- Going right in C, each 1000 becomes 1111 (a stretch of 0^4-separated cells filled). -/
theorem right_C_1000 (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨L, rep (n) [true, false, false, false] (R), .C⟩ = some ⟨rep (n) [true, true, true, true] (L), R, .C⟩ := by
  have hn : (n) * 4 = 4 * n := by omega
  have c0 : ∀ L R : Tape, steps 4 ⟨app [] L, app [true, false, false, false] R, .C⟩ = some ⟨app [] (app [true, true, true, true] L), R, .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨L, rep (n) [true, false, false, false] (R), .C⟩ = some ⟨rep (n) [true, true, true, true] (L), R, .C⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans hn (h0)

/-- Going right in E, each 0001 becomes 1111. -/
theorem right_E_0001 (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨L, rep (n) [false, false, false, true] (R), .E⟩ = some ⟨rep (n) [true, true, true, true] (L), R, .E⟩ := by
  have hn : (n) * 4 = 4 * n := by omega
  have c0 : ∀ L R : Tape, steps 4 ⟨app [] L, app [false, false, false, true] R, .E⟩ = some ⟨app [] (app [true, true, true, true] L), R, .E⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 4) ⟨L, rep (n) [false, false, false, true] (R), .E⟩ = some ⟨rep (n) [true, true, true, true] (L), R, .E⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans hn (h0)

end H16925
