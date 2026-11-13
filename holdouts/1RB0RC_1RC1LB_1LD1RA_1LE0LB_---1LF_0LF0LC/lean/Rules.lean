import Machine

/-! Shift rules: C turns 100 into 111, A turns 001 into 111 and passes over 1101, each for every n. -/

namespace H71477

open TM

/-- C going right turns every `100` into `111`. -/
theorem right_C_100 (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨L, rep (n) [true, false, false] (R), .C⟩ = some ⟨rep (n) [true, true, true] (L), R, .C⟩ := by
  have hn : (n) * 3 = 3 * n := by omega
  have c0 : ∀ L R : Tape, steps 3 ⟨app [] L, app [true, false, false] R, .C⟩ = some ⟨app [] (app [true, true, true] L), R, .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨L, rep (n) [true, false, false] (R), .C⟩ = some ⟨rep (n) [true, true, true] (L), R, .C⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans hn (h0)

/-- A going right turns every `001` into `111`. -/
theorem right_A_001 (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨L, rep (n) [false, false, true] (R), .A⟩ = some ⟨rep (n) [true, true, true] (L), R, .A⟩ := by
  have hn : (n) * 3 = 3 * n := by omega
  have c0 : ∀ L R : Tape, steps 3 ⟨app [] L, app [false, false, true] R, .A⟩ = some ⟨app [] (app [true, true, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨L, rep (n) [false, false, true] (R), .A⟩ = some ⟨rep (n) [true, true, true] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans hn (h0)

/-- A going right passes over `1101` unchanged. -/
theorem right_A_1101 (n : Nat) (L R : Tape) :
    steps (10 * n) ⟨L, rep (n) [true, true, false, true] (R), .A⟩ = some ⟨rep (n) [true, false, true, true] (L), R, .A⟩ := by
  have hn : (n) * 10 = 10 * n := by omega
  have c0 : ∀ L R : Tape, steps 10 ⟨app [] L, app [true, true, false, true] R, .A⟩ = some ⟨app [] (app [true, false, true, true] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 10) ⟨L, rep (n) [true, true, false, true] (R), .A⟩ = some ⟨rep (n) [true, false, true, true] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans hn (h0)

end H71477
