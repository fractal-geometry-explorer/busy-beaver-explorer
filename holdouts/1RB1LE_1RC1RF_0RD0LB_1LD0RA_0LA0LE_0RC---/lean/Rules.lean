import Machine

/-! # Crossing rules of 1RB1LE_1RC1RF_0RD0LB_1LD0RA_0LA0LE_0RC---

Moving right, C crosses runs of `011` and of `011111` at once, shifting them by one cell; these are the two pieces of the period-24 background word as the right sweep sees it.

Written by `bbtools.symtm.prove` (the trace of a symbolic run, checked by the kernel). -/

namespace H82729

open TM

/-- C crosses copies of `011`, leaving `110`. -/
theorem c_cross_3 (n : Nat) (L R : Tape) :
    steps (9 * n) ⟨L, rep (n) [false, true, true] (R), .C⟩ = some ⟨rep (n) [false, true, true] (L), R, .C⟩ := by
  have c0 : ∀ L R : Tape, steps 9 ⟨app [] L, app [false, true, true] R, .C⟩ = some ⟨app [] (app [false, true, true] L), R, .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 9) ⟨L, rep (n) [false, true, true] (R), .C⟩ = some ⟨rep (n) [false, true, true] (L), R, .C⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 9) (by omega) (h0)


/-- C crosses copies of `011111`, leaving `111110`. -/
theorem c_cross_6 (n : Nat) (L R : Tape) :
    steps (20 * n) ⟨L, rep (n) [false, true, true, true, true, true] (R), .C⟩ = some ⟨rep (n) [false, true, true, true, true, true] (L), R, .C⟩ := by
  have c0 : ∀ L R : Tape, steps 20 ⟨app [] L, app [false, true, true, true, true, true] R, .C⟩ = some ⟨app [] (app [false, true, true, true, true, true] L), R, .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 20) ⟨L, rep (n) [false, true, true, true, true, true] (R), .C⟩ = some ⟨rep (n) [false, true, true, true, true, true] (L), R, .C⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 20) (by omega) (h0)


end H82729
