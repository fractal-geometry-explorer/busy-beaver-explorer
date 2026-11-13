import Machine

/-! Sweep rules of the self-loops, written by `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/sweeps.py`. -/

namespace H25604

open TM

/-- `C` crosses a run of 1s leftwards, writing 1s. -/
theorem sweep_C1 (n : Nat) (L R : Tape) :
    steps (n + 1) ⟨rep (n) [true] (cons false (L)), cons true (R), .C⟩ = some ⟨L, cons false (cons true (rep (n) [true] (R))), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [true] L, app [true] R, .C⟩ = some ⟨L, app [true] (app [true] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨rep (n) [true] (cons false (L)), cons true (R), .C⟩ = some ⟨cons false (L), cons true (rep (n) [true] (R)), .C⟩ :=
    cross_l trans c0 (n) (cons false (L)) (R)
  have h1 : steps 1 ⟨cons false (L), cons true (rep (n) [true] (R)), .C⟩ = some ⟨L, cons false (cons true (rep (n) [true] (R))), .C⟩ := rfl
  exact steps_congr trans (a := (n) * 1 + (1)) (by omega) (steps_seq trans h0 (h1))

end H25604
