import Machine

/-! Sweep rules of the self-loops, written by `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/sweeps.py`. -/

namespace H130046

open TM

/-- `A` crosses a run of 1s rightwards, writing 0s. -/
theorem sweep_A1 (n : Nat) (L R : Tape) :
    steps (n) ⟨L, rep (n) [true] (R), .A⟩ = some ⟨rep (n) [false] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .A⟩ = some ⟨app [] (app [false] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨L, rep (n) [true] (R), .A⟩ = some ⟨rep (n) [false] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)

end H130046
