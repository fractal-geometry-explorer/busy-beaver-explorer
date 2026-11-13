import Machine

/-! Sweep rules of the self-loops, written by `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/sweeps.py`. -/

namespace H155590

open TM

/-- `D` crosses a run of 1s rightwards, writing 0s. -/
theorem sweep_D1 (n : Nat) (L R : Tape) :
    steps (n) ⟨L, rep (n) [true] (R), .D⟩ = some ⟨rep (n) [false] (L), R, .D⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .D⟩ = some ⟨app [] (app [false] L), R, .D⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨L, rep (n) [true] (R), .D⟩ = some ⟨rep (n) [false] (L), R, .D⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)

end H155590
