import Machine

/-! Sweep rules of the self-loops, written by `holdouts/1RB0RA_0LC0RE_1LE1LD_0LE---_1LF0LC_1RA1LE/py/sweeps.py`. -/

namespace H65692

open TM

/-- `A` crosses a run of 1s rightwards, writing 0s. -/
theorem sweep_A1 (n : Nat) (L R : Tape) :
    steps (n) ⟨L, rep (n) [true] (R), .A⟩ = some ⟨rep (n) [false] (L), R, .A⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [] L, app [true] R, .A⟩ = some ⟨app [] (app [false] L), R, .A⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨L, rep (n) [true] (R), .A⟩ = some ⟨rep (n) [false] (L), R, .A⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 1) (by omega) (h0)

/-- `C` crosses a run of 0s leftwards, writing 1s. -/
theorem sweep_C0 (n : Nat) (L R : Tape) :
    steps (n + 1) ⟨rep (n) [false] (cons true (L)), cons false (R), .C⟩ = some ⟨L, cons true (cons true (rep (n) [true] (R))), .C⟩ := by
  have c0 : ∀ L R : Tape, steps 1 ⟨app [false] L, app [false] R, .C⟩ = some ⟨L, app [false] (app [true] R), .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 1) ⟨rep (n) [false] (cons true (L)), cons false (R), .C⟩ = some ⟨cons true (L), cons false (rep (n) [true] (R)), .C⟩ :=
    cross_l trans c0 (n) (cons true (L)) (R)
  have h1 : steps 1 ⟨cons true (L), cons false (rep (n) [true] (R)), .C⟩ = some ⟨L, cons true (cons true (rep (n) [true] (R))), .C⟩ := rfl
  exact steps_congr trans (a := (n) * 1 + (1)) (by omega) (steps_seq trans h0 (h1))

end H65692
