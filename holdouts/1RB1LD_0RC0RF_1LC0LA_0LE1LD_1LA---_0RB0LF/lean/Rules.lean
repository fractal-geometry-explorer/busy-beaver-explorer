import Machine

/-! # A transfer rule of 1RB1LD_0RC0RF_1LC0LA_0LE1LD_1LA---_0RB0LF

The tape is a few blocks of 1s separated by short runs of 0s. Inside a sweep, a single 0 travels right through a block, three steps per cell (`c_shift`), which moves one unit from the block on its right to the block on its left each step of three.

Written by `bbtools.symtm.prove` (the trace of a symbolic run, checked by the kernel). -/

namespace H68273

open TM

/-- `0 C> 1^n` becomes `1^n 0 C>` in 3n steps: the 0 next to the head travels right through the block (C1 -> 0LA, A0 -> 1RB, B0 -> 0RC). -/
theorem c_shift (n : Nat) (L R : Tape) :
    steps (3 * n) ⟨cons false (L), rep (n) [true] (R), .C⟩ = some ⟨cons false (rep (n) [true] (L)), R, .C⟩ := by
  have c0 : ∀ L R : Tape, steps 3 ⟨app [false] L, app [true] R, .C⟩ = some ⟨app [false] (app [true] L), R, .C⟩ := fun _ _ => rfl
  have h0 : steps ((n) * 3) ⟨cons false (L), rep (n) [true] (R), .C⟩ = some ⟨cons false (rep (n) [true] (L)), R, .C⟩ :=
    cross_r trans c0 (n) (L) (R)
  exact steps_congr trans (a := (n) * 3) (by omega) (h0)


end H68273
