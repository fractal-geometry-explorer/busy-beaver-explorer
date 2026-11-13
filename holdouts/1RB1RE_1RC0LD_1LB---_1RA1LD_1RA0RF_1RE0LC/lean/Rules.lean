import Machine

/-! The leftward sweep of 1RB1RE_1RC0LD_1LB---_1RA1LD_1RA0RF_1RE0LC. Written by `py/rules.py` with `bbtools.symtm.prove`; checked by the kernel. -/

namespace H151599

open TM

/-- The leftward sweep: the block of words 01011111 becomes a block of words 11101000. -/
theorem sweep_left (n : Nat) (L : Tape) :
    steps (38 * n + 118) ⟨cons true (cons true (rep (n + 3) [true, true, true, true, true, false, true, false] (L))), cons false (blank), .B⟩ = some ⟨L, cons true (rep (n + 3) [true, true, false, true, false, false, false, true] (cons true (cons false (cons true (blank))))), .D⟩ := by
  have h0 : steps 4 ⟨cons true (cons true (rep (n + 3) [true, true, true, true, true, false, true, false] (L))), cons false (blank), .B⟩ = some ⟨rep (n + 3) [true, true, true, true, true, false, true, false] (L), cons true (cons true (cons false (cons true (blank)))), .D⟩ := rfl
  have c1 : ∀ L R : Tape, steps 38 ⟨app [true, true, true, true, true, false, true, false] L, app [true] R, .D⟩ = some ⟨L, app [true] (app [true, true, false, true, false, false, false, true] R), .D⟩ := fun _ _ => rfl
  have h1 : steps ((n + 3) * 38) ⟨rep (n + 3) [true, true, true, true, true, false, true, false] (L), cons true (cons true (cons false (cons true (blank)))), .D⟩ = some ⟨L, cons true (rep (n + 3) [true, true, false, true, false, false, false, true] (cons true (cons false (cons true (blank))))), .D⟩ :=
    cross_l trans c1 (n + 3) (L) (cons true (cons false (cons true (blank))))
  exact steps_congr trans (a := 4 + ((n + 3) * 38)) (by omega) (steps_seq trans h0 (h1))

end H151599
