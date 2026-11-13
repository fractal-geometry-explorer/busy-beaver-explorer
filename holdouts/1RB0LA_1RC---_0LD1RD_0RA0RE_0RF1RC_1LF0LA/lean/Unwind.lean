import Rules

/-!
# The leftward half of a pass, for any number of blocks

On its way back to the wall the head turns each block `1^2 0` (written on the way right) back into `1^3`:
`unwind`: `L (110)^n 111 B>000 R` reaches `L 111 B>000 (111)^n R` in 11n steps, for every n and all tapes L, R
(`unit` of `Rules.lean`, generated, iterated by induction; written by hand).
-/

namespace H7846

open TM

theorem unwind (L : Tape) (n : Nat) : ∀ R : Tape,
    steps (11 * n) ⟨cons true (cons true (cons true (rep n [false, true, true] L))), cons false (cons false (cons false R)), .B⟩ =
      some ⟨cons true (cons true (cons true L)), cons false (cons false (cons false (rep n [true, true, true] R))), .B⟩ := by
  induction n with
  | zero => intro R; rfl
  | succ n ih =>
    intro R
    have h := steps_seq trans (unit (rep n [false, true, true] L) R) (ih (cons true (cons true (cons true R))))
    rw [show 11 + 11 * n = 11 * (n + 1) by omega,
      show cons true (cons true (cons true R)) = app [true, true, true] R from rfl, rep_app_comm] at h
    exact h

end H7846
