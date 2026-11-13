import Macro

/-!
# From blank tape to the particle picture

`reach_Q0`: 1,819 steps from blank tape give `Q0 4 26 R1` (`R1 = 0 1 1 0 0 1 1 0 0 1 1 0 0 1`, then blank tape);
`travel` carries Q twelve pairs to the right (`reach_travel`, step 4,699), and one more bounce puts Q, in its long
form, next to the first stationary particle `P = 0 1 1 0 0` (`reach_P`, step 4,921).  Kernel only
(`decide +kernel` on the list simulator of `TM/Fin.lean`).
-/

namespace H86275

open TM

/-- The tape right of Q at step 1,819. -/
def R1 : Tape := app [false, true, true, false, false, true, true, false, false, true, true, false, false, true] blank

theorem reach_Q0 : steps 1819 init = some (Q0 4 26 R1) := by
  have h : fsteps 1819 (FCfg.blank .A) = some ⟨[true], [true, false, true, false, true, false, true, false, true, false, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true], .A⟩ := by decide +kernel
  exact (blank_reaches trans h).trans rfl

theorem reach_travel : steps 4699 init = some (Q0 52 2 R1) :=
  steps_congr trans (by omega) (steps_seq trans reach_Q0 (travel 12 4 1 R1))

theorem reach_P : steps 4921 init = some (Q1 54 0 R1) :=
  steps_congr trans (by omega) (steps_seq trans reach_travel (bounce0 52 0 R1))

end H86275
