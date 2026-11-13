import Macro

/-!
# From blank tape to the particle picture

`reach_Q0`: 397 steps from blank tape give `Q0 3 10 R0` (`R0 = 0 1 1 0 0 1 1`, then blank tape); `travel` then
carries Q four pairs to the right (`reach_travel`, step 813), and one more bounce puts Q, in its long form,
next to the first stationary particle `P = 0 1 1 0 0` (`reach_P`, step 903).  Kernel only (`decide +kernel` on
the list simulator of `TM/Fin.lean`).
-/

namespace H54407

open TM

/-- The tape right of Q at step 397. -/
def R0 : Tape := app [false, true, true, false, false, true, true] blank

theorem reach_Q0 : steps 397 init = some (Q0 3 10 R0) := by
  have h : fsteps 397 (FCfg.blank .A) = some ⟨[true], [true, false, true, false, true, false, true, false, false,
      true, false, true, false, true, false, true, false, true, false, true, false, true, false, true, false, true,
      false, true, false, false, true, true, false, false, true, true], .A⟩ := by decide +kernel
  exact (blank_reaches trans h).trans rfl

theorem reach_travel : steps 813 init = some (Q0 19 2 R0) :=
  steps_congr trans (by omega) (steps_seq trans reach_Q0 (travel 4 3 1 R0))

theorem reach_P : steps 903 init = some (Q1 21 0 R0) :=
  steps_congr trans (by omega) (steps_seq trans reach_travel (bounce0 19 0 R0))

end H54407
