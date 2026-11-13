import Carry

/-!
# From blank tape to the first sweep configuration

After 2,340 steps from blank tape the machine is in the sweep configuration
`1^3 | 0 2 2 1 1 1 1 1 2 0 | 0 1 B>0` (leftmost block `1^3`, then ten digits), checked by Lean's kernel on the
list simulator of `tools/lean/TM/Fin.lean`.  From there on the sweeps of `Sweep.lean` and `Carry.lean` apply.
-/

namespace H115779

open TM

/-- The first sweep configuration of the run. -/
def D0 : List Nat := [0, 2, 2, 1, 1, 1, 1, 1, 2, 0]

theorem reach_D0 : steps 2340 init = some (P (raw 3) D0) := by
  have h := blank_reaches trans (n := 2340) (q := .A)
    (c := ⟨[true, false, true, true, false, true, true, true, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, false, true, true, false, true, true, true], [], .B⟩) (by decide +kernel)
  exact h

/-- The next sweep, by `sweep_zero`: the last digit 0 merges with the 2 before it. -/
theorem reach_D1 : steps (2340 + 21) init = some (P (raw 3) [0, 2, 2, 1, 1, 1, 1, 1, 4]) := by
  have h := sweep_zero (raw 3) [0, 2, 2, 1, 1, 1, 1, 1] 2 []
  exact steps_seq trans reach_D0 h

end H115779
