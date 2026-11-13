import Carry

/-!
# From blank tape to the first configuration of the long run

After 5,512 steps from blank tape (sweep 29) the machine is in the configuration
`1^3 | 0 0 1 1 1 0 2 1 1 1 1 1 1 1 1 1 1 | 0 1^4 C>0`: the leftmost block `1^3`, seventeen digits, and the right end
in its other phase, just after a carry at the leftmost block `1^6` (the nested run, not formalized, which the first
sweeps went through twice).  Checked by Lean's kernel on the list simulator of `tools/lean/TM/Fin.lean`.  From
there on the sweeps of `Sweep.lean` and `Carry.lean` apply.
-/

namespace H23154

open TM

/-- The digits at step 5,512. -/
def D0 : List Nat := [0, 0, 1, 1, 1, 0, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

theorem reach_D0 : steps 5512 init = some (Q (raw 3) D0) := by
  have h := blank_reaches trans (n := 5512) (q := .A) (c := ⟨[true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, true, true, true, false, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, true, true, true, false, true, true, false, true, true, false, true, true, true], [], .C⟩) (by decide +kernel)
  exact h

end H23154
