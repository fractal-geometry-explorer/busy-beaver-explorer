import Machine

/-!
# The first samples of the run: F at the left end of an all-ones tape

The run from blank tape passes through configurations `F> 1^N` on otherwise blank tape (head on the leftmost 1),
with N = 8, 22, 42, 58, 90, 148, 218, 298, 410, 554, 746, 1002, ... Each one fixes the rest of the run, so the
machine is the map N ↦ N' iterated from 8. Here: the first samples, by Lean's list simulator (`tools/lean/TM/Fin.lean`).
-/

namespace H45924

open TM

/-- The sample `F> 1^N` as a configuration. -/
def sample (N : Nat) : Config := FCfg.toCfg ⟨[], List.replicate N true, .F⟩

/-- 43 steps from blank tape: `F> 1^8`. -/
theorem orbit_8 : steps 43 init = some (sample 8) := blank_reaches trans (by decide +kernel)

/-- `F> 1^90` after 5,156 steps (kernel). -/
theorem orbit_90 : steps 5156 init = some (sample 90) := blank_reaches trans (by decide +kernel)

/-- `F> 1^148` after 13,203 steps (kernel). -/
theorem orbit_148 : steps 13203 init = some (sample 148) := blank_reaches trans (by decide +kernel)

/-- `F> 1^4992` after 17,659,931 steps (`native_decide`). -/
theorem orbit_4992 : steps 17659931 init = some (sample 4992) := blank_reaches trans (by native_decide)

/-- `F> 1^8906` after 56,708,301 steps (`native_decide`). -/
theorem orbit_8906 : steps 56708301 init = some (sample 8906) := blank_reaches trans (by native_decide)

end H45924
