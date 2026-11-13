import Sim

/-! A long run of the checked simulator of `Sim.lean` (compiled evaluation, `native_decide`). -/

namespace H158007

open TM

/-- No halt in the first 2,000,000,000 steps from blank tape: 100,000,000 steps of the simulator, each proved to
be a run of the machine (`runH_sound`), count more machine steps than that. -/
theorem no_halt_2e9 : ∃ c, steps 2000000000 init = some c :=
  no_halt_of_runH (k := 100000000) (by native_decide)

end H158007
