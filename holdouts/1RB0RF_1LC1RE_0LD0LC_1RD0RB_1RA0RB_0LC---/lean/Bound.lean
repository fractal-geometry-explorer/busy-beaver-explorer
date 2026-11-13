import Full

/-!
# A bounded run of the macro map

`Full.lean` proves that every step of the macro map `astep` is at least 17 machine steps.  Here the map is run
for 10^8 steps from the first Q configuration by compiled evaluation (`native_decide`): it never fails, so the
machine does not halt in its first 27 + 17·10^8 steps.
-/

namespace H67116

open TM

/-- 10^8 steps of the macro map succeed (compiled evaluation). -/
theorem arun_native : arunB 100000000 start = true := by native_decide

/-- No halt in the first 1,700,000,027 steps from blank tape. -/
theorem blank_runs_macro : ∃ c, steps (27 + 17 * 100000000) init = some c :=
  runs_of_arun _ (arunB_sound _ _ arun_native)

end H67116
