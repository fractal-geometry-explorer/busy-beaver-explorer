import Machine

/-!
# The run from blank tape, bounded

Plain step-by-step runs, evaluated on the list simulator of `tools/lean/TM/Fin.lean` (proved to agree with `steps`).
In the bbchallenge count these say the machine does not halt within the first 20,000 steps (kernel) and the first
10,000,000 steps (`native_decide`, which also trusts Lean's compiler).  They are a floor and a test of the setup, not
the way to the question: the run's macro structure is where the proofs have to go.
-/

namespace BB6b

open TM

/-- 20,000 steps from blank tape without a halt, checked by Lean's kernel alone. -/
theorem blank_runs_20000 : ∃ c, steps 20000 init = some c :=
  blank_runs trans (by decide +kernel)

/-- 10,000,000 steps from blank tape without a halt, by compiled evaluation. -/
theorem blank_runs_10M : ∃ c, steps 10000000 init = some c :=
  blank_runs trans (by native_decide)

end BB6b
