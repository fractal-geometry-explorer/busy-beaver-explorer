import Machine

/-!
# The run from blank tape, bounded

Plain step-by-step runs, evaluated on the list simulator of `tools/lean/TM/Fin.lean` (proved to agree with `steps`).
They are a floor and a test of the setup, not the way to the question: the passes of `Rules.lean` are.

The only halting transition is F0, and F is entered only by E0 (write 1, move left).  So a halt is exactly the moment
E reads a 0 with a 0 to its left (`halt_shape`).
-/

namespace BB6d

open TM

/-- The halting configurations: the machine stops exactly in state F on a 0. -/
theorem step_none_iff (c : Config) : step c = none ↔ c.st = .F ∧ c.r 0 = false := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h : r 0 <;> simp [step, TM.step, trans, h]

/-- `0 E>0` halts after one ordinary step, whatever the rest of the tape. -/
theorem halt_shape (L R : Tape) : ∃ c, steps 1 ⟨cons false L, cons false R, .E⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- After 17 steps from blank tape the tape is `1^2 0 1^2 A>0`, the start of the first pass, checked by the kernel. -/
theorem blank_at_17 :
    steps 17 init = some (FCfg.toCfg ⟨[true, true, false, true, true], [], .A⟩) :=
  blank_reaches trans (by decide +kernel)

/-- 20,000 steps from blank tape without a halt, checked by Lean's kernel alone. -/
theorem blank_runs_20000 : ∃ c, steps 20000 init = some c :=
  blank_runs trans (by decide +kernel)

/-- 10,000,000 steps from blank tape without a halt, by compiled evaluation. -/
theorem blank_runs_10M : ∃ c, steps 10000000 init = some c :=
  blank_runs trans (by native_decide)

end BB6d
