import Macro

/-!
# 1RB1LF_1RC1RB_1RD0RB_0LE0LF_---1LD_0LE1LA: long runs of the block machine

The block machine of `Macro.lean` is proved to follow the Turing machine step for step (`mrun_blank`), so evaluating
it is a cheap way to certify long runs: 30,000 block steps (1,199,390 machine steps) by Lean's kernel alone, and
18,000,000 block steps (124,890,717,366 machine steps) by compiled evaluation.  The C program `c/msim.c` runs the same
block machine to 10^18 steps (trusted, not proved).
-/

namespace H60424

open TM

theorem run_of_mrun {k N : Nat} (h : (mrun k minit 0).map (fun p => p.2) = some N) : ∃ c, steps N init = some c := by
  cases hm : mrun k minit 0 with
  | none => rw [hm] at h; cases h
  | some p =>
    obtain ⟨c, t⟩ := p
    rw [hm] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨_, mrun_blank k c t hm⟩

set_option maxRecDepth 1000000 in
/-- 1,199,390 steps from blank tape without a halt: 30,000 block-machine steps, evaluated by the kernel. -/
theorem macro_runs_kernel : ∃ c, steps 1199390 init = some c :=
  run_of_mrun (k := 30000) (by decide +kernel)

/-- 124,890,717,366 steps from blank tape without a halt: 18,000,000 block-machine steps, by `native_decide`. -/
theorem macro_runs_native : ∃ c, steps 124890717366 init = some c :=
  run_of_mrun (k := 18000000) (by native_decide)

end H60424
