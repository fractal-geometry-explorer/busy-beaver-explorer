import Rle

/-!
# A long run from blank tape

From the configuration reached after 5,512 steps (`reach_D0`, the right end in its other phase) the run-length
sweep program `runR` (`Rle.lean`) goes 258,046 sweeps, every one of them a proved sweep, to step 266,357,150,814.
There the carry of the counter reaches the leftmost block `1^12` (digits `1 1 5 1^9 3 1^129022`), whose length is
even: the third nested run of the run from blank tape starts (after those at sweeps 5 and 28), which no proved
rule covers (`nextR` answers
`none`).  Evaluated by compiled code (`native_decide`): the machine does not halt in its first 266,357,150,814
steps (`no_halt_long`).
-/

namespace H23154

open TM

/-- The configuration after 5,512 steps, on runs (`D0 = [0, 0, 1, 1, 1, 0, 2, 1^10]`, other phase). -/
def s0R : MR := ⟨3, [(1, 10), (2, 1), (0, 1), (1, 3), (0, 2)], true⟩

theorem s0R_cfg : s0R.cfg = Q (raw 3) D0 := rfl

theorem run_value : ((runR 258046 s0R 5512).map (·.2)) = some 266357150814 := by native_decide

/-- The next sweep is a carry at a leftmost block of even length, not covered by the proved rules. -/
theorem run_stops : ((runR 258046 s0R 5512).map (fun x => (x.1.r, (nextR x.1).isNone))) = some (12, true) := by
  native_decide

/-- **No halt in the first 266,357,150,814 steps.** -/
theorem no_halt_long : ∃ c, steps 266357150814 init = some c := by
  have h := run_value
  cases e : runR 258046 s0R 5512 with
  | none => rw [e] at h; cases h
  | some x =>
    rw [e] at h
    obtain ⟨s', t'⟩ := x
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact ⟨_, runR_sound 258046 s0R 5512 s' _ e (by rw [s0R_cfg]; exact reach_D0)⟩

end H23154
