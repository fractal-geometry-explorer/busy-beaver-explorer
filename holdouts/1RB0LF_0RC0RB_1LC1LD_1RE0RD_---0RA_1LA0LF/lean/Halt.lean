import Machine

/-!
# 1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF: what a halt needs

The machine halts on `E0`.  `E` is entered only from `D0`, and `D` only from `C1` (moving left, after writing a 1,
which is then the cell `E` reads) or from `D1` (moving right).  So the step two before a halt is `D` reading a 1:
**a halt needs a D-run**, D erasing a block of 1s rightwards (`halt_needs_drun`).  In the run from blank tape D-runs
are rare: in the first 10^9 steps there are four, all at the right end of the tape (the wall), when the wall grows.
-/

namespace H147837

open TM

theorem halt_needs_drun (c c1 c2 : Config) (h1 : step c = some c1) (h2 : step c1 = some c2)
    (h3 : step c2 = none) : c.st = .D ∧ c.r 0 = true := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases hr : r 0 <;> simp [step, TM.step, trans, hr] at h1 <;> subst h1 <;>
    cases hl : l 0 <;> cases hr1 : r 1 <;> cases hl1 : l 1 <;> cases hr2 : r 2 <;>
    simp [step, TM.step, trans, hr, hl, hr1, hl1, tail, cons] at h2 <;> subst h2 <;>
    simp [step, TM.step, trans, hr, hl, hr1, hl1, hr2, tail, cons] at h3 ⊢

end H147837
