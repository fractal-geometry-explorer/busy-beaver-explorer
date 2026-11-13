import Machine

/-!
# 1RB0RA_1LC0RA_0LD0LC_1RD1RE_1LF0LE_---0LB: what a halt needs

The machine halts on `F0`.  `F` is entered only from `E0` (moving left), and `E` from `D1` (moving right, after
writing a 1, which `F` would then read) or from `E1` (moving left).  So the step two before a halt is `E` reading a
1: **a halt needs an E-run**, E erasing a block of 1s leftwards (`halt_needs_erun`).  This is the mirror image of
`halt_needs_drun` of 1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF, whose state D is this machine's E.
-/

namespace H29825

open TM

theorem halt_needs_erun (c c1 c2 : Config) (h1 : step c = some c1) (h2 : step c1 = some c2)
    (h3 : step c2 = none) : c.st = .E ∧ c.r 0 = true := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases hr : r 0 <;> simp [step, TM.step, trans, hr] at h1 <;> subst h1 <;>
    cases hl : l 0 <;> cases hr1 : r 1 <;> cases hl1 : l 1 <;> cases hr2 : r 2 <;>
    simp [step, TM.step, trans, hr, hl, hr1, hl1, tail, cons] at h2 <;> subst h2 <;>
    simp [step, TM.step, trans, hr, hl, hr1, hl1, hr2, tail, cons] at h3 ⊢

end H29825
