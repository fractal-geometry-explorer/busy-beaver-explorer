import Machine

/-! # Where a halt of 1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB can come from

Written by `py/route.py`.  `halt_route`: if the machine halts on its third step from a configuration `c0` (two
ordinary steps, then a configuration with no transition), then `c0` is one of the patterns below.  So a run reaches
a halt only through one of them; a proof of non-halting only has to rule these out.  The proof splits on the state
and on the five cells around the head and lets `simp` run the steps (kernel-checked). -/

set_option linter.unusedSimpArgs false

namespace H113677

open TM

/-- Two steps before a halt the machine is in one of: D with 0 left, 1 right, 1 two right; D with 1 under the head, 1 right, 1 two right; D with 0 left, 0 under the head. -/
theorem halt_route (c0 c1 c2 : Config) (h1 : step c0 = some c1) (h2 : step c1 = some c2)
    (h3 : step c2 = none) :
      (c0.st = .D ∧ c0.l 0 = false ∧ c0.r 1 = true ∧ c0.r 2 = true) ∨
      (c0.st = .D ∧ c0.r 0 = true ∧ c0.r 1 = true ∧ c0.r 2 = true) ∨
      (c0.st = .D ∧ c0.l 0 = false ∧ c0.r 0 = false) := by
  obtain ⟨l, r, s⟩ := c0
  cases s <;> cases ha : r 0 <;> cases hb : r 1 <;> cases hc : r 2 <;> cases hd : l 0 <;> cases he : l 1 <;>
    simp [step, TM.step, trans, ha, hb, hc, hd, he, cons, tail] at h1 <;> subst h1 <;>
    simp [step, TM.step, trans, ha, hb, hc, hd, he, cons, tail] at h2 <;> subst h2 <;>
    simp_all [step, TM.step, trans, cons, tail]

end H113677
