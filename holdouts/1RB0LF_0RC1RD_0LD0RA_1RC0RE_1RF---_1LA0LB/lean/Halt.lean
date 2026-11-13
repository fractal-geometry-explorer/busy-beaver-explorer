import Machine

/-!
# 1RB0LF_0RC1RD_0LD0RA_1RC0RE_1RF---_1LA0LB: what a halt needs

The machine halts on `E1`.  `E` is entered only from `D1` (moving right), `D` only from `B1` (moving right), and
`B` from `A0` (moving right) or from `F1` (moving left, after writing a 0, which `D` would then read).  So the
configuration three steps before a halt is `A` reading a 0 with `1 1 1` to its right: **a halt needs the word
`A>0 1 1 1`** (`halt_needs_A0111`).
-/

namespace H79385

open TM

theorem halt_needs_A0111 (c c1 c2 c3 : Config) (h1 : step c = some c1) (h2 : step c1 = some c2)
    (h3 : step c2 = some c3) (h4 : step c3 = none) :
    c.st = .A ∧ c.r 0 = false ∧ c.r 1 = true ∧ c.r 2 = true ∧ c.r 3 = true := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases hr : r 0 <;> simp [step, TM.step, trans, hr] at h1 <;> subst h1 <;>
    cases hl : l 0 <;> cases hr1 : r 1 <;> cases hl1 : l 1 <;> cases hr2 : r 2 <;>
    simp [step, TM.step, trans, hr, hl, hr1, hl1, tail, cons] at h2 <;> subst h2 <;>
    cases hl2 : l 2 <;> cases hr3 : r 3 <;>
    simp [step, TM.step, trans, hr, hl, hr1, hl1, hr2, hl2, hr3, tail, cons] at h3 <;> subst h3 <;>
    simp [step, TM.step, trans, hr, hl, hr1, hl1, hr2, hl2, hr3, tail, cons] at h4 ⊢

end H79385
