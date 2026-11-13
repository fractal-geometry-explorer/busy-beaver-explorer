import Machine

/-!
# 1RB0LE_1LC1RD_1LA0RB_1RC1RB_1LF0LC_---0RC: how a halt comes about

The only halting transition is F reading 0. F is entered only from E reading 0 (`enter_F`), E only from A reading 1
(`enter_E`) and A only from C reading 0 (`enter_A`), all three moving left. So the machine halts exactly at
`0 E>0`, that is at `0 0 A>1`, that is at `0 0 1 C>0` (`halt_E`, `halt_A`, `halt_C`).

Written by a script from the table; each theorem is checked by the kernel.
-/

namespace H101395

open TM

/-- F reading 0 halts at once. -/
theorem halt_F (L R : Tape) :
    ∃ c, steps 0 ⟨app [] L, app [false] R, .F⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `0 E>0` halts: E writes 1 and steps left onto a 0 in state F. -/
theorem halt_E (L R : Tape) :
    ∃ c, steps 1 ⟨app [false] L, app [false] R, .E⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `0 0 A>1` halts two steps later. -/
theorem halt_A (L R : Tape) :
    ∃ c, steps 2 ⟨app [false, false] L, app [true] R, .A⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `0 0 1 C>0` halts three steps later. -/
theorem halt_C (L R : Tape) :
    ∃ c, steps 3 ⟨app [true, false, false] L, app [false] R, .C⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- F is entered only from E reading 0. -/
theorem enter_F {c c' : Config} (h : step c = some c') (h' : c'.st = .F) :
    c.st = .E ∧ c.r 0 = false := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

/-- E is entered only from A reading 1. -/
theorem enter_E {c c' : Config} (h : step c = some c') (h' : c'.st = .E) :
    c.st = .A ∧ c.r 0 = true := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

/-- A is entered only from C reading 0. -/
theorem enter_A {c c' : Config} (h : step c = some c') (h' : c'.st = .A) :
    c.st = .C ∧ c.r 0 = false := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

end H101395
