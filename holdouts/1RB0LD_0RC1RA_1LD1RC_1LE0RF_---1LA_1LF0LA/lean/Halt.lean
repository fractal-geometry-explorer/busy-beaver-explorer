import Machine

/-!
# 1RB0LD_0RC1RA_1LD1RC_1LE0RF_---1LA_1LF0LA: how a halt comes about

The only halting transition is E reading 0. E is entered only from D reading 0 (`enter_E`), which writes 1 and
steps left, so the machine halts exactly at `0 D>0` (`halt_D`). D is entered from A reading 1 and C reading 0, both
moving left (`enter_D`), which gives `0 0 A>1` and `0 0 C>0` (`halt_A`, `halt_C`).

Written by a script from the table; each theorem is checked by the kernel.
-/

namespace H137602

open TM

/-- E reading 0 halts at once. -/
theorem halt_E (L R : Tape) :
    ∃ c, steps 0 ⟨app [] L, app [false] R, .E⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `0 D>0` halts: D writes 1 and steps left onto a 0 in state E. -/
theorem halt_D (L R : Tape) :
    ∃ c, steps 1 ⟨app [false] L, app [false] R, .D⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `0 0 A>1` halts two steps later. -/
theorem halt_A (L R : Tape) :
    ∃ c, steps 2 ⟨app [false, false] L, app [true] R, .A⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `0 0 C>0` halts two steps later. -/
theorem halt_C (L R : Tape) :
    ∃ c, steps 2 ⟨app [false, false] L, app [false] R, .C⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- E is entered only from D reading 0. -/
theorem enter_E {c c' : Config} (h : step c = some c') (h' : c'.st = .E) :
    c.st = .D ∧ c.r 0 = false := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

/-- D is entered from A reading 1 or C reading 0. -/
theorem enter_D {c c' : Config} (h : step c = some c') (h' : c'.st = .D) :
    (c.st = .A ∧ c.r 0 = true) ∨ (c.st = .C ∧ c.r 0 = false) := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

end H137602
