import Machine

/-!
# 1RB---_0RC1RD_1LD1LF_1LE0RB_1RF1LD_1LA0LC: how a halt comes about

The only halting transition is A reading 1, and A is entered only from F reading 0 (`enter_A`), so the
machine halts exactly when F reads a 0 whose left neighbour is 1 (`halt_F`). F is entered from C reading 1 and
from E reading 0 (`enter_F`), which gives the two ways in: B reading an isolated 0 (`halt_B`) and E reading the first
of two 0s (`halt_E`).

Written by a script from the table; each theorem is checked by the kernel.
-/

namespace H2968

open TM

/-- A reading 1 halts at once. -/
theorem halt_A (L R : Tape) :
    ∃ c, steps 0 ⟨app [] L, app [true] R, .A⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `1 F>0` halts: F writes 1 and steps left onto the 1, in state A. -/
theorem halt_F (L R : Tape) :
    ∃ c, steps 1 ⟨app [true] L, app [false] R, .F⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `E>0 0` halts: E writes 1 and steps right; F reads the next 0 and steps back onto that 1. -/
theorem halt_E (L R : Tape) :
    ∃ c, steps 2 ⟨app [] L, app [false, false] R, .E⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `1 B>0 1`: an isolated 0 met by B halts four steps later. -/
theorem halt_B (L R : Tape) :
    ∃ c, steps 3 ⟨app [true] L, app [false, true] R, .B⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- A is entered only from F reading 0. -/
theorem enter_A {c c' : Config} (h : step c = some c') (h' : c'.st = .A) :
    c.st = .F ∧ c.r 0 = false := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

/-- F is entered from C reading 1 or E reading 0. -/
theorem enter_F {c c' : Config} (h : step c = some c') (h' : c'.st = .F) :
    (c.st = .C ∧ c.r 0 = true) ∨ (c.st = .E ∧ c.r 0 = false) := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

end H2968
