import Machine

/-!
# 1RB0LA_1RC---_1RD1RA_0RE1LC_1LF0RF_1LD0RC: how a halt comes about

The only halting transition is B reading 1, and B is entered only from A reading 0 (`enter_B`), so the machine
halts exactly at `A>0 1`. A is entered from A reading 1 (moving left, which leaves a 0 behind it) and from C
reading 1 (moving right) (`enter_A`); the second way gives the pattern `C>1 0 1` (`halt_C`).

Written by a script from the table; each theorem is checked by the kernel.
-/

namespace H76289

open TM

/-- B reading 1 halts at once. -/
theorem halt_B (L R : Tape) :
    ∃ c, steps 0 ⟨app [] L, app [true] R, .B⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `A>0 1` halts: A writes 1 and steps right onto a 1 in state B. -/
theorem halt_A (L R : Tape) :
    ∃ c, steps 1 ⟨app [] L, app [false, true] R, .A⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `C>1 0 1`: C steps right onto an isolated 0 in state A; halt 3 steps after C. -/
theorem halt_C (L R : Tape) :
    ∃ c, steps 2 ⟨app [] L, app [true, false, true] R, .C⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- B is entered only from A reading 0. -/
theorem enter_B {c c' : Config} (h : step c = some c') (h' : c'.st = .B) :
    c.st = .A ∧ c.r 0 = false := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

/-- A is entered from A reading 1 or C reading 1. -/
theorem enter_A {c c' : Config} (h : step c = some c') (h' : c'.st = .A) :
    (c.st = .A ∧ c.r 0 = true) ∨ (c.st = .C ∧ c.r 0 = true) := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

end H76289
