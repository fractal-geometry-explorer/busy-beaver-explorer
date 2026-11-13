import Machine

/-!
# 1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LF---_1LB1RF: how a halt comes about

The only halting transition is E reading 1. E is entered from C reading 1 and from D reading 0 (`enter_E`).
C is entered only from A reading 1 (`enter_C`), moving left, so A has just written 0 on the cell to C's right:
the way through C never halts (`via_C_safe`). D is entered only from B reading 1 (`enter_D`), so the machine halts
exactly when B reads 1 followed by `0 1` (`halt_B`).

Written by a script from the table; each theorem is checked by the kernel.
-/

namespace H31128

open TM

/-- E reading 1 halts at once. -/
theorem halt_E (L R : Tape) :
    ∃ c, steps 0 ⟨app [] L, app [true] R, .E⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `D>0 1` halts: D writes 1 and steps right onto a 1 in state E. -/
theorem halt_D (L R : Tape) :
    ∃ c, steps 1 ⟨app [] L, app [false, true] R, .D⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `B>1 0 1` halts three steps later. -/
theorem halt_B (L R : Tape) :
    ∃ c, steps 2 ⟨app [] L, app [true, false, true] R, .B⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `A>0 1 0 1` (A on a fresh cell at the left end, say) halts four steps later. -/
theorem halt_A (L R : Tape) :
    ∃ c, steps 3 ⟨app [] L, app [false, true, false, true] R, .A⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- E is entered from C reading 1 or D reading 0. -/
theorem enter_E {c c' : Config} (h : step c = some c') (h' : c'.st = .E) :
    (c.st = .C ∧ c.r 0 = true) ∨ (c.st = .D ∧ c.r 0 = false) := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

/-- C is entered only from A reading 1. -/
theorem enter_C {c c' : Config} (h : step c = some c') (h' : c'.st = .C) :
    c.st = .A ∧ c.r 0 = true := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

/-- D is entered only from B reading 1. -/
theorem enter_D {c c' : Config} (h : step c = some c') (h' : c'.st = .D) :
    c.st = .B ∧ c.r 0 = true := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

/-- The way into E through C is safe: after `x A>1`, if C reads `x = 1` then E reads the 0 that A has just
written, so it does not halt. -/
theorem via_C_safe (L R : Tape) :
    ∃ c, steps 2 ⟨app [true] L, app [true] R, .A⟩ = some c ∧ c.st = .E ∧ c.r 0 = false :=
  ⟨_, rfl, rfl, rfl⟩

end H31128
