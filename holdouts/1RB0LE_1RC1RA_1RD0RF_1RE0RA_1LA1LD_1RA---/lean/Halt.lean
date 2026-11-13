import Machine

/-!
# 1RB0LE_1RC1RA_1RD0RF_1RE0RA_1LA1LD_1RA---: how a halt comes about

The only halting transition is F reading 1. F is entered only from C reading 1 (`enter_F`), C only from B reading
0 (`enter_C`) and B only from A reading 0 (`enter_B`), all moving right. So the machine halts exactly at `C>1 1`,
that is at `B>0 1 1`, that is at `A>0 0 1 1` (`halt_C`, `halt_B`, `halt_A`).

Written by a script from the table; each theorem is checked by the kernel.
-/

namespace H10690

open TM

/-- F reading 1 halts at once. -/
theorem halt_F (L R : Tape) :
    ∃ c, steps 0 ⟨app [] L, app [true] R, .F⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `C>1 1` halts: C writes 0 and steps right onto a 1 in state F. -/
theorem halt_C (L R : Tape) :
    ∃ c, steps 1 ⟨app [] L, app [true, true] R, .C⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `B>0 1 1` halts two steps later. -/
theorem halt_B (L R : Tape) :
    ∃ c, steps 2 ⟨app [] L, app [false, true, true] R, .B⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `A>0 0 1 1` halts three steps later. -/
theorem halt_A (L R : Tape) :
    ∃ c, steps 3 ⟨app [] L, app [false, false, true, true] R, .A⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- F is entered only from C reading 1. -/
theorem enter_F {c c' : Config} (h : step c = some c') (h' : c'.st = .F) :
    c.st = .C ∧ c.r 0 = true := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

/-- C is entered only from B reading 0. -/
theorem enter_C {c c' : Config} (h : step c = some c') (h' : c'.st = .C) :
    c.st = .B ∧ c.r 0 = false := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

/-- B is entered only from A reading 0. -/
theorem enter_B {c c' : Config} (h : step c = some c') (h' : c'.st = .B) :
    c.st = .A ∧ c.r 0 = false := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

end H10690
