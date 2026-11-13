import Machine

/-!
# 1RB0LE_0LC0RF_1LD1LC_1RA0RD_0LA1LA_1RD---: how a halt comes about

The only halting transition is F reading 1. F is entered only from B reading 1 (`enter_F`) and B only from A
reading 0 (`enter_B`), so the machine halts exactly at `A>0 1 1` (`halt_A`). A is entered from D reading 0 (moving
right) and from E (moving left, `enter_A`); E is entered only from A reading 1 (`enter_E`), which leaves a 0 that
the following F reads, so the way through E never halts (`via_E0_safe`, `via_E1_safe`). That leaves
`D>0 0 1 1` (`halt_D`).

Written by a script from the table; each theorem is checked by the kernel.
-/

namespace H52729

open TM

/-- F reading 1 halts at once. -/
theorem halt_F (L R : Tape) :
    ∃ c, steps 0 ⟨app [] L, app [true] R, .F⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `B>1 1` halts: B writes 0 and steps right onto a 1 in state F. -/
theorem halt_B (L R : Tape) :
    ∃ c, steps 1 ⟨app [] L, app [true, true] R, .B⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `A>0 1 1` halts two steps later. -/
theorem halt_A (L R : Tape) :
    ∃ c, steps 2 ⟨app [] L, app [false, true, true] R, .A⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `D>0 0 1 1` halts three steps later. -/
theorem halt_D (L R : Tape) :
    ∃ c, steps 3 ⟨app [] L, app [false, false, true, true] R, .D⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- F is entered only from B reading 1. -/
theorem enter_F {c c' : Config} (h : step c = some c') (h' : c'.st = .F) :
    c.st = .B ∧ c.r 0 = true := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

/-- B is entered only from A reading 0. -/
theorem enter_B {c c' : Config} (h : step c = some c') (h' : c'.st = .B) :
    c.st = .A ∧ c.r 0 = false := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

/-- A is entered from D reading 0, E reading 0 or E reading 1. -/
theorem enter_A {c c' : Config} (h : step c = some c') (h' : c'.st = .A) :
    (c.st = .D ∧ c.r 0 = false) ∨ (c.st = .E ∧ c.r 0 = false) ∨ (c.st = .E ∧ c.r 0 = true) := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

/-- E is entered only from A reading 1. -/
theorem enter_E {c c' : Config} (h : step c = some c') (h' : c'.st = .E) :
    c.st = .A ∧ c.r 0 = true := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

/-- The way into A through E is safe (1): `0 0 A>1` goes A, E, A and reaches B on the 0 that E wrote. -/
theorem via_E0_safe (L R : Tape) :
    ∃ c, steps 3 ⟨app [false, false] L, app [true] R, .A⟩ = some c ∧ c.st = .B ∧ c.r 0 = false :=
  ⟨_, rfl, rfl, rfl⟩

/-- The way into A through E is safe (2): `0 1 A>1` goes A, E, A, B and reaches F on the 0 that the first A wrote. -/
theorem via_E1_safe (L R : Tape) :
    ∃ c, steps 4 ⟨app [true, false] L, app [true] R, .A⟩ = some c ∧ c.st = .F ∧ c.r 0 = false :=
  ⟨_, rfl, rfl, rfl⟩

end H52729
