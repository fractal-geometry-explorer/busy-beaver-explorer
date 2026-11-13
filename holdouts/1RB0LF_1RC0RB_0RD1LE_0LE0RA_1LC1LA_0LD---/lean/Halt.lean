import Machine

/-!
# 1RB0LF_1RC0RB_0RD1LE_0LE0RA_1LC1LA_0LD---: how a halt comes about

The only halting transition is F reading 1. F is entered only from A reading 1 (`enter_F`), which writes 0 and
steps left, so the machine halts exactly at `1 A>1` (`halt_A`). A is entered from D reading 1 (moving right) and from
E reading 1 (moving left) (`enter_A`). The D way never halts, because F then reads the 0 that D has just written
(`via_D_safe`); the E way gives `1 1 E>1` (`halt_E`).

Written by a script from the table; each theorem is checked by the kernel.
-/

namespace H11596

open TM

/-- F reading 1 halts at once. -/
theorem halt_F (L R : Tape) :
    ∃ c, steps 0 ⟨app [] L, app [true] R, .F⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `1 A>1` halts: A writes 0 and steps left onto a 1 in state F. -/
theorem halt_A (L R : Tape) :
    ∃ c, steps 1 ⟨app [true] L, app [true] R, .A⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `1 1 E>1` halts two steps later. -/
theorem halt_E (L R : Tape) :
    ∃ c, steps 2 ⟨app [true, true] L, app [true] R, .E⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `1 1 1 C>1` halts three steps later. -/
theorem halt_C (L R : Tape) :
    ∃ c, steps 3 ⟨app [true, true, true] L, app [true] R, .C⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `1 1 1 D>0` halts three steps later. -/
theorem halt_D (L R : Tape) :
    ∃ c, steps 3 ⟨app [true, true, true] L, app [false] R, .D⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- F is entered only from A reading 1. -/
theorem enter_F {c c' : Config} (h : step c = some c') (h' : c'.st = .F) :
    c.st = .A ∧ c.r 0 = true := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

/-- A is entered from D reading 1 or E reading 1. -/
theorem enter_A {c c' : Config} (h : step c = some c') (h' : c'.st = .A) :
    (c.st = .D ∧ c.r 0 = true) ∨ (c.st = .E ∧ c.r 0 = true) := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

/-- E is entered from C reading 1 or D reading 0. -/
theorem enter_E {c c' : Config} (h : step c = some c') (h' : c'.st = .E) :
    (c.st = .C ∧ c.r 0 = true) ∨ (c.st = .D ∧ c.r 0 = false) := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

/-- The way into A through D is safe: `D>1 1` goes to A on the second 1, which steps back left in state F onto
the 0 that D has just written. -/
theorem via_D_safe (L R : Tape) :
    ∃ c, steps 2 ⟨app [] L, app [true, true] R, .D⟩ = some c ∧ c.st = .F ∧ c.r 0 = false :=
  ⟨_, rfl, rfl, rfl⟩

end H11596
