import Machine

/-!
# 1RB0LC_1LC0RF_1LD1RC_1LA0RE_1LB1RD_---0RD: how a halt comes about

The only halting transition is F reading 0. F is entered only from B reading 1 (`enter_F`), so the machine halts
exactly at `B>1 0`. B is entered from A reading 0 and from E reading 0 (`enter_B`); E is entered only from D reading
1 (`enter_E`), and that way B always reads the 0 that D has just written (`via_E_safe`). So a halt needs `A>0 1 0`
(`halt_A`). A>0 followed by `1 1 0` moves two cells right and starts again (`achain`); this gives the whole
family `A>0 1 (1 0)^n 0` (`halt_chain`).

Written by a script from the table; each theorem is checked by the kernel.
-/

namespace H174142

open TM

/-- F reading 0 halts at once. -/
theorem halt_F (L R : Tape) :
    ∃ c, steps 0 ⟨app [] L, app [false] R, .F⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `B>1 0` halts: B writes 0 and steps right onto a 0 in state F. -/
theorem halt_B (L R : Tape) :
    ∃ c, steps 1 ⟨app [] L, app [true, false] R, .B⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- `A>0 1 0` halts two steps later. -/
theorem halt_A (L R : Tape) :
    ∃ c, steps 2 ⟨app [] L, app [false, true, false] R, .A⟩ = some c ∧ step c = none :=
  ⟨_, rfl, rfl⟩

/-- F is entered only from B reading 1. -/
theorem enter_F {c c' : Config} (h : step c = some c') (h' : c'.st = .F) :
    c.st = .B ∧ c.r 0 = true := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

/-- B is entered from A reading 0 or E reading 0. -/
theorem enter_B {c c' : Config} (h : step c = some c') (h' : c'.st = .B) :
    (c.st = .A ∧ c.r 0 = false) ∨ (c.st = .E ∧ c.r 0 = false) := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

/-- E is entered only from D reading 1. -/
theorem enter_E {c c' : Config} (h : step c = some c') (h' : c'.st = .E) :
    c.st = .D ∧ c.r 0 = true := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

/-- A is entered only from D reading 0. -/
theorem enter_A {c c' : Config} (h : step c = some c') (h' : c'.st = .A) :
    c.st = .D ∧ c.r 0 = false := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases h0 : r 0 <;> simp [step, TM.step, trans, h0] at h <;> (try subst h) <;> simp_all

/-- The way into B through E is safe: `D>1 0` goes to E, which writes 1 and steps back left onto the 0 that D has
just written, so B reads 0 and does not halt. -/
theorem via_E_safe (L R : Tape) :
    ∃ c, steps 2 ⟨app [] L, app [true, false] R, .D⟩ = some c ∧ c.st = .B ∧ c.r 0 = false :=
  ⟨_, rfl, rfl, rfl⟩

/-- `A>0 1 1 0` becomes `1 0 A>0 1` in four steps (A, B, F, D): A walks right over `1 0` pairs. -/
theorem achain (n : Nat) (L R : Tape) :
    steps (4 * n) ⟨L, cons false (cons true (rep n [true, false] R)), .A⟩ =
      some ⟨rep n [false, true] L, cons false (cons true R), .A⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    have h1 : steps 4 ⟨L, cons false (cons true (rep (n + 1) [true, false] R)), .A⟩ =
        some ⟨app [false, true] L, cons false (cons true (rep n [true, false] R)), .A⟩ := rfl
    have h2 := steps_seq trans h1 (ih (app [false, true] L))
    rw [rep_app_comm] at h2
    exact steps_congr trans (by omega) h2

/-- The whole halting family: `A>0 1 (1 0)^n 0` halts, for every n. -/
theorem halt_chain (n : Nat) (L R : Tape) :
    ∃ c, steps (4 * n + 2) ⟨L, cons false (cons true (rep n [true, false] (cons false R))), .A⟩ = some c ∧
      step c = none := by
  obtain ⟨c, h1, h2⟩ := halt_A (rep n [false, true] L) R
  exact ⟨c, steps_seq trans (achain n L (cons false R)) h1, h2⟩

end H174142
