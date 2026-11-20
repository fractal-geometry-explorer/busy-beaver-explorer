import Blank

/-!
# 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF: the only way to halt

The halting transition is E1, and E is entered only by D0 (write 1, move left). D is entered by B1 (write 0, move
right), which leaves a 0 to the left of the head, or by C0 (write 1, move left); C is entered only by B0 (write 1, move
left). So the last four steps of a halting run start in state B reading 0 with the cells 0, 0, 1 to its left
(`halt_needs_pattern`): an internal run of exactly three 0s, entered by B from its right end.

This is the condition the accelerated engine of `coq/` checks at every raw step (it stops on D reading 0 with a 1 to its
left); all of the engine's macro rules were checked to contain no such step.
-/

namespace H123029

open TM

/-- E is entered only by D reading 0, and E then reads the cell that was left of D. -/
theorem enter_E {c c' : Config} (h : step c = some c') (hE : c'.st = .E) :
    c.st = .D ∧ c.r 0 = false ∧ c'.r 0 = c.l 0 := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases hr : r 0 <;>
    simp [step, TM.step, trans, hr] at h <;> subst h <;> simp_all

/-- D is entered by B reading 1 (then the cell left of the head is 0) or by C reading 0 (moving left). -/
theorem enter_D {c c' : Config} (h : step c = some c') (hD : c'.st = .D) :
    (c.st = .B ∧ c.r 0 = true ∧ c'.l 0 = false) ∨ (c.st = .C ∧ c.r 0 = false ∧ c'.r 0 = c.l 0 ∧ c'.l 0 = c.l 1) := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases hr : r 0 <;>
    simp [step, TM.step, trans, hr] at h <;> subst h <;> simp_all [cons, tail]

/-- C is entered only by B reading 0 (moving left). -/
theorem enter_C {c c' : Config} (h : step c = some c') (hC : c'.st = .C) :
    c.st = .B ∧ c.r 0 = false ∧ c'.r 0 = c.l 0 ∧ c'.l 0 = c.l 1 ∧ c'.l 1 = c.l 2 := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases hr : r 0 <;>
    simp [step, TM.step, trans, hr] at h <;> subst h <;> simp_all [cons, tail]

/-- A halt comes four steps after B reads 0 with 0, 0, 1 to its left (nearest cell first). -/
theorem halt_needs_pattern {c c₁ c₂ c₃ : Config} (h₁ : step c = some c₁) (h₂ : step c₁ = some c₂)
    (h₃ : step c₂ = some c₃) (h₄ : step c₃ = none) :
    c.st = .B ∧ c.r 0 = false ∧ c.l 0 = false ∧ c.l 1 = false ∧ c.l 2 = true := by
  have hE : c₃.st = .E ∧ c₃.r 0 = true := (step_none_iff c₃).1 h₄
  obtain ⟨hD, hD0, hl⟩ := enter_E h₃ hE.1
  rcases enter_D h₂ hD with ⟨_, _, hB⟩ | ⟨hC, hC0, hr2, hl2⟩
  · -- entered from B1: the cell left of D is 0, so E reads 0
    rw [hE.2] at hl; rw [hB] at hl; exact absurd hl (by decide)
  · obtain ⟨hB, hB0, hr1, hl1, hl1'⟩ := enter_C h₁ hC
    refine ⟨hB, hB0, ?_, ?_, ?_⟩
    · rw [← hr1]; exact hC0
    · rw [← hl1, ← hr2]; exact hD0
    · rw [← hl1', ← hl2, ← hl, hE.2]

end H123029
