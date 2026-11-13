import Blank

/-!
# Where a halt can come from

The machine stops only on E reading 1 (`step_none_iff` in `Blank.lean`).  Going back four steps: E is entered only
from D on a 0 (moving right), D on a 0 next to a 1 only from C on a 0 (moving right; the other way into D, F on a 1
moving left, leaves a 0 on D's right), C only from B on a 0 and B only from A on a 0, all moving right.  So a halt
needs the head in state A on four 0s in a row followed by a 1: `A> 0 0 0 0 1`.
-/

namespace H180268

open TM

theorem into_E {c c' : Config} (h : step c = some c') (hs : c'.st = .E) :
    c.st = .D ∧ c.r 0 = false ∧ c'.r = tail c.r := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases hr : r 0 <;> simp [step, TM.step, trans, hr] at h <;> subst h <;> simp_all

theorem into_D_one {c c' : Config} (h : step c = some c') (hs : c'.st = .D) (h1 : c'.r 1 = true) :
    c.st = .C ∧ c.r 0 = false ∧ c'.r = tail c.r := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases hr : r 0 <;> simp [step, TM.step, trans, hr] at h <;> subst h <;> simp_all [cons]

theorem into_C {c c' : Config} (h : step c = some c') (hs : c'.st = .C) :
    c.st = .B ∧ c.r 0 = false ∧ c'.r = tail c.r := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases hr : r 0 <;> simp [step, TM.step, trans, hr] at h <;> subst h <;> simp_all

theorem into_B {c c' : Config} (h : step c = some c') (hs : c'.st = .B) :
    c.st = .A ∧ c.r 0 = false ∧ c'.r = tail c.r := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases hr : r 0 <;> simp [step, TM.step, trans, hr] at h <;> subst h <;> simp_all

/-- Four steps before a halting configuration the head is in state A on `0 0 0 0 1`. -/
theorem halt_needs_four_zeros {c₀ c₁ c₂ c₃ c₄ : Config} (h₁ : step c₀ = some c₁) (h₂ : step c₁ = some c₂)
    (h₃ : step c₂ = some c₃) (h₄ : step c₃ = some c₄) (hh : step c₄ = none) :
    c₀.st = .A ∧ c₀.r 0 = false ∧ c₀.r 1 = false ∧ c₀.r 2 = false ∧ c₀.r 3 = false ∧ c₀.r 4 = true := by
  have hE := (step_none_iff c₄).1 hh
  obtain ⟨d1, d2, d3⟩ := into_E h₄ hE.1
  have e4 : c₃.r 1 = true := by rw [← hE.2, d3]; rfl
  obtain ⟨c1, c2, c3⟩ := into_D_one h₃ d1 e4
  obtain ⟨b1, b2, b3⟩ := into_C h₂ c1
  obtain ⟨a1, a2, a3⟩ := into_B h₁ b1
  refine ⟨a1, a2, ?_, ?_, ?_, ?_⟩
  · have := b2; rw [a3] at this; exact this
  · have := c2; rw [b3, a3] at this; exact this
  · have := d2; rw [c3, b3, a3] at this; exact this
  · have := e4; rw [c3, b3, a3] at this; exact this

end H180268
