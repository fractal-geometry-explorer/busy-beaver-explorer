import Blank

/-!
# Where a halt can come from

The machine stops only on E reading 1 (`step_none_iff`).  E is entered only from C on a 0, moving right, so E reads
the cell C had on its right.  C is entered from B on a 0 moving left (B writes that 0, so E would read 0) or from F
on a 1 moving right.  So a halt needs, two steps before, the head in state F on `1 0 1`; and F is entered only from
E on a 0 (moving right).  The run C0 E0 F1 C0 E0 F1 ... is a sweep to the right over `001 001 ...`; a halt is that
sweep meeting `0 1` where it expects `0 0`.
-/

namespace H63822

open TM

theorem into_E {c c' : Config} (h : step c = some c') (hs : c'.st = .E) :
    c.st = .C ∧ c.r 0 = false ∧ c'.r = tail c.r := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases hr : r 0 <;> simp [step, TM.step, trans, hr] at h <;> subst h <;> simp_all

theorem into_C_one {c c' : Config} (h : step c = some c') (hs : c'.st = .C) (h1 : c'.r 1 = true) :
    c.st = .F ∧ c.r 0 = true ∧ c'.r = tail c.r := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases hr : r 0 <;> simp [step, TM.step, trans, hr] at h <;> subst h <;> simp_all [cons]

theorem into_F {c c' : Config} (h : step c = some c') (hs : c'.st = .F) :
    c.st = .E ∧ c.r 0 = false ∧ c'.r = tail c.r ∧ c'.l 0 = true := by
  obtain ⟨l, r, s⟩ := c
  cases s <;> cases hr : r 0 <;> simp [step, TM.step, trans, hr] at h <;> subst h <;> simp_all

/-- Two steps before a halt the head is in state F on `1 0 1`, and one step before that in E on `0 1 0 1`. -/
theorem halt_needs {c₀ c₁ c₂ c₃ : Config} (h₁ : step c₀ = some c₁) (h₂ : step c₁ = some c₂)
    (h₃ : step c₂ = some c₃) (hh : step c₃ = none) :
    c₁.st = .F ∧ c₁.r 0 = true ∧ c₁.r 1 = false ∧ c₁.r 2 = true ∧
    c₀.st = .E ∧ c₀.r 0 = false ∧ c₀.r 1 = true ∧ c₀.r 2 = false ∧ c₀.r 3 = true := by
  have hE := (step_none_iff c₃).1 hh
  obtain ⟨d1, d2, d3⟩ := into_E h₃ hE.1
  have e1 : c₂.r 1 = true := by rw [← hE.2, d3]; rfl
  obtain ⟨f1, f2, f3⟩ := into_C_one h₂ d1 e1
  obtain ⟨g1, g2, g3, _⟩ := into_F h₁ f1
  have k1 : c₁.r 1 = false := by have := d2; rw [f3] at this; exact this
  have k2 : c₁.r 2 = true := by have := e1; rw [f3] at this; exact this
  refine ⟨f1, f2, k1, k2, g1, g2, ?_, ?_, ?_⟩
  · have := f2; rw [g3] at this; exact this
  · have := k1; rw [g3] at this; exact this
  · have := k2; rw [g3] at this; exact this

end H63822
