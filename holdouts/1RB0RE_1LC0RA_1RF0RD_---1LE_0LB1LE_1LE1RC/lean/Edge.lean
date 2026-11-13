import Blank
import EdgeCert

/-!
# A halt can only happen at the right edge

A closed tape language (`EdgeCert.lean`, found by `tools/py/bbtools/ctl.py` from windows of 4 cells, checked here
by `decide` in the kernel) covers every configuration of the run from blank tape (`reach_inv`).  In it, every
abstract configuration where the halting transition D0 can fire has blank tape after the head cell, and past the
head two 0s in a row occur only in the blank region beyond everything written (`right_no_double_zero`).  So the
machine halts from blank tape exactly when it is in state D with nothing but blank tape from the head onward
(`halts_iff_edge`): at the right end of the written tape.
-/

namespace H127123

open TM

theorem cert_closed : TM.CTL.closed trans certL certR certS = true := by decide +kernel

theorem cert_starts : TM.CTL.starts certL certR certS St.A = true := by decide +kernel

theorem cert_blankOnly : TM.CTL.blankOnly certR certB = true := by decide +kernel

theorem cert_haltsBlank : TM.CTL.haltsBlank trans certR certS certB = true := by decide +kernel

theorem cert_noDoubleZero : TM.CTL.noDoubleZero certR certS certRt certB = true := by decide +kernel

/-- Every configuration of the run from blank tape is in the language. -/
theorem reach_inv {n : Nat} {c : Config} (h : steps n init = some c) : TM.CTL.Inv certL certR certS c :=
  TM.CTL.reach trans cert_closed cert_starts h

/-- Past the head cell, two 0s in a row are followed only by 0s. -/
theorem right_no_double_zero {n : Nat} {c : Config} (h : steps n init = some c) {i : Nat}
    (h0 : c.r (i + 1) = false) (h1 : c.r (i + 2) = false) : ∀ j, i + 1 ≤ j → c.r j = false :=
  TM.CTL.no_double_zero cert_blankOnly cert_noDoubleZero (reach_inv h) h0 h1

/-- Every halt from blank tape happens in state D with blank tape from the head onward. -/
theorem halt_at_edge {n : Nat} {c : Config} (h : steps n init = some c) (hs : step c = none) :
    c.st = .D ∧ c.r = blank := by
  have ht := TM.CTL.halt_tail_blank trans cert_blankOnly cert_haltsBlank (reach_inv h) hs
  obtain ⟨hS, h0⟩ := (step_none_iff c).1 hs
  refine ⟨hS, ?_⟩
  rw [← TM.CTL.cons_head_tail c.r, ht, h0]
  exact cons_false_blank

/-- The machine halts from blank tape exactly when D reaches the blank region at the right. -/
theorem halts_iff_edge : HaltsFromBlank ↔ ∃ n c, steps n init = some c ∧ c.st = .D ∧ c.r = blank := by
  constructor
  · rintro ⟨n, c, h, hs⟩
    exact ⟨n, c, h, halt_at_edge h hs⟩
  · rintro ⟨n, ⟨l, r, s⟩, h, hS, hr⟩
    simp only at hS hr
    subst hS hr
    exact ⟨n, _, h, rfl⟩

end H127123
