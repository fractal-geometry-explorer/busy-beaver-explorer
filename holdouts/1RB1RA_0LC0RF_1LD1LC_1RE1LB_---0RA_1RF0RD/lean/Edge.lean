import EdgeCert

/-!
# A halt can only happen at the right edge

A closed tape language from windows of three cells (`EdgeCert.lean`, found by `tools/py/bbtools/ctl.py`, checked
here by `decide` in the kernel) covers every configuration of the run from blank tape (`reach_inv`).  In it, every
configuration where the halting transition E0 can fire has only blank tape after the head cell, so the machine halts
from blank tape exactly when E steps onto the blank region beyond the right end of the tape (`halts_iff_edge`).
-/

namespace H81504

open TM

theorem cert_closed : TM.CTL.closed trans certL certR certS = true := by decide +kernel

theorem cert_starts : TM.CTL.starts certL certR certS St.A = true := by decide +kernel

theorem cert_blankOnly : TM.CTL.blankOnly certR certB = true := by decide +kernel

theorem cert_haltsBlank : TM.CTL.haltsBlank trans certR certS certB = true := by decide +kernel

/-- Every configuration of the run from blank tape is in the language. -/
theorem reach_inv {n : Nat} {c : Config} (h : steps n init = some c) : TM.CTL.Inv certL certR certS c :=
  TM.CTL.reach trans cert_closed cert_starts h

/-- Every halt from blank tape happens in state E with blank tape from the head onward. -/
theorem halt_at_edge {n : Nat} {c : Config} (h : steps n init = some c) (hs : step c = none) :
    c.st = .E ∧ c.r = blank := by
  have ht := TM.CTL.halt_tail_blank trans cert_blankOnly cert_haltsBlank (reach_inv h) hs
  obtain ⟨hE, h0⟩ := (step_none_iff c).1 hs
  refine ⟨hE, ?_⟩
  rw [← TM.CTL.cons_head_tail c.r, ht, h0]
  exact cons_false_blank

/-- The machine halts from blank tape exactly when E reaches the blank region at the right. -/
theorem halts_iff_edge : HaltsFromBlank ↔ ∃ n c, steps n init = some c ∧ c.st = .E ∧ c.r = blank := by
  constructor
  · rintro ⟨n, c, h, hs⟩
    exact ⟨n, c, h, halt_at_edge h hs⟩
  · rintro ⟨n, ⟨l, r, s⟩, h, hE, hr⟩
    simp only at hE hr
    subst hE hr
    exact ⟨n, _, h, rfl⟩

end H81504
