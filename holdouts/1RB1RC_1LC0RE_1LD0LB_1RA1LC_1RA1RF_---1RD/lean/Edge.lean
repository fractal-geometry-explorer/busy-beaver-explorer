import EdgeCert

/-!
# A halt can only happen at the right edge

A closed tape language (`EdgeCert.lean`, found by `py/fctl.py`) covers every configuration of the run from blank tape
(`reach_inv`).  Its closure and its list of halting configurations are checked by `native_decide` (5,545 abstract
configurations: too much for `decide` in the kernel), the start and the blank-only states by the kernel.  The automata
remember, for each side of the head, the six nearest cells and the parity of the distance to the next 0: the tape of
this machine is read in pairs (`01` and `11`), and plain windows lose the alignment of the pairs inside a long run of
1s.  In the language, the only configuration where the halting transition F0 can fire has blank tape from the head
onward, so the machine halts from blank tape exactly when F steps onto the blank region beyond the far (right) end
of the tape (`halts_iff_edge`).
-/

namespace H136824

open TM

theorem cert_closed : TM.CTL.closed trans certL certR certS = true := by native_decide

theorem cert_starts : TM.CTL.starts certL certR certS St.A = true := by decide +kernel

theorem cert_blankOnly : TM.CTL.blankOnly certR certB = true := by decide +kernel

theorem cert_haltsBlank : TM.CTL.haltsBlank trans certR certS certB = true := by native_decide

/-- Every configuration of the run from blank tape is in the language. -/
theorem reach_inv {n : Nat} {c : Config} (h : steps n init = some c) : TM.CTL.Inv certL certR certS c :=
  TM.CTL.reach trans cert_closed cert_starts h

/-- Every halt from blank tape happens in state F with blank tape from the head onward. -/
theorem halt_at_edge {n : Nat} {c : Config} (h : steps n init = some c) (hs : step c = none) :
    c.st = .F ∧ c.r = blank := by
  have ht := TM.CTL.halt_tail_blank trans cert_blankOnly cert_haltsBlank (reach_inv h) hs
  obtain ⟨hF, h0⟩ := (step_none_iff c).1 hs
  refine ⟨hF, ?_⟩
  rw [← TM.CTL.cons_head_tail c.r, ht, h0]
  exact cons_false_blank

/-- The machine halts from blank tape exactly when F reaches the blank region at the right. -/
theorem halts_iff_edge : HaltsFromBlank ↔ ∃ n c, steps n init = some c ∧ c.st = .F ∧ c.r = blank := by
  constructor
  · rintro ⟨n, c, h, hs⟩
    exact ⟨n, c, h, halt_at_edge h hs⟩
  · rintro ⟨n, ⟨l, r, s⟩, h, hF, hr⟩
    simp only at hF hr
    subst hF hr
    exact ⟨n, _, h, rfl⟩

end H136824
