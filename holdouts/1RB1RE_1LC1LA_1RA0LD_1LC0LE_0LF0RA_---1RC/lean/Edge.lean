import EdgeCert

/-!
# A halt can only happen at the left edge

A closed tape language from windows of four cells (`EdgeCert.lean`, found by `tools/py/bbtools/ctl.py`, checked
here by `decide` in the kernel) covers every configuration of the run from blank tape (`reach_inv`).  In it, every
configuration where the halting transition F0 can fire has only blank tape to the left of the head (left automaton
state 18, the window `####`), so the machine halts from blank tape exactly when F reads a 0 with nothing but blank
tape to its left (`halts_iff_edge`).  The shared library states this for the right side only; the left-side
version is proved here.
-/

namespace H132695

open TM

/-- The left automaton states that accept only the blank tape. -/
def certBL : List Nat := [18]

/-- Every abstract configuration where a halting transition can fire has its left state in `B`. -/
def haltsBlankL (S : List (St × Nat × Nat)) (B : List Nat) : Bool :=
  S.all (fun a => (certR.pops a.2.2).all (fun p => (trans a.1 p.1).isSome || decide (a.2.1 ∈ B)))

theorem cert_closed : TM.CTL.closed trans certL certR certS = true := by decide +kernel

theorem cert_starts : TM.CTL.starts certL certR certS St.A = true := by decide +kernel

theorem cert_blankOnlyL : TM.CTL.blankOnly certL certBL = true := by decide +kernel

theorem cert_haltsBlankL : haltsBlankL certS certBL = true := by decide +kernel

/-- Every configuration of the run from blank tape is in the language. -/
theorem reach_inv {n : Nat} {c : Config} (h : steps n init = some c) : TM.CTL.Inv certL certR certS c :=
  TM.CTL.reach trans cert_closed cert_starts h

/-- Every halt from blank tape happens in state F with blank tape left of the head. -/
theorem halt_at_edge {n : Nat} {c : Config} (h : steps n init = some c) (hs : step c = none) :
    c.st = .F ∧ c.l = blank := by
  obtain ⟨ql, qr, hmem, hl, hr⟩ := reach_inv h
  obtain ⟨⟨x, qr'⟩, hp, hx, _⟩ := hr.pop
  have hH := cert_haltsBlankL
  simp only [haltsBlankL, List.all_eq_true] at hH
  have h1 := hH _ hmem _ hp
  simp only at hx h1
  have hst := (step_none_iff c).1 hs
  refine ⟨hst.1, ?_⟩
  have hnone : trans c.st x = none := by
    rw [← hx, hst.1, hst.2]; rfl
  rw [hnone] at h1
  simp only [Option.isSome_none, Bool.false_or, decide_eq_true_eq] at h1
  exact hl.blank_of_blankOnly cert_blankOnlyL h1

/-- The machine halts from blank tape exactly when F reads a 0 with only blank tape to its left. -/
theorem halts_iff_edge :
    HaltsFromBlank ↔ ∃ n c, steps n init = some c ∧ c.st = .F ∧ c.r 0 = false ∧ c.l = blank := by
  constructor
  · rintro ⟨n, c, h, hs⟩
    exact ⟨n, c, h, (halt_at_edge h hs).1, ((step_none_iff c).1 hs).2, (halt_at_edge h hs).2⟩
  · rintro ⟨n, c, h, hF, h0, _⟩
    exact ⟨n, c, h, (step_none_iff c).2 ⟨hF, h0⟩⟩

end H132695
