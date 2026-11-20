import EdgeCert

/-!
# A halt can only happen at the left edge

A closed tape language from windows of three cells (`EdgeCert.lean`, found by `tools/py/bbtools/ctl.py`, checked
here by `decide` in the kernel) covers every configuration of the run from blank tape (`reach_inv`).  In it, every
configuration where the halting transition C0 can fire has only blank tape left of the head, so the machine halts
from blank tape exactly when C reads a 0 with nothing but blank tape on its left (`halts_iff_left_edge`).

The tape of the run is `0^∞ 1^N W`: a run of 1s on the left (a visit counter, crossed by D and A, `Shifts.lean`) and
an irregular word W next to it.  The head reaches the blank cells left of the run in C only if W has eaten the whole
run, so this is the formal half of "it halts iff W eats the whole run between two visits".
-/

namespace H92364

open TM

/-- The left automaton's states that accept only the blank tape (state 8 is the window `###`). -/
def certBL : List Nat := [8]

theorem cert_closed : TM.CTL.closed trans certL certR certS = true := by decide +kernel

theorem cert_starts : TM.CTL.starts certL certR certS St.A = true := by decide +kernel

theorem cert_blankOnlyL : TM.CTL.blankOnly certL certBL = true := by decide +kernel

theorem cert_haltsBlankL : TM.CTL.haltsBlankL trans certR certS certBL = true := by decide +kernel

/-- Every configuration of the run from blank tape is in the language. -/
theorem reach_inv {n : Nat} {c : Config} (h : steps n init = some c) : TM.CTL.Inv certL certR certS c :=
  TM.CTL.reach trans cert_closed cert_starts h

/-- Every halt from blank tape happens in state C reading 0 with blank tape left of the head. -/
theorem halt_at_left_edge {n : Nat} {c : Config} (h : steps n init = some c) (hs : step c = none) :
    c.st = .C ∧ c.r 0 = false ∧ c.l = blank := by
  have hl := TM.CTL.halt_left_blank trans cert_blankOnlyL cert_haltsBlankL (reach_inv h) hs
  obtain ⟨hC, h0⟩ := (step_none_iff c).1 hs
  exact ⟨hC, h0, hl⟩

/-- The machine halts from blank tape exactly when C reads a 0 with only blank tape on its left. -/
theorem halts_iff_left_edge :
    HaltsFromBlank ↔ ∃ n c, steps n init = some c ∧ c.st = .C ∧ c.r 0 = false ∧ c.l = blank := by
  constructor
  · rintro ⟨n, c, h, hs⟩
    exact ⟨n, c, h, halt_at_left_edge h hs⟩
  · rintro ⟨n, ⟨l, r, s⟩, h, hC, h0, _⟩
    simp only at hC h0
    subst hC
    refine ⟨n, _, h, ?_⟩
    exact (step_none_iff _).2 ⟨rfl, h0⟩

end H92364
