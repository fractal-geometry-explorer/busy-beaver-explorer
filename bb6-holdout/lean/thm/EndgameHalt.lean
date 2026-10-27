import EndgameTheorem
import BB6.HaltStretch

/-!
# A halt from a pass start needs a contact after the endgame

`endgame_no_close` with `halt_after_rounds`: if the machine halts from a phase-0 pass start (the hypotheses of
`endgame_no_close`: R ≤ 4096 even and outside the closing set, gaps ≥ 448), then the run first gets through the
certified stretch, on which no end meeting comes within distance 2, and the mark model, run on from the round start
where the stretch ends, reaches a stuck configuration: a close at the right end or an interior contact
(`stuck_cases`).
-/

namespace BB6
open BB6.Sym

theorem endgame_halt_needs_contact (R : Nat) (hR : R % 2 = 0) (hR2 : 2 ≤ R) (hR4 : R ≤ 4096)
    (hS : closingSet.contains R = false) (a b E : Nat) (ha : a % 2 = 1) (hb : b % 2 = 0) (hE : E % 2 = 0)
    (h1 : 448 ≤ a) (h2 : a + 448 ≤ b) (h3 : b + 448 + R + 1 ≤ E) (T : Nat)
    (hT : steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E) = none) :
    ∃ n ms' W', roundsZ 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E = .newRound ms' W' ∧
      (∀ d ∈ meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E, 3 ≤ d) ∧
      ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t) := by
  obtain ⟨n, -, ms', W', -, hr, hm⟩ := endgame_no_close R hR hR2 hR4 hS a b E ha hb hE h1 h2 h3
  have hwf : roundWF [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E := by
    simp only [roundWF, rightOK, mval, mlen, iff_true]
    omega
  have hG : noG [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] := by
    intro m hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp
  obtain ⟨-, -, -, -, -, t, ht, htw, hts⟩ := halt_after_rounds 1000 n _ E ms' W' hwf hG hr T hT
  exact ⟨n, ms', W', hr, hm, t, ht, htw, stuck_cases hts⟩

#print axioms endgame_halt_needs_contact

end BB6
