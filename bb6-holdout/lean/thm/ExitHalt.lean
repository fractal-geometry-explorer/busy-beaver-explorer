import ExitTheorem
import BB6.HaltStretch

/-!
# A halt from a loop state needs a contact after the exit

`exit_stretch` with `halt_after_rounds`: if the machine halts from a loop state (walls at a, b, c, width E, parities
and gaps ≥ 390 as in `exit_stretch`), then it first gets through the close-free stretch to the exit event
(`ExitEvent`: a clean tape, a break of the end-meeting chain, or a loop state again after a full pass), and the mark
model, run on from there, reaches a stuck configuration: a close at the right end or an interior contact
(`stuck_cases`).
-/

namespace BB6
open BB6.Sym

/-- **A halt from a loop state needs a contact after the exit.** -/
theorem exit_halt_needs_contact (a b c E : Nat) (ha : a % 2 = 1) (hb : b % 2 = 0) (hc : c % 2 = 1) (hE : E % 2 = 0)
    (h1 : 390 ≤ a) (h2 : a + 390 ≤ b) (h3 : b + 390 ≤ c) (h4 : c + 390 ≤ E) (T : Nat)
    (hT : steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E) = none) :
    ∃ n ms' W', roundsZ 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E = .newRound ms' W' ∧
      (∀ d ∈ meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E, 3 ≤ d) ∧
      ExitEvent n (meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E) ms' W' ∧
      ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t) := by
  obtain ⟨n, -, ms', W', -, hr, hm, he⟩ := exit_stretch a b c E ha hb hc hE h1 h2 h3 h4
  have hwf : roundWF [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] E := by
    simp only [roundWF, rightOK, mval, mlen, iff_true]
    omega
  have hG : noG [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] := by
    intro m hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp
  obtain ⟨-, -, -, -, -, t, ht, htw, hts⟩ := halt_after_rounds 1000 n _ E ms' W' hwf hG hr T hT
  exact ⟨n, ms', W', hr, hm, he, t, ht, htw, stuck_cases hts⟩

#print axioms exit_halt_needs_contact

end BB6
