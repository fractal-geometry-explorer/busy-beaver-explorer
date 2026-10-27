import LoopTheorem
import BB6.HaltStretch

/-!
# A halt from a pass start needs a contact after the loop's end

`loop_stretch` with `halt_after_rounds`: if the machine halts from a phase-0 pass start whose gaps are all at least 448
(`PassStart448`), it first gets through the close-free stretch `loop_stretch` certifies, through p full passes, each
to a pass start whose gaps are again all at least 448, to the last of them, `ms₁ W₁` with right end R₁ = R/16^p and
left countdown L₁/64^p.  From there, either R₁ is in the closing set and the left countdown is in R₁'s class
(`InCloseClass`; then R³/L₁² ≤ 176³/256² at the first pass start, `sigma_through_passes`), and the mark model, run on
from `ms₁ W₁`, reaches a stuck configuration; or the run goes on close-free to where it leaves the loop (`LoopEnd`: an
end event at which it is not at a pass start with every gap at least 448 after a full pass), and the model reaches a
stuck configuration from there.  A stuck configuration is a close at the right end or an interior contact
(`stuck_cases`).  `loop_halt_sigma` is the σ bound: from a pass start with R³/L₁² > 176³/256² (log₂W > σ + 6.38), a
halt comes only after the run has left the loop.
-/

namespace BB6
open BB6.Sym

/-- A pass start with every gap at least 448 is a well-formed round start without gap marks. -/
theorem PassStart448.wf {ms : List Mark} {W R : Nat} (h : PassStart448 ms W R) : roundWF ms W ∧ noG ms := by
  obtain ⟨a, b, rfl, ha, hb, hW, hR, hR2, h1, h2, h3⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [roundWF, rightOK, mval, mlen, iff_true]
    omega
  · intro m hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

/-- **A halt from a pass start needs a contact after the loop's end.**  If the machine halts from a phase-0 pass start
with right end R and every gap at least 448, the mark model covers a close-free stretch from it (every end meeting at
distance at least 3) through p full passes to the last pass start `ms₁ W₁` with gaps again all at least 448 (right end
R₁ = R/16^p, left countdown L₁/64^p), and then either R₁ is in the closing set with the left countdown in its class,
R³/L₁² ≤ 176³/256² at the first pass start (`SigmaOK`), and the model reaches a stuck configuration from `ms₁ W₁`; or
the model covers a further close-free stretch to where the run leaves the loop (`LoopEnd`) and reaches a stuck
configuration from there: a close at the right end or an interior contact. -/
theorem loop_halt_needs_contact (R : Nat) (ms : List Mark) (W : Nat) (hP : PassStart448 ms W R) (T : Nat)
    (hT : steps T (roundStart ms W) = none) :
    ∃ n₁ ms₁ W₁ R₁ p, roundsZ 1000 n₁ ms W = .newRound ms₁ W₁ ∧ (∀ d ∈ meetsRounds 1000 n₁ ms W, 3 ≤ d) ∧
      PassStart448 ms₁ W₁ R₁ ∧ R = 16 ^ p * R₁ ∧ passL1 ms W = 64 ^ p * passL1 ms₁ W₁ ∧
      ((InCloseClass ms₁ W₁ R₁ ∧ SigmaOK R (passL1 ms W) ∧
          ∃ t, Reach ⟨[], 1, ms₁, W₁⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
        ∃ n₂ ms' W', roundsZ 1000 n₂ ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n₂ ms₁ W₁, 3 ≤ d) ∧
          LoopEnd 1000 R₁ (passL1 ms₁ W₁) n₂ (meetsRounds 1000 n₂ ms₁ W₁) ms' W' ∧
          ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) := by
  obtain ⟨hwf, hG⟩ := hP.wf
  obtain ⟨n₁, -, ms₁, W₁, R₁, p, -, hr₁, hm₁, hP₁, hRp, hLp, hrest⟩ := loop_stretch R ms W hP
  obtain ⟨hwf₁, hG₁⟩ := hP₁.wf
  obtain ⟨k₁, -, -, hT₁, -, t, ht, htw, hts⟩ := halt_after_rounds 1000 n₁ ms W ms₁ W₁ hwf hG hr₁ T hT
  refine ⟨n₁, ms₁, W₁, R₁, p, hr₁, hm₁, hP₁, hRp, hLp, ?_⟩
  rcases hrest with hc | ⟨n₂, -, ms', W', -, hr₂, hm₂, he⟩
  · exact Or.inl ⟨hc, sigma_through_passes hc p R _ hRp hLp, t, ht, htw, stuck_cases hts⟩
  · obtain ⟨-, -, -, -, -, t', ht', htw', hts'⟩ := halt_after_rounds 1000 n₂ ms₁ W₁ ms' W' hwf₁ hG₁ hr₂ _ hT₁
    exact Or.inr ⟨n₂, ms', W', hr₂, hm₂, he, t', ht', htw', stuck_cases hts'⟩

/-- **The σ bound.**  If the machine halts from a phase-0 pass start with right end R, every gap at least 448 and
R³/L₁² > 176³/256² (with s = log₂(W/R), λ = log₂(|L₁|/W) and σ = 3s + 2λ: log₂W > σ + 6.38), then it does not close
through the loop: the mark model covers a close-free stretch through p full passes to the last pass start `ms₁ W₁`
with gaps again all at least 448, then a further close-free stretch to where the run leaves the loop (`LoopEnd`), and
the halt needs a stuck configuration after that. -/
theorem loop_halt_sigma (R : Nat) (ms : List Mark) (W : Nat) (hP : PassStart448 ms W R)
    (hσ : ¬ SigmaOK R (passL1 ms W)) (T : Nat) (hT : steps T (roundStart ms W) = none) :
    ∃ n₁ ms₁ W₁ R₁ p, roundsZ 1000 n₁ ms W = .newRound ms₁ W₁ ∧ (∀ d ∈ meetsRounds 1000 n₁ ms W, 3 ≤ d) ∧
      PassStart448 ms₁ W₁ R₁ ∧ R = 16 ^ p * R₁ ∧ passL1 ms W = 64 ^ p * passL1 ms₁ W₁ ∧
      ∃ n₂ ms' W', roundsZ 1000 n₂ ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n₂ ms₁ W₁, 3 ≤ d) ∧
        LoopEnd 1000 R₁ (passL1 ms₁ W₁) n₂ (meetsRounds 1000 n₂ ms₁ W₁) ms' W' ∧
        ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t) := by
  obtain ⟨n₁, ms₁, W₁, R₁, p, hr₁, hm₁, hP₁, hRp, hLp, ⟨-, hs, -⟩ | h⟩ := loop_halt_needs_contact R ms W hP T hT
  · exact absurd hs hσ
  · exact ⟨n₁, ms₁, W₁, R₁, p, hr₁, hm₁, hP₁, hRp, hLp, h⟩

#print axioms loop_halt_needs_contact
#print axioms loop_halt_sigma

end BB6
