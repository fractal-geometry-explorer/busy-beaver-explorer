import EndToEnd
import CleanDirect

/-!
# End to end above 2⁴¹

`blank_halt_clean` with the clean tapes of width in [2³², 2⁴¹) run one by one (`clean_step_direct`,
`thm/CleanDirect.lean`): the clean tape a halt from blank tape needs is at least 2⁴¹ wide, and it lies in the cut
classes of the clean-tape tree over the widths ≥ 2⁴¹ (`cleanTreeG directWidth d`) at every depth.  This adds the
evaluation `clean_direct_ok` (`native_decide`) to what `blank_halt_clean` trusts.
-/

namespace BB6
open BB6.Sym

theorem stepsBelow_direct : StepsBelow directWidth := clean_step_direct

/-- **What a halt from blank tape needs, above 2⁴¹.**  If the machine, started on blank tape, halts after T steps,
then it first reaches a clean tape of even width W ≥ 2⁴¹ with W/2 in a cut class of the clean-tape tree over the
widths ≥ 2⁴¹ at every depth, and halts from that clean tape; and the mark model, run from that clean tape, reaches a
stuck configuration. -/
theorem blank_halt_clean_direct (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t) := by
  obtain ⟨W, k, -, h⟩ := blank_halt_clean_from directWidth (by decide) stepsBelow_direct T hT
  exact ⟨W, k, h⟩

/-- **The open question, reduced, above 2⁴¹.**  If the machine does not halt from any clean tape of even width
W ≥ 2⁴¹ with W/2 in a cut class of the clean-tape tree over the widths ≥ 2⁴¹ at every depth, then it does not halt
from blank tape. -/
theorem never_halts_of_cut_classes_direct
    (h : ∀ W, directWidth ≤ W → W % 2 = 0 → (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) →
      ∀ T, steps T (roundStart [⟨.M, W - 2⟩] W) ≠ none) :
    ∀ T, steps T ⟨blank, blank, .A⟩ ≠ none := by
  intro T hT
  obtain ⟨W, k, hle, hW, hcut, -, hTW, -⟩ := blank_halt_clean_direct T hT
  exact h W hle hW hcut (T - k) hTW

#print axioms blank_halt_clean_direct
#print axioms never_halts_of_cut_classes_direct

end BB6
