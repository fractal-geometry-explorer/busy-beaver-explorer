import Prefix
import CleanTheorem
import LoopHalt

/-!
# End to end: what a halt of the machine from blank tape needs

The pieces, all theorems about the machine `1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE` started on blank tape:

* `blank_prefix` (`thm/Prefix.lean`): the machine reaches the one-marker clean tape of width 2³² without halting.
* `clean_tree_step` (`thm/CleanTheorem.lean`): from every clean tape of width W ≥ 2³², the machine reaches a wider
  clean tape without halting, unless W/2 lies in one of the clean-tape tree's cut classes.
* `round_halt_needs_contact`, `stuck_cases` (`BB6/HaltClose`, `BB6/HaltStretch`): a halt from a round start needs
  the mark model, run from there, to reach a stuck configuration: a close at the right end or an interior contact.
* `loop_halt_needs_contact` (`thm/LoopHalt.lean`): a halt from a phase-0 pass start with every gap at least 448 comes
  only after the close-free stretch `loop_stretch` certifies from it, through its passes, and needs a stuck
  configuration after it: after a pass start whose R is in the closing set with L₁ in R's class, or after the run
  leaves the loop (`LoopEnd`).  (`exit_halt_needs_contact` (`thm/ExitHalt.lean`), the same after a loop state's exit
  stretch, is not imported here.)

`clean_chain` chains the clean-tape steps by strong induction on the halting time (a run from a clean tape to a wider
one takes at least one step, `roundStart_one_ne`), and `blank_halt_structure` puts everything together.

**What is not claimed.**  Nothing is said about the clean tapes in the cut classes: whether the machine halts from
them is exactly what remains open.  The cut classes are residue classes of W/2 (to at most `cleanTree.depth` binary
digits) of total measure `clean_tree_cut_mass`; the statement says that a halt must pass through a clean tape of width
at least 2³² in one of them, and halt from there.
-/

namespace BB6
open BB6.Sym

theorem noG_one (W : Nat) : noG [⟨.M, W⟩] := by
  intro m hm
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
  subst hm; simp

/-- **A halt from a wide clean tape passes through a clean tape in a cut class.**  If the machine halts T steps after
a clean tape of even width W ≥ `cleanGamma`, then it reaches a clean tape of some even width W' ≥ W with W'/2 in a cut
class of the clean-tape tree, and halts from there. -/
theorem clean_chain (T : Nat) : ∀ (W : Nat), W % 2 = 0 → cleanGamma ≤ W →
    steps T (roundStart [⟨.M, W - 2⟩] W) = none →
    ∃ W' k, W ≤ W' ∧ W' % 2 = 0 ∧ cleanTree.cutMem [(W' : Int) / 2, 0] = true ∧
      steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧
      steps (T - k) (roundStart [⟨.M, W' - 2⟩] W') = none := by
  induction T using Nat.strongRecOn with
  | ind T ih =>
    intro W hW hG hT
    have hG6 : 6 ≤ W := by simp only [cleanGamma] at hG; omega
    obtain ⟨n, k, ms', W', hr, hk, hc⟩ := clean_tree_step W hW hG
    rcases hc with hc | ⟨-, rfl, hlt⟩
    · exact ⟨W, 0, Nat.le_refl _, hW, hc, rfl, by simpa using hT⟩
    · have hwf : roundWF [⟨.M, W - 2⟩] W := roundWF_one.mpr ⟨hG6, hW⟩
      obtain ⟨-, -, hwf'⟩ := rounds_run 1000 n _ _ hwf (by rw [hr]; intro h; cases h)
      rw [hr] at hwf'
      have hW' : 6 ≤ W' ∧ W' % 2 = 0 := roundWF_one.mp hwf'
      obtain ⟨hle, hT'⟩ := steps_none_split hT hk
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0
          simp only [steps, Option.some.injEq] at hk
          exact absurd hk (roundStart_one_ne W W' hG6 hlt hW hW'.2)
        · exact h0
      obtain ⟨W'', k'', h1, h2, h3, h4, h5⟩ := ih (T - k) (by omega) W' hW'.2 (by omega) hT'
      refine ⟨W'', k + k'', by omega, h2, h3, steps_seq hk h4, ?_⟩
      rw [show T - (k + k'') = T - k - k'' by omega]
      exact h5

/-- **End to end: what a halt from blank tape needs.**  If the machine, started on blank tape, halts after T steps,
then:

1. it first reaches a clean tape (gap, then only the end marker) of even width W ≥ 2³² with W/2 in one of the cut
   classes of the clean-tape tree, and halts from that clean tape;
2. the mark model, run from that clean tape, reaches a stuck configuration: a close at the right end
   (`EndClose`: the gap meets the end marker at distance 0, or touches a block at the end) or an interior contact;
3. every phase-0 pass start the machine passes on its way (walls at a, b, E − R − 1, width E, the parities, every gap
   ≥ 448: `PassStart448`) is followed by a close-free stretch the mark model covers, through the pass starts with
   gaps again all ≥ 448 to the last of them (right end R₁ ≤ R), and the halt needs a stuck configuration after it:
   either right there, with R₁ in the closing set {2, 4, 8, 16, 24, 32, 48, 64, 176} and L₁ in R₁'s class
   (`InCloseClass`), or after a further close-free stretch to where the run leaves the loop (`LoopEnd`: it leaves
   phase 0, its end meetings leave the halving chain, or it reaches the next pass start, and it is not at a pass
   start with every gap ≥ 448 there). -/
theorem blank_halt_structure (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    (∃ W k, prefixWidth ≤ W ∧ W % 2 = 0 ∧ cleanTree.cutMem [(W : Int) / 2, 0] = true ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∧
    (∀ (R : Nat) (ms : List Mark) (W k : Nat), PassStart448 ms W R →
      steps k ⟨blank, blank, .A⟩ = some (roundStart ms W) →
      ∃ n₁ ms₁ W₁ R₁, roundsZ 1000 n₁ ms W = .newRound ms₁ W₁ ∧ (∀ d ∈ meetsRounds 1000 n₁ ms W, 3 ≤ d) ∧
        PassStart448 ms₁ W₁ R₁ ∧ R₁ ≤ R ∧
        ((InCloseClass ms₁ W₁ R₁ ∧ ∃ t, Reach ⟨[], 1, ms₁, W₁⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
          ∃ n₂ ms' W', roundsZ 1000 n₂ ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n₂ ms₁ W₁, 3 ≤ d) ∧
            LoopEnd 1000 R₁ n₂ (meetsRounds 1000 n₂ ms₁ W₁) ms' W' ∧
            ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t))) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨k₀, hk₀⟩ := blank_prefix
    obtain ⟨-, hT₀⟩ := steps_none_split hT hk₀
    obtain ⟨W, k, hle, hW, hcut, hk, hTW⟩ :=
      clean_chain (T - k₀) prefixWidth (by decide) (by decide) hT₀
    have hG6 : 6 ≤ W := by simp only [prefixWidth] at hle; omega
    obtain ⟨t, ht, htw, hts⟩ := round_halt_needs_contact [⟨.M, W - 2⟩] W _ (roundWF_one.mpr ⟨hG6, hW⟩)
      (noG_one _) hTW
    refine ⟨W, k₀ + k, hle, hW, hcut, steps_seq hk₀ hk, ?_, t, ht, htw, stuck_cases hts⟩
    rw [show T - (k₀ + k) = T - k₀ - k by omega]
    exact hTW
  · intro R ms W k hP hk
    obtain ⟨-, hT'⟩ := steps_none_split hT hk
    exact loop_halt_needs_contact R ms W hP _ hT'

/-- **The open question, reduced.**  If the machine does not halt from any clean tape of even width W ≥ 2³² with W/2
in a cut class of the clean-tape tree, then it does not halt from blank tape. -/
theorem never_halts_of_cut_classes
    (h : ∀ W, prefixWidth ≤ W → W % 2 = 0 → cleanTree.cutMem [(W : Int) / 2, 0] = true →
      ∀ T, steps T (roundStart [⟨.M, W - 2⟩] W) ≠ none) :
    ∀ T, steps T ⟨blank, blank, .A⟩ ≠ none := by
  intro T hT
  obtain ⟨⟨W, k, hle, hW, hcut, -, hTW, -⟩, -⟩ := blank_halt_structure T hT
  exact h W hle hW hcut (T - k) hTW

#print axioms blank_halt_structure
#print axioms never_halts_of_cut_classes

end BB6
