import CleanEntryTheorem
import RouteEntryHalt
import EndToEndDirect
open BB6 BB6.Sym

/-! # Clean tapes and loop entries, from blank tape

`clean_tree_entry_step` (`thm/CleanEntryTheorem.lean`) ends every path of the clean-tape tree with loop entries at a
wider clean tape, at a wider pass start from which no point of the class closes through the loop (`EntryNoClose`), or
in a cut class.  `clean_entry_chain` chains such steps by strong induction on the halting time, as `clean_chain` does
(`thm/EndToEnd.lean`), with the step (`hStep`, for any notion `Cut` of the cut classes) and what a halt from a loop
entry needs (`hQ`) as hypotheses: at an entry, either a property `Q` of the entry and the time left, or a wider clean
tape that the run reaches from the entry, from which the chain goes on.  `entry_halt` (`thm/RouteEntryHalt.lean`)
gives the first: from a loop entry that cannot close, the loop's chain ends without a close where the run leaves three
walls.  With the prefix to 2³² and the clean tapes of width in [2³², 2⁴¹) run one by one (`stepsBelow_direct`), a halt
from blank tape needs a clean tape of width at least 2⁴¹ in a cut class of the tree with entries at every depth, or a
loop entry wider than 2⁴¹ from which the loop's chain ends that way (`blank_halt_clean_entry`).  From the kernel's
prefix to 2²⁰ the same holds with the plain tree over the widths ≥ 2²⁰ below 2²⁴, where the entries' width test is not
decided on the classes, and the tree with entries over the widths ≥ 2²⁴ above (`blank_halt_clean_entry_kernel`). -/

/-- A run of the mark model from a clean tape to a wider one keeps the width even and takes at least one machine
step. -/
theorem clean_next {W n k W' : Nat} (hW : W % 2 = 0) (hG6 : 6 ≤ W) (hlt : W < W')
    (hr : roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound [⟨.M, W' - 2⟩] W')
    (hk : steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.M, W' - 2⟩] W')) : W' % 2 = 0 ∧ 0 < k := by
  have hwf : roundWF [⟨.M, W - 2⟩] W := roundWF_one.mpr ⟨hG6, hW⟩
  obtain ⟨-, -, hwf'⟩ := rounds_run 1000 n _ _ hwf (by rw [hr]; intro h; cases h)
  rw [hr] at hwf'
  have hW' : 6 ≤ W' ∧ W' % 2 = 0 := roundWF_one.mp hwf'
  refine ⟨hW'.2, ?_⟩
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0
    simp only [steps, Option.some.injEq] at hk
    exact absurd hk (roundStart_one_ne W W' hG6 hlt hW hW'.2)
  · exact h0

/-- **A halt from a clean tape, through the clean tapes and the loop entries.**  Let every clean tape of even width
in [A, B) reach a wider one (`StepsBelow A B`); let every clean tape of even width W ≥ B, at every depth d, either be
cut (`Cut d W`) or reach a wider clean tape after at least one round, or a wider loop entry that cannot close
(`EntryNoClose`), without halting (`hStep`); and let a halt from every loop entry that cannot close need either `Q` of
the entry and the time left, or a wider clean tape of even width that the run reaches after at least one step (`hQ`).
If the machine halts T steps after a clean tape of even width W ≥ A, then it reaches a clean tape of even width
W′ ≥ W, W′ ≥ B, that is cut at every depth, and halts from there; or it reaches a loop entry of width W′ > W, W′ > B,
that cannot close, after k steps, and `Q` holds of it with the time left, T − k. -/
theorem clean_entry_chain (A B : Nat) (h6 : 6 ≤ A) (hB : StepsBelow A B)
    (Cut : Nat → Nat → Prop)
    (hStep : ∀ d W, W % 2 = 0 → B ≤ W →
      ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
        steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
        (Cut d W ∨ (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W') ∨ (EntryNoClose ms' W' ∧ W < W')))
    (Q : List Mark → Nat → Nat → Prop)
    (hQ : ∀ ms W T, EntryNoClose ms W → steps T (roundStart ms W) = none →
      Q ms W T ∨ ∃ k W', 0 < k ∧ W < W' ∧ W' % 2 = 0 ∧
        steps k (roundStart ms W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧
        steps (T - k) (roundStart [⟨.M, W' - 2⟩] W') = none)
    (T : Nat) : ∀ W, W % 2 = 0 → A ≤ W → steps T (roundStart [⟨.M, W - 2⟩] W) = none →
      (∃ W' k, W ≤ W' ∧ B ≤ W' ∧ W' % 2 = 0 ∧ (∀ d, Cut d W') ∧
        steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧
        steps (T - k) (roundStart [⟨.M, W' - 2⟩] W') = none) ∨
      ∃ ms' W' k, W < W' ∧ B < W' ∧ EntryNoClose ms' W' ∧
        steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧ Q ms' W' (T - k) := by
  induction T using Nat.strongRecOn with
  | ind T ih =>
    intro W hW hA hT
    have hG6 : 6 ≤ W := by omega
    by_cases hstop : B ≤ W ∧ ∀ d, Cut d W
    · exact Or.inl ⟨W, 0, Nat.le_refl _, hstop.1, hW, hstop.2, rfl, by simpa using hT⟩
    -- otherwise the run reaches a loop entry where `Q` holds, or a wider clean tape, and the chain goes on from there
    suffices hnext : (∃ ms' W' k, W < W' ∧ B < W' ∧ EntryNoClose ms' W' ∧
        steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧ Q ms' W' (T - k)) ∨
        ∃ k W', 0 < k ∧ W < W' ∧ W' % 2 = 0 ∧
          steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.M, W' - 2⟩] W') by
      rcases hnext with h | ⟨k, W', hk0, hlt, hW', hk⟩
      · exact Or.inr h
      obtain ⟨hle, hT'⟩ := steps_none_split hT hk
      rcases ih (T - k) (by omega) W' hW' (by omega) hT' with ⟨W'', k'', h1, h2, h3, h4, h5, h6⟩ |
          ⟨ms'', W'', k'', h1, h2, h3, h4, h5⟩
      · refine Or.inl ⟨W'', k + k'', by omega, h2, h3, h4, steps_seq hk h5, ?_⟩
        rw [show T - (k + k'') = T - k - k'' by omega]
        exact h6
      · refine Or.inr ⟨ms'', W'', k + k'', by omega, h2, h3, steps_seq hk h4, ?_⟩
        rw [show T - (k + k'') = T - k - k'' by omega]
        exact h5
    by_cases hb : W < B
    · obtain ⟨n, k, W', hr, hk, -, hlt⟩ := hB W hW hA hb
      obtain ⟨hW', hk0⟩ := clean_next hW hG6 hlt hr hk
      exact Or.inr ⟨k, W', hk0, hlt, hW', hk⟩
    obtain ⟨d, hd⟩ := Classical.not_forall.mp (fun hall => hstop ⟨by omega, hall⟩)
    obtain ⟨n, k, ms', W', hr, hk, hc⟩ := hStep d W hW (by omega)
    rcases hc with hc | ⟨-, rfl, hlt⟩ | ⟨he, hlt⟩
    · exact absurd hc hd
    · obtain ⟨hW', hk0⟩ := clean_next hW hG6 hlt hr hk
      exact Or.inr ⟨k, W', hk0, hlt, hW', hk⟩
    · obtain ⟨-, hT'⟩ := steps_none_split hT hk
      rcases hQ ms' W' (T - k) he hT' with hq | ⟨k', W'', hk', hlt', hW'', hk'', -⟩
      · exact Or.inl ⟨ms', W', k, hlt, by omega, he, hk, hq⟩
      · exact Or.inr ⟨k + k', W'', by omega, by omega, hW'', steps_seq hk hk''⟩

/-- **A halt from blank tape, after a prefix, with the loop entries.**  `clean_entry_chain` from the clean tape of even
width W₀ ≥ A that the run from blank tape reaches after k₀ steps, with `Q` from `entry_halt`: if the machine halts
after T steps, then either it reaches a clean tape of even width W ≥ B that is cut at every depth, halts from there,
and the mark model, run from there, reaches a stuck configuration; or it reaches a loop entry of width W > B that
cannot close (`EntryNoClose`), halts from there, and the loop's chain from there (`LoopChain`) ends without a close,
where the run, close-free, has left phase 0 or the halving chain at a round start that is not three walls, and the
halt needs a stuck configuration after that. -/
theorem blank_halt_clean_entry_from (A B W₀ k₀ : Nat) (h6 : 6 ≤ A) (hB : StepsBelow A B)
    (Cut : Nat → Nat → Prop)
    (hStep : ∀ d W, W % 2 = 0 → B ≤ W →
      ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
        steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
        (Cut d W ∨ (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W') ∨ (EntryNoClose ms' W' ∧ W < W')))
    (hW₀ : W₀ % 2 = 0) (hAW₀ : A ≤ W₀) (hk₀ : steps k₀ ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W₀ - 2⟩] W₀))
    (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    (∃ W k, B ≤ W ∧ W % 2 = 0 ∧ (∀ d, Cut d W) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
    ∃ ms W k, B < W ∧ EntryNoClose ms W ∧ steps k ⟨blank, blank, .A⟩ = some (roundStart ms W) ∧
      steps (T - k) (roundStart ms W) = none ∧
      ∃ R ks ms₁ W₁ R₁, PassStart448 ms W R ∧ LoopChain ms W R ks ms₁ W₁ R₁ ∧
        ∃ n ms' W', roundsZ 1000 n ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n ms₁ W₁, 3 ≤ d) ∧
          (LeftPhase0 n ms' ∨ ChainBreak (meetsRounds 1000 n ms₁ W₁)) ∧ NotWWW ms' ∧
          ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t) := by
  obtain ⟨-, hT₀⟩ := steps_none_split hT hk₀
  rcases clean_entry_chain A B h6 hB Cut hStep (fun ms W T => steps T (roundStart ms W) = none)
      (fun _ _ _ _ hT => Or.inl hT) (T - k₀) W₀ hW₀ hAW₀ hT₀ with ⟨W, k, hle, hBW, hW, hcut, hk, hTW⟩ |
      ⟨ms, W, k, -, hBW, he, hk, hTW⟩
  · have hG6 : 6 ≤ W := by omega
    obtain ⟨t, ht, htw, hts⟩ := round_halt_needs_contact [⟨.M, W - 2⟩] W _ (roundWF_one.mpr ⟨hG6, hW⟩)
      (noG_one _) hTW
    refine Or.inl ⟨W, k₀ + k, hBW, hW, hcut, steps_seq hk₀ hk, ?_, t, ht, htw, stuck_cases hts⟩
    rw [show T - (k₀ + k) = T - k₀ - k by omega]
    exact hTW
  · refine Or.inr ⟨ms, W, k₀ + k, hBW, he, steps_seq hk₀ hk, ?_, entry_halt he _ hTW⟩
    rw [show T - (k₀ + k) = T - k₀ - k by omega]
    exact hTW

/-- **What a halt from blank tape needs, with the loop entries.**  `blank_halt_clean_entry_from` with the prefix to
2³² (`blank_prefix`), the clean tapes of width in [2³², 2⁴¹) run one by one (`stepsBelow_direct`) and the clean-tape
tree with loop entries over the widths ≥ 2⁴¹ (`clean_tree_entry_step`): if the machine, started on blank tape, halts
after T steps, then either it reaches a clean tape of even width W ≥ 2⁴¹ with W/2 in a cut class of
`cleanTreeGE directWidth d` at every depth, halts from there, and the mark model reaches a stuck configuration from
there; or it reaches a loop entry of width W > 2⁴¹ that cannot close (`EntryNoClose`: a phase-0 pass start with every
gap at least 448, from which no close through the loop fits its right end and left countdown), halts from there, and
the loop's chain from there ends without a close, where the run, close-free, has left phase 0 or the halving chain at
a round start that is not three walls, and the halt needs a stuck configuration after that. -/
theorem blank_halt_clean_entry (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    (∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeGE directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
    ∃ ms W k, directWidth < W ∧ EntryNoClose ms W ∧ steps k ⟨blank, blank, .A⟩ = some (roundStart ms W) ∧
      steps (T - k) (roundStart ms W) = none ∧
      ∃ R ks ms₁ W₁ R₁, PassStart448 ms W R ∧ LoopChain ms W R ks ms₁ W₁ R₁ ∧
        ∃ n ms' W', roundsZ 1000 n ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n ms₁ W₁, 3 ≤ d) ∧
          (LeftPhase0 n ms' ∨ ChainBreak (meetsRounds 1000 n ms₁ W₁)) ∧ NotWWW ms' ∧
          ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t) := by
  obtain ⟨k₀, hk₀⟩ := blank_prefix
  exact blank_halt_clean_entry_from cleanGamma directWidth prefixWidth k₀ (by decide) stepsBelow_direct
    (fun d W => (cleanTreeGE directWidth d).cutMem [(W : Int) / 2, 0] = true)
    (fun d W hW h => clean_tree_entry_step directWidth d W (by decide) hW h) (by decide) (by decide) hk₀ T hT

/-- **The kernel's step, with the loop entries.**  For every clean tape of even width W ≥ 2²⁰ and every depth d, with
the plain clean-tape tree over the widths ≥ 2²⁰ if W < 2²⁴ (`clean_tree_step_G`; there the loop entries' width test,
2²⁴, is not decided on the classes) and the tree with loop entries over the widths ≥ 2²⁴ if not
(`clean_tree_entry_step`): W/2 is in a cut class of that tree, or the run reaches a wider clean tape after at least one
round, or a wider loop entry that cannot close. -/
theorem clean_entry_step_kernel (d W : Nat) (hW : W % 2 = 0) (h : kernelPrefixWidth ≤ W) :
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
      (((W < 2 ^ 24 → (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
          (2 ^ 24 ≤ W → (cleanTreeGE (2 ^ 24) d).cutMem [(W : Int) / 2, 0] = true)) ∨
        (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W') ∨ (EntryNoClose ms' W' ∧ W < W')) := by
  by_cases hl : W < 2 ^ 24
  · obtain ⟨n, k, ms', W', hr, hk, hc⟩ := clean_tree_step_G kernelPrefixWidth d W (by decide) hW h
    refine ⟨n, k, ms', W', hr, hk, ?_⟩
    rcases hc with hc | hc
    · exact Or.inl ⟨fun _ => hc, fun h' => absurd h' (Nat.not_le.mpr hl)⟩
    · exact Or.inr (Or.inl hc)
  · obtain ⟨n, k, ms', W', hr, hk, hc⟩ := clean_tree_entry_step (2 ^ 24) d W (by decide) hW (Nat.le_of_not_lt hl)
    refine ⟨n, k, ms', W', hr, hk, ?_⟩
    rcases hc with hc | hc | hc
    · exact Or.inl ⟨fun h' => absurd h' hl, fun _ => hc⟩
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr hc)

/-- **The same, checked by the kernel alone.**  `blank_halt_clean_entry_from` from the kernel's prefix to 2²⁰
(`blank_prefix_kernel`), with the plain clean-tape tree over the widths ≥ 2²⁰ for the clean tapes below 2²⁴ and the
tree with loop entries over the widths ≥ 2²⁴ above (`clean_entry_step_kernel`): if the machine, started on blank tape,
halts after T steps, then either it reaches a clean tape of even width W ≥ 2²⁰ that is cut at every depth, by
`cleanTreeG 2²⁰ d` if W < 2²⁴ and by `cleanTreeGE 2²⁴ d` if not, halts from there, and the mark model reaches a stuck
configuration from there; or it reaches a loop entry of width W > 2²⁰ that cannot close, halts from there, and the
loop's chain from there ends without a close, as in `blank_halt_clean_entry`.  Nothing here is evaluated by compiled
code. -/
theorem blank_halt_clean_entry_kernel (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    (∃ W k, kernelPrefixWidth ≤ W ∧ W % 2 = 0 ∧
      (W < 2 ^ 24 → ∀ d, (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      (2 ^ 24 ≤ W → ∀ d, (cleanTreeGE (2 ^ 24) d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
    ∃ ms W k, kernelPrefixWidth < W ∧ EntryNoClose ms W ∧ steps k ⟨blank, blank, .A⟩ = some (roundStart ms W) ∧
      steps (T - k) (roundStart ms W) = none ∧
      ∃ R ks ms₁ W₁ R₁, PassStart448 ms W R ∧ LoopChain ms W R ks ms₁ W₁ R₁ ∧
        ∃ n ms' W', roundsZ 1000 n ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n ms₁ W₁, 3 ≤ d) ∧
          (LeftPhase0 n ms' ∨ ChainBreak (meetsRounds 1000 n ms₁ W₁)) ∧ NotWWW ms' ∧
          ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t) := by
  obtain ⟨k₀, hk₀⟩ := blank_prefix_kernel
  rcases blank_halt_clean_entry_from kernelPrefixWidth kernelPrefixWidth kernelPrefixWidth k₀ (by decide)
      (stepsBelow_self _) _ clean_entry_step_kernel (by decide) (Nat.le_refl _) hk₀ T hT with
      ⟨W, k, h1, h2, hcut, h3⟩ | h
  · exact Or.inl ⟨W, k, h1, h2, fun hl d => (hcut d).1 hl, fun hl d => (hcut d).2 hl, h3⟩
  · exact Or.inr h

#print axioms clean_entry_chain
#print axioms blank_halt_clean_entry
#print axioms blank_halt_clean_entry_kernel
