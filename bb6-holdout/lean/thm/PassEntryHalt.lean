import CleanEntryHalt
import PassHalt
open BB6 BB6.Sym

/-! # From blank tape, past the loop's end

`blank_halt_clean_entry_from` (`thm/CleanEntryHalt.lean`) leaves a halting run from blank tape at a clean tape that is
cut at every depth, or at a loop entry that cannot close (`EntryNoClose`), from which it only follows the loop's chain
to its end (`entry_halt`).  The pass-start trees (`thm/PassHalt.lean`) follow the run past that end: by
`pass_halt_chain`, a halt from a pass start of width at least 2¹³ follows the loop's chain to a last pass start where
the left countdown is in a closing class, or that is cut at every depth of its pass-start tree, or from which the run
reaches a wider clean tape and halts from there.  From a loop entry that cannot close the first is out
(`EntryNoClose.no_close`), so a halt from the entry needs a pass start cut at every depth of its tree, or a wider clean
tape (`entry_pass_halt`), from which `clean_entry_chain` goes on.  So a halt from blank tape needs a clean tape in a cut
class of the clean-tape tree at every depth, or a pass start in a cut class of its pass-start tree at every depth
(`blank_halt_pass`, and `blank_halt_pass_kernel` with nothing evaluated by compiled code).  Some pass starts in the
pass-start trees' cut classes do halt (1/8 of those with R = 6), so what is left open is whether the run from blank tape
reaches one of them, or a clean tape in a cut class.  The clean-tape tree without loop entries follows the run on
through every entry, so such a pass start comes only after a clean tape that this tree leaves open at every depth:
`blank_halt_open` (and `blank_halt_open_kernel`) puts `blank_halt_clean_direct` and `blank_halt_pass` together. -/

/-- The loop's chain is a run of the machine: its last pass start follows its first. -/
theorem LoopChain.reach {ms : List Mark} {W R : Nat} {ks : List StepKind} {ms' : List Mark} {W' R' : Nat}
    (h : LoopChain ms W R ks ms' W' R') : ∃ t, steps t (roundStart ms W) = some (roundStart ms' W') := by
  induction h with
  | nil _ => exact ⟨0, rfl⟩
  | cons _ _ kk _ hk _ _ _ _ _ ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨kk + t, steps_seq hk ht⟩

/-- **A halt from a loop entry that cannot close.**  If the machine halts T steps after a loop entry that cannot close
(`EntryNoClose`), then its run follows the loop's chain (`LoopChain`) to a last pass start with walls a₁, b₁ and
W₁ − R₁ − 1 that lies in a cut leaf of its pass-start tree at every depth (`PassCut`), which it reaches after t steps
and halts from; or it reaches a one-marker clean tape of even width W′ > W after k > 0 steps, and halts from there. -/
theorem entry_pass_halt {ms : List Mark} {W : Nat} (h : EntryNoClose ms W) (T : Nat)
    (hT : steps T (roundStart ms W) = none) :
    (∃ R ks a₁ b₁ W₁ R₁ t, LoopChain ms W R ks [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧
      (∀ d, PassCut d R₁ a₁ b₁ W₁) ∧
      steps t (roundStart ms W) = some (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) ∧
      steps (T - t) (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) = none) ∨
    ∃ k W', 0 < k ∧ W < W' ∧ W' % 2 = 0 ∧
      steps k (roundStart ms W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧
      steps (T - k) (roundStart [⟨.M, W' - 2⟩] W') = none := by
  obtain ⟨hW, R, a, b, rfl, hP, hh, -⟩ := id h
  obtain ⟨ks, a₁, b₁, W₁, R₁, hch, -, hend⟩ :=
    pass_halt_chain T R a b W hP (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by decide)) hW) hh hT
  rcases hend with ⟨hc, -⟩ | hcut | ⟨k, W', hk, -, hlt, hW', hs, hT'⟩
  · exact (h.no_close hch hc).elim
  · obtain ⟨t, ht⟩ := hch.reach
    exact Or.inl ⟨R, ks, a₁, b₁, W₁, R₁, t, hch, hcut, ht, (steps_none_split hT ht).2⟩
  · exact Or.inr ⟨k, W', hk, hlt, hW', hs, hT'⟩

/-- **A halt from blank tape, after a prefix, past the loop's end.**  `clean_entry_chain` from the clean tape of even
width W₀ ≥ A that the run from blank tape reaches after k₀ steps, with `Q` from `entry_pass_halt`: if the machine halts
after T steps, then either it reaches a clean tape of even width W ≥ B that is cut at every depth, halts from there,
and the mark model, run from there, reaches a stuck configuration; or it reaches a pass start of width W > B, W ≥ 2²⁴,
with walls a, b and W − R − 1 and every gap at least 448 (`PassStart448`), that lies in a cut leaf of its pass-start
tree at every depth, halts from there, and the mark model reaches a stuck configuration from there. -/
theorem blank_halt_pass_from (A B W₀ k₀ : Nat) (h6 : 6 ≤ A) (hB : StepsBelow A B)
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
    ∃ R a b W k, B < W ∧ 2 ^ 24 ≤ W ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ∧
      (∀ d, PassCut d R a b W) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) ∧
      steps (T - k) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t) := by
  obtain ⟨-, hT₀⟩ := steps_none_split hT hk₀
  rcases clean_entry_chain A B h6 hB Cut hStep
      (fun ms W T' => ∃ R ks a₁ b₁ W₁ R₁ t, LoopChain ms W R ks [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧
        (∀ d, PassCut d R₁ a₁ b₁ W₁) ∧
        steps t (roundStart ms W) = some (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) ∧
        steps (T' - t) (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) = none)
      (fun _ _ T' he hT' => entry_pass_halt he T' hT') (T - k₀) W₀ hW₀ hAW₀ hT₀ with
      ⟨W, k, hle, hBW, hW, hcut, hk, hTW⟩ | ⟨ms, W, k, -, hBW, he, hk, R, ks, a₁, b₁, W₁, R₁, t, hch, hcut, ht, hT₁⟩
  · have hG6 : 6 ≤ W := by omega
    obtain ⟨u, hu, huw, hus⟩ := round_halt_needs_contact [⟨.M, W - 2⟩] W _ (roundWF_one.mpr ⟨hG6, hW⟩)
      (noG_one _) hTW
    refine Or.inl ⟨W, k₀ + k, hBW, hW, hcut, steps_seq hk₀ hk, ?_, u, hu, huw, stuck_cases hus⟩
    rw [show T - (k₀ + k) = T - k₀ - k by omega]
    exact hTW
  · -- the chain only widens, from the entry's width W ≥ 2²⁴
    have hW₁ := hch.width
    have h24 : 2 ^ 24 ≤ W₁ := Nat.le_trans he.1 (by omega)
    have hP₁ := hch.last
    obtain ⟨hwf, hG⟩ := hP₁.wf
    obtain ⟨u, hu, huw, hus⟩ := round_halt_needs_contact _ W₁ _ hwf hG hT₁
    refine Or.inr ⟨R₁, a₁, b₁, W₁, k₀ + k + t, by omega, h24, hP₁, hcut, steps_seq (steps_seq hk₀ hk) ht, ?_,
      u, hu, huw, stuck_cases hus⟩
    rw [show T - (k₀ + k + t) = T - k₀ - k - t by omega]
    exact hT₁

/-- **What a halt from blank tape needs.**  `blank_halt_pass_from` with the prefix to 2³² (`blank_prefix`), the clean
tapes of width in [2³², 2⁴¹) run one by one (`stepsBelow_direct`) and the clean-tape tree with loop entries over the
widths ≥ 2⁴¹ (`clean_tree_entry_step`): if the machine, started on blank tape, halts after T steps, then either it
reaches a clean tape of even width W ≥ 2⁴¹ with W/2 in a cut class of `cleanTreeGE directWidth d` at every depth, or a
pass start of width W > 2⁴¹ with every gap at least 448 that lies in a cut leaf of its pass-start tree at every depth
(`PassCut`); it halts from there, and the mark model reaches a stuck configuration from there. -/
theorem blank_halt_pass (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    (∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeGE directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
    ∃ R a b W k, directWidth < W ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ∧
      (∀ d, PassCut d R a b W) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) ∧
      steps (T - k) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t) := by
  obtain ⟨k₀, hk₀⟩ := blank_prefix
  rcases blank_halt_pass_from cleanGamma directWidth prefixWidth k₀ (by decide) stepsBelow_direct
      (fun d W => (cleanTreeGE directWidth d).cutMem [(W : Int) / 2, 0] = true)
      (fun d W hW h => clean_tree_entry_step directWidth d W (by decide) hW h) (by decide) (by decide) hk₀ T hT with
      h | ⟨R, a, b, W, k, hlt, -, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨R, a, b, W, k, hlt, h⟩

/-- **The same, checked by the kernel alone.**  `blank_halt_pass_from` from the kernel's prefix to 2²⁰
(`blank_prefix_kernel`) with `clean_entry_step_kernel`: if the machine, started on blank tape, halts after T steps,
then either it reaches a clean tape of even width W ≥ 2²⁰ that is cut at every depth, by `cleanTreeG 2²⁰ d` if
W < 2²⁴ and by `cleanTreeGE 2²⁴ d` if not, or a pass start of width W ≥ 2²⁴ with every gap at least 448 that lies in
a cut leaf of its pass-start tree at every depth; it halts from there, and the mark model reaches a stuck configuration
from there.  Nothing here is evaluated by compiled code. -/
theorem blank_halt_pass_kernel (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    (∃ W k, kernelPrefixWidth ≤ W ∧ W % 2 = 0 ∧
      (W < 2 ^ 24 → ∀ d, (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      (2 ^ 24 ≤ W → ∀ d, (cleanTreeGE (2 ^ 24) d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
    ∃ R a b W k, 2 ^ 24 ≤ W ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ∧
      (∀ d, PassCut d R a b W) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) ∧
      steps (T - k) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t) := by
  obtain ⟨k₀, hk₀⟩ := blank_prefix_kernel
  rcases blank_halt_pass_from kernelPrefixWidth kernelPrefixWidth kernelPrefixWidth k₀ (by decide)
      (stepsBelow_self _) _ clean_entry_step_kernel (by decide) (Nat.le_refl _) hk₀ T hT with
      ⟨W, k, h1, h2, hcut, h3⟩ | ⟨R, a, b, W, k, -, h⟩
  · exact Or.inl ⟨W, k, h1, h2, fun hl d => (hcut d).1 hl, fun hl d => (hcut d).2 hl, h3⟩
  · exact Or.inr ⟨R, a, b, W, k, h⟩

/-! ## The open clean tapes, and past the loop's end from them

`blank_halt_clean_direct` and `blank_halt_pass` follow the same halting run with two trees: the clean-tape tree, and
the same tree with loop entries.  Where the second stops at a loop entry, the first follows the run on through the
loop, so the pass starts of `blank_halt_pass` are reached only from clean tapes that the first tree leaves open at every
depth.  `clean_entry_chain_open` is `clean_entry_chain` with the step taken only where the clean tape is not cut at
every depth, recording a property `P` of the clean tape from which it reaches a loop entry; with `P` "cut at every
depth by the clean-tape tree", `blank_halt_open` puts the two statements together. -/

/-- **The chain, recording the clean tape before the entry.**  As `clean_entry_chain`, with a step (`hStep`) that is
taken only from a clean tape not cut at every depth, and that records a property `P` of the clean tape when it ends at
a loop entry.  If the machine halts T steps after a clean tape of even width W ≥ A, then it reaches a clean tape of
even width W′ ≥ W, W′ ≥ B, cut at every depth, and halts from there; or it reaches a clean tape of even width W₀ ≥ W,
W₀ ≥ B, with `P W₀`, and from there a loop entry wider than W₀ that cannot close, of which `Q` holds with the time
left. -/
theorem clean_entry_chain_open (A B : Nat) (h6 : 6 ≤ A) (hB : StepsBelow A B)
    (Cut : Nat → Nat → Prop) (P : Nat → Prop)
    (hStep : ∀ W, W % 2 = 0 → B ≤ W → ¬ (∀ d, Cut d W) →
      ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
        steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
        ((0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W') ∨ (P W ∧ EntryNoClose ms' W' ∧ W < W')))
    (Q : List Mark → Nat → Nat → Prop)
    (hQ : ∀ ms W T, EntryNoClose ms W → steps T (roundStart ms W) = none →
      Q ms W T ∨ ∃ k W', 0 < k ∧ W < W' ∧ W' % 2 = 0 ∧
        steps k (roundStart ms W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧
        steps (T - k) (roundStart [⟨.M, W' - 2⟩] W') = none)
    (T : Nat) : ∀ W, W % 2 = 0 → A ≤ W → steps T (roundStart [⟨.M, W - 2⟩] W) = none →
      (∃ W' k, W ≤ W' ∧ B ≤ W' ∧ W' % 2 = 0 ∧ (∀ d, Cut d W') ∧
        steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧
        steps (T - k) (roundStart [⟨.M, W' - 2⟩] W') = none) ∨
      ∃ W₀ k₀ ms' W' k, W ≤ W₀ ∧ B ≤ W₀ ∧ W₀ % 2 = 0 ∧ P W₀ ∧
        steps k₀ (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.M, W₀ - 2⟩] W₀) ∧
        W₀ < W' ∧ EntryNoClose ms' W' ∧
        steps k (roundStart [⟨.M, W₀ - 2⟩] W₀) = some (roundStart ms' W') ∧ Q ms' W' (T - k₀ - k) := by
  induction T using Nat.strongRecOn with
  | ind T ih =>
    intro W hW hA hT
    have hG6 : 6 ≤ W := by omega
    by_cases hstop : B ≤ W ∧ ∀ d, Cut d W
    · exact Or.inl ⟨W, 0, Nat.le_refl _, hstop.1, hW, hstop.2, rfl, by simpa using hT⟩
    -- otherwise the run reaches a loop entry where `Q` holds, or a wider clean tape, and the chain goes on from there
    suffices hnext : (∃ ms' W' k, B ≤ W ∧ P W ∧ W < W' ∧ EntryNoClose ms' W' ∧
        steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧ Q ms' W' (T - k)) ∨
        ∃ k W', 0 < k ∧ W < W' ∧ W' % 2 = 0 ∧
          steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.M, W' - 2⟩] W') by
      rcases hnext with ⟨ms', W', k, hBW, hP, hlt, he, hk, hq⟩ | ⟨k, W', hk0, hlt, hW', hk⟩
      · exact Or.inr ⟨W, 0, ms', W', k, Nat.le_refl _, hBW, hW, hP, rfl, hlt, he, hk, by simpa using hq⟩
      obtain ⟨hle, hT'⟩ := steps_none_split hT hk
      rcases ih (T - k) (by omega) W' hW' (by omega) hT' with ⟨W'', k'', h1, h2, h3, h4, h5, h6⟩ |
          ⟨W₀, k₀, ms'', W'', k'', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      · refine Or.inl ⟨W'', k + k'', by omega, h2, h3, h4, steps_seq hk h5, ?_⟩
        rw [show T - (k + k'') = T - k - k'' by omega]
        exact h6
      · refine Or.inr ⟨W₀, k + k₀, ms'', W'', k'', by omega, h2, h3, h4, steps_seq hk h5, h6, h7, h8, ?_⟩
        rw [show T - (k + k₀) - k'' = T - k - k₀ - k'' by omega]
        exact h9
    by_cases hb : W < B
    · obtain ⟨n, k, W', hr, hk, -, hlt⟩ := hB W hW hA hb
      obtain ⟨hW', hk0⟩ := clean_next hW hG6 hlt hr hk
      exact Or.inr ⟨k, W', hk0, hlt, hW', hk⟩
    obtain ⟨n, k, ms', W', hr, hk, hc⟩ := hStep W hW (by omega) (fun hall => hstop ⟨by omega, hall⟩)
    rcases hc with ⟨-, rfl, hlt⟩ | ⟨hP, he, hlt⟩
    · obtain ⟨hW', hk0⟩ := clean_next hW hG6 hlt hr hk
      exact Or.inr ⟨k, W', hk0, hlt, hW', hk⟩
    · obtain ⟨-, hT'⟩ := steps_none_split hT hk
      rcases hQ ms' W' (T - k) he hT' with hq | ⟨k', W'', hk', hlt', hW'', hk'', -⟩
      · exact Or.inl ⟨ms', W', k, by omega, hP, hlt, he, hk, hq⟩
      · exact Or.inr ⟨k + k', W'', by omega, by omega, hW'', steps_seq hk hk''⟩

/-- **A halt from blank tape, after a prefix: an open clean tape, and past the loop's end from it.**  Two notions of
cut class, `CutG` with a step that ends at a wider clean tape (`hStepG`, the clean-tape tree) and `CutE` with a step
that may also end at a loop entry that cannot close (`hStepE`, the tree with loop entries).  If the machine halts after
T steps, then it reaches a clean tape of even width W ≥ B that is cut at every depth by the first, halts from there,
and either W is cut at every depth by the second too, and the mark model reaches a stuck configuration from W; or the
run from W reaches a pass start of width W₁ > W, W₁ ≥ 2²⁴, with every gap at least 448, that lies in a cut leaf of its
pass-start tree at every depth (through a loop entry that cannot close and the loop's chain from it), halts from there,
and the mark model reaches a stuck configuration from there. -/
theorem blank_halt_open_from (A B W₀ k₀ : Nat) (h6 : 6 ≤ A) (hB : StepsBelow A B)
    (CutG CutE : Nat → Nat → Prop)
    (hStepG : ∀ d W, W % 2 = 0 → B ≤ W →
      ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
        steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
        (CutG d W ∨ (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W')))
    (hStepE : ∀ d W, W % 2 = 0 → B ≤ W →
      ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
        steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
        (CutE d W ∨ (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W') ∨ (EntryNoClose ms' W' ∧ W < W')))
    (hW₀ : W₀ % 2 = 0) (hAW₀ : A ≤ W₀) (hk₀ : steps k₀ ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W₀ - 2⟩] W₀))
    (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, B ≤ W ∧ W % 2 = 0 ∧ (∀ d, CutG d W) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      (((∀ d, CutE d W) ∧
          ∃ u, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ u ∧ u.wf ∧ (EndClose u ∨ InteriorContact u)) ∨
        ∃ R a b W₁ t, W < W₁ ∧ 2 ^ 24 ≤ W₁ ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R ∧
          (∀ d, PassCut d R a b W₁) ∧
          steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ∧
          steps (T - k - t) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) = none ∧
          ∃ u, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩], W₁⟩ u ∧ u.wf ∧
            (EndClose u ∨ InteriorContact u)) := by
  obtain ⟨-, hT₀⟩ := steps_none_split hT hk₀
  -- the step: by the clean-tape tree where it does not cut at every depth, else by the tree with loop entries
  have hStep : ∀ W, W % 2 = 0 → B ≤ W → ¬ (∀ d, CutG d W ∧ CutE d W) →
      ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
        steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
        ((0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W') ∨ ((∀ d, CutG d W) ∧ EntryNoClose ms' W' ∧ W < W')) := by
    intro W hW hBW hn
    by_cases hG : ∀ d, CutG d W
    · obtain ⟨d, hd⟩ := Classical.not_forall.mp (fun hE : ∀ d, CutE d W => hn fun d => ⟨hG d, hE d⟩)
      obtain ⟨n, k, ms', W', hr, hk, hc⟩ := hStepE d W hW hBW
      rcases hc with hc | hc | ⟨he, hlt⟩
      · exact absurd hc hd
      · exact ⟨n, k, ms', W', hr, hk, Or.inl hc⟩
      · exact ⟨n, k, ms', W', hr, hk, Or.inr ⟨hG, he, hlt⟩⟩
    · obtain ⟨d, hd⟩ := Classical.not_forall.mp hG
      obtain ⟨n, k, ms', W', hr, hk, hc⟩ := hStepG d W hW hBW
      rcases hc with hc | hc
      · exact absurd hc hd
      · exact ⟨n, k, ms', W', hr, hk, Or.inl hc⟩
  rcases clean_entry_chain_open A B h6 hB (fun d W => CutG d W ∧ CutE d W) (fun W => ∀ d, CutG d W) hStep
      (fun ms W T' => ∃ R ks a₁ b₁ W₁ R₁ t, LoopChain ms W R ks [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧
        (∀ d, PassCut d R₁ a₁ b₁ W₁) ∧
        steps t (roundStart ms W) = some (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) ∧
        steps (T' - t) (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) = none)
      (fun _ _ T' he hT' => entry_pass_halt he T' hT') (T - k₀) W₀ hW₀ hAW₀ hT₀ with
      ⟨W, k, hle, hBW, hW, hcut, hk, hTW⟩ |
      ⟨W, k, ms, W', k', -, hBW, hW, hG, hk, hlt, he, hk', R, ks, a₁, b₁, W₁, R₁, t, hch, hcut, ht, hT₁⟩
  · have hG6 : 6 ≤ W := by omega
    obtain ⟨u, hu, huw, hus⟩ := round_halt_needs_contact [⟨.M, W - 2⟩] W _ (roundWF_one.mpr ⟨hG6, hW⟩)
      (noG_one _) hTW
    refine ⟨W, k₀ + k, hBW, hW, fun d => (hcut d).1, steps_seq hk₀ hk, ?_,
      Or.inl ⟨fun d => (hcut d).2, u, hu, huw, stuck_cases hus⟩⟩
    rw [show T - (k₀ + k) = T - k₀ - k by omega]
    exact hTW
  · -- the chain only widens, from the entry's width W' ≥ 2²⁴
    have hW₁ := hch.width
    have h24 : 2 ^ 24 ≤ W₁ := Nat.le_trans he.1 (by omega)
    have hP₁ := hch.last
    obtain ⟨hwf, hGP⟩ := hP₁.wf
    obtain ⟨u, hu, huw, hus⟩ := round_halt_needs_contact _ W₁ _ hwf hGP hT₁
    obtain ⟨-, hTW⟩ := steps_none_split hT₀ hk
    refine ⟨W, k₀ + k, hBW, hW, hG, steps_seq hk₀ hk, ?_,
      Or.inr ⟨R₁, a₁, b₁, W₁, k' + t, by omega, h24, hP₁, hcut, steps_seq hk' ht, ?_, u, hu, huw, stuck_cases hus⟩⟩
    · rw [show T - (k₀ + k) = T - k₀ - k by omega]
      exact hTW
    · rw [show T - (k₀ + k) - (k' + t) = T - k₀ - k - k' - t by omega]
      exact hT₁

/-- **What a halt from blank tape needs: an open clean tape, and past the loop's end from it.**
`blank_halt_open_from` with the prefix to 2³² (`blank_prefix`), the clean tapes of width in [2³², 2⁴¹) run one by one
(`stepsBelow_direct`), the clean-tape tree over the widths ≥ 2⁴¹ (`clean_tree_step_G`) and the same tree with loop
entries (`clean_tree_entry_step`): if the machine, started on blank tape, halts after T steps, then it reaches a clean
tape of even width W ≥ 2⁴¹ with W/2 in a cut class of `cleanTreeG directWidth d` at every depth, and halts from there;
and either W/2 is also in a cut class of `cleanTreeGE directWidth d` at every depth, and the mark model reaches a stuck
configuration from W, or the run from W reaches a pass start wider than W with every gap at least 448 that lies in a
cut leaf of its pass-start tree at every depth (`PassCut`), halts from there, and the mark model reaches a stuck
configuration from there.  So the pass starts of `blank_halt_pass` come only after the clean tapes of
`blank_halt_clean_direct`. -/
theorem blank_halt_open (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      (((∀ d, (cleanTreeGE directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
          ∃ u, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ u ∧ u.wf ∧ (EndClose u ∨ InteriorContact u)) ∨
        ∃ R a b W₁ t, W < W₁ ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R ∧
          (∀ d, PassCut d R a b W₁) ∧
          steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ∧
          steps (T - k - t) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) = none ∧
          ∃ u, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩], W₁⟩ u ∧ u.wf ∧
            (EndClose u ∨ InteriorContact u)) := by
  obtain ⟨k₀, hk₀⟩ := blank_prefix
  obtain ⟨W, k, h1, h2, h3, h4, h5, h | ⟨R, a, b, W₁, t, hlt, -, h⟩⟩ :=
    blank_halt_open_from cleanGamma directWidth prefixWidth k₀ (by decide) stepsBelow_direct
      (fun d W => (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true)
      (fun d W => (cleanTreeGE directWidth d).cutMem [(W : Int) / 2, 0] = true)
      (fun d W hW h => clean_tree_step_G directWidth d W (by decide) hW h)
      (fun d W hW h => clean_tree_entry_step directWidth d W (by decide) hW h) (by decide) (by decide) hk₀ T hT
  · exact ⟨W, k, h1, h2, h3, h4, h5, Or.inl h⟩
  · exact ⟨W, k, h1, h2, h3, h4, h5, Or.inr ⟨R, a, b, W₁, t, hlt, h⟩⟩

/-- **The same, checked by the kernel alone.**  `blank_halt_open_from` from the kernel's prefix to 2²⁰
(`blank_prefix_kernel`), with the clean-tape tree over the widths ≥ 2²⁰ and `clean_entry_step_kernel`: if the machine,
started on blank tape, halts after T steps, then it reaches a clean tape of even width W ≥ 2²⁰ with W/2 in a cut class
of `cleanTreeG 2²⁰ d` at every depth, and halts from there; and either, if W ≥ 2²⁴, W/2 is also in a cut class of
`cleanTreeGE 2²⁴ d` at every depth, and the mark model reaches a stuck configuration from W, or the run from W reaches
a pass start wider than W and 2²⁴ with every gap at least 448 that lies in a cut leaf of its pass-start tree at every
depth, halts from there, and the mark model reaches a stuck configuration from there.  Nothing here is evaluated by
compiled code. -/
theorem blank_halt_open_kernel (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, kernelPrefixWidth ≤ W ∧ W % 2 = 0 ∧
      (∀ d, (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      (((2 ^ 24 ≤ W → ∀ d, (cleanTreeGE (2 ^ 24) d).cutMem [(W : Int) / 2, 0] = true) ∧
          ∃ u, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ u ∧ u.wf ∧ (EndClose u ∨ InteriorContact u)) ∨
        ∃ R a b W₁ t, W < W₁ ∧ 2 ^ 24 ≤ W₁ ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R ∧
          (∀ d, PassCut d R a b W₁) ∧
          steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ∧
          steps (T - k - t) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) = none ∧
          ∃ u, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩], W₁⟩ u ∧ u.wf ∧
            (EndClose u ∨ InteriorContact u)) := by
  obtain ⟨k₀, hk₀⟩ := blank_prefix_kernel
  obtain ⟨W, k, h1, h2, h3, h4, h5, ⟨hcut, h⟩ | h⟩ :=
    blank_halt_open_from kernelPrefixWidth kernelPrefixWidth kernelPrefixWidth k₀ (by decide)
      (stepsBelow_self _)
      (fun d W => (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) _
      (fun d W hW h => clean_tree_step_G kernelPrefixWidth d W (by decide) hW h) clean_entry_step_kernel
      (by decide) (Nat.le_refl _) hk₀ T hT
  · exact ⟨W, k, h1, h2, h3, h4, h5, Or.inl ⟨fun hl d => (hcut d).2 hl, h⟩⟩
  · exact ⟨W, k, h1, h2, h3, h4, h5, Or.inr h⟩

#print axioms entry_pass_halt
#print axioms blank_halt_pass
#print axioms blank_halt_pass_kernel
#print axioms blank_halt_open
#print axioms blank_halt_open_kernel
