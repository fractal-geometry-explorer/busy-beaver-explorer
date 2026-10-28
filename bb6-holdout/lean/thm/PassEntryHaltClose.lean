import PassEntryHalt
import PassHaltClose
import RouteEntryHaltC
open BB6 BB6.Sym

/-! # From blank tape, past the loop's end, with end meetings at distance 2 passed

`thm/PassEntryHalt.lean` with the narrower closing classes of `closeClassC` on both sides of the loop's end: the loop
entries that cannot close in a class of `closeClassC` (`EntryNoCloseC`, and the clean-tape tree `cleanTreeGEC` that
stops at them, `thm/RouteEntryHaltC.lean`), and the pass-start trees with those classes at their close leaves
(`pass_halt_chain_close`, `PassCutC`, `thm/PassHaltClose.lean`).  From a loop entry of `EntryNoCloseC` the chain
reaches no class of `closeClassC` (`EntryNoCloseC.no_close`), so a halt from the entry needs a pass start cut at every
depth of its tree, or a wider clean tape (`entry_pass_halt_close`).  `blank_halt_pass_close` and
`blank_halt_open_close` (and their kernel versions, with nothing evaluated by compiled code) are `blank_halt_pass` and
`blank_halt_open` so: a halt from blank tape needs a clean tape in a cut class of the clean-tape tree at every depth,
or a pass start in a cut class of its pass-start tree at every depth, reached through a loop entry that cannot close
in a class of `closeClassC`.  Every loop entry of `EntryNoClose` is one of `EntryNoCloseC` (`EntryNoClose.toC`), so
these trees stop at least where the older ones do. -/

/-- **A halt from a loop entry that cannot close in a class of `closeClassC`.**  `entry_pass_halt` with
`pass_halt_chain_close` and `EntryNoCloseC.no_close`: if the machine halts T steps after such an entry, then its run
follows the loop's chain (`LoopChain`) to a last pass start with walls a₁, b₁ and W₁ − R₁ − 1 that lies in a cut leaf
of its pass-start tree at every depth (`PassCutC`), which it reaches after t steps and halts from; or it reaches a
one-marker clean tape of even width W′ > W after k > 0 steps, and halts from there. -/
theorem entry_pass_halt_close {ms : List Mark} {W : Nat} (h : EntryNoCloseC ms W) (T : Nat)
    (hT : steps T (roundStart ms W) = none) :
    (∃ R ks a₁ b₁ W₁ R₁ t, LoopChain ms W R ks [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧
      (∀ d, PassCutC d R₁ a₁ b₁ W₁) ∧
      steps t (roundStart ms W) = some (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) ∧
      steps (T - t) (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) = none) ∨
    ∃ k W', 0 < k ∧ W < W' ∧ W' % 2 = 0 ∧
      steps k (roundStart ms W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧
      steps (T - k) (roundStart [⟨.M, W' - 2⟩] W') = none := by
  obtain ⟨hW, R, a, b, rfl, hP, hh, -⟩ := id h
  obtain ⟨ks, a₁, b₁, W₁, R₁, hch, -, hend⟩ :=
    pass_halt_chain_close T R a b W hP (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by decide)) hW) hh hT
  rcases hend with ⟨hc, -⟩ | hcut | ⟨k, W', hk, -, hlt, hW', hs, hT'⟩
  · exact (h.no_close hch hc).elim
  · obtain ⟨t, ht⟩ := hch.reach
    exact Or.inl ⟨R, ks, a₁, b₁, W₁, R₁, t, hch, hcut, ht, (steps_none_split hT ht).2⟩
  · exact Or.inr ⟨k, W', hk, hlt, hW', hs, hT'⟩

/-- **A halt from blank tape, after a prefix, past the loop's end, with the narrower classes.**  `blank_halt_pass_from`
with loop entries of `EntryNoCloseC` and `entry_pass_halt_close` (through `clean_entry_chain_open`): if the machine
halts after T steps, then either it reaches a clean tape of even width W ≥ B that is cut at every depth, halts from
there, and the mark model, run from there, reaches a stuck configuration; or it reaches a pass start of width W > B,
W ≥ 2²⁴, with walls a, b and W − R − 1 and every gap at least 448 (`PassStart448`), that lies in a cut leaf of its
pass-start tree at every depth (`PassCutC`), halts from there, and the mark model reaches a stuck configuration from
there. -/
theorem blank_halt_pass_from_close (A B W₀ k₀ : Nat) (h6 : 6 ≤ A) (hB : StepsBelow A B)
    (Cut : Nat → Nat → Prop)
    (hStep : ∀ d W, W % 2 = 0 → B ≤ W →
      ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
        steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
        (Cut d W ∨ (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W') ∨ (EntryNoCloseC ms' W' ∧ W < W')))
    (hW₀ : W₀ % 2 = 0) (hAW₀ : A ≤ W₀) (hk₀ : steps k₀ ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W₀ - 2⟩] W₀))
    (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    (∃ W k, B ≤ W ∧ W % 2 = 0 ∧ (∀ d, Cut d W) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
    ∃ R a b W k, B < W ∧ 2 ^ 24 ≤ W ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ∧
      (∀ d, PassCutC d R a b W) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) ∧
      steps (T - k) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t) := by
  obtain ⟨-, hT₀⟩ := steps_none_split hT hk₀
  -- the step at a clean tape that is not cut at every depth, from the tree at a depth where it is not cut
  have hStep' : ∀ W, W % 2 = 0 → B ≤ W → ¬ (∀ d, Cut d W) →
      ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
        steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
        ((0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W') ∨ (True ∧ EntryNoCloseC ms' W' ∧ W < W')) := by
    intro W hW hBW hn
    obtain ⟨d, hd⟩ := Classical.not_forall.mp hn
    obtain ⟨n, k, ms', W', hr, hk, hc⟩ := hStep d W hW hBW
    rcases hc with hc | hc | ⟨he, hlt⟩
    · exact absurd hc hd
    · exact ⟨n, k, ms', W', hr, hk, Or.inl hc⟩
    · exact ⟨n, k, ms', W', hr, hk, Or.inr ⟨trivial, he, hlt⟩⟩
  rcases clean_entry_chain_open A B h6 hB Cut (fun _ => True) EntryNoCloseC hStep'
      (fun ms W T' => ∃ R ks a₁ b₁ W₁ R₁ t, LoopChain ms W R ks [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧
        (∀ d, PassCutC d R₁ a₁ b₁ W₁) ∧
        steps t (roundStart ms W) = some (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) ∧
        steps (T' - t) (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) = none)
      (fun _ _ T' he hT' => entry_pass_halt_close he T' hT') (T - k₀) W₀ hW₀ hAW₀ hT₀ with
      ⟨W, k, hle, hBW, hW, hcut, hk, hTW⟩ |
        ⟨W₂, k₂, ms, W, k, -, hBW₂, -, -, hk₂, hlt, he, hk, R, ks, a₁, b₁, W₁, R₁, t, hch, hcut, ht, hT₁⟩
  · have hG6 : 6 ≤ W := by omega
    obtain ⟨u, hu, huw, hus⟩ := round_halt_needs_contact [⟨.M, W - 2⟩] W _ (roundWF_one.mpr ⟨hG6, hW⟩)
      (noG_one _) hTW
    refine Or.inl ⟨W, k₀ + k, hBW, hW, hcut, steps_seq hk₀ hk, ?_, u, hu, huw, stuck_cases hus⟩
    rw [show T - (k₀ + k) = T - k₀ - k by omega]
    exact hTW
  · -- the chain only widens, from the entry's width W ≥ 2²⁴
    obtain ⟨hle, hP₁, u, hu, huw, hus⟩ := hch.last_halt hT₁
    refine Or.inr ⟨R₁, a₁, b₁, W₁, k₀ + k₂ + k + t, by omega, Nat.le_trans he.1 hle, hP₁, hcut,
      steps_seq (steps_seq (steps_seq hk₀ hk₂) hk) ht, ?_, u, hu, huw, hus⟩
    rw [show T - (k₀ + k₂ + k + t) = T - k₀ - k₂ - k - t by omega]
    exact hT₁

/-- **What a halt from blank tape needs, with the narrower classes.**  `blank_halt_pass` with `cleanTreeGEC` and
`entry_pass_halt_close`: if the machine, started on blank tape, halts after T steps, then either it reaches a clean
tape of even width W ≥ 2⁴¹ with W/2 in a cut class of `cleanTreeGEC directWidth d` at every depth, or a pass start of
width W > 2⁴¹ with every gap at least 448 that lies in a cut leaf of its pass-start tree at every depth (`PassCutC`); it
halts from there, and the mark model reaches a stuck configuration from there. -/
theorem blank_halt_pass_close (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    (∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeGEC directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
    ∃ R a b W k, directWidth < W ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ∧
      (∀ d, PassCutC d R a b W) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) ∧
      steps (T - k) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t) := by
  obtain ⟨k₀, hk₀⟩ := blank_prefix
  rcases blank_halt_pass_from_close cleanGamma directWidth prefixWidth k₀ (by decide) stepsBelow_direct
      (fun d W => (cleanTreeGEC directWidth d).cutMem [(W : Int) / 2, 0] = true)
      (fun d W hW h => clean_tree_entry_stepC directWidth d W (by decide) hW h) (by decide) (by decide) hk₀ T hT with
      h | ⟨R, a, b, W, k, hlt, -, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨R, a, b, W, k, hlt, h⟩

/-- `clean_entry_step_kernel` with `cleanTreeGEC`: from every clean tape of even width W ≥ 2²⁰, the plain clean-tape
tree over the widths ≥ 2²⁰ below 2²⁴, and the tree with loop entries of `EntryNoCloseC` over the widths ≥ 2²⁴ above. -/
theorem clean_entry_step_kernel_close (d W : Nat) (hW : W % 2 = 0) (h : kernelPrefixWidth ≤ W) :
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
      (((W < 2 ^ 24 → (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
          (2 ^ 24 ≤ W → (cleanTreeGEC (2 ^ 24) d).cutMem [(W : Int) / 2, 0] = true)) ∨
        (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W') ∨ (EntryNoCloseC ms' W' ∧ W < W')) := by
  by_cases hl : W < 2 ^ 24
  · obtain ⟨n, k, ms', W', hr, hk, hc⟩ := clean_tree_step_G kernelPrefixWidth d W (by decide) hW h
    refine ⟨n, k, ms', W', hr, hk, ?_⟩
    rcases hc with hc | hc
    · exact Or.inl ⟨fun _ => hc, fun h' => absurd h' (Nat.not_le.mpr hl)⟩
    · exact Or.inr (Or.inl hc)
  · obtain ⟨n, k, ms', W', hr, hk, hc⟩ :=
      clean_tree_entry_stepC (2 ^ 24) d W (by decide) hW (Nat.le_of_not_lt hl)
    refine ⟨n, k, ms', W', hr, hk, ?_⟩
    rcases hc with hc | hc | hc
    · exact Or.inl ⟨fun h' => absurd h' hl, fun _ => hc⟩
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr hc)

/-- **The same, checked by the kernel alone.**  `blank_halt_pass_from_close` from the kernel's prefix to 2²⁰
(`blank_prefix_kernel`) with `clean_entry_step_kernel_close`: if the machine, started on blank tape, halts after T
steps, then either it reaches a clean tape of even width W ≥ 2²⁰ that is cut at every depth, by `cleanTreeG 2²⁰ d` if
W < 2²⁴ and by `cleanTreeGEC 2²⁴ d` if not, or a pass start of width W ≥ 2²⁴ with every gap at least 448 that lies in a
cut leaf of its pass-start tree at every depth (`PassCutC`); it halts from there, and the mark model reaches a stuck
configuration from there.  Nothing here is evaluated by compiled code. -/
theorem blank_halt_pass_kernel_close (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    (∃ W k, kernelPrefixWidth ≤ W ∧ W % 2 = 0 ∧
      (W < 2 ^ 24 → ∀ d, (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      (2 ^ 24 ≤ W → ∀ d, (cleanTreeGEC (2 ^ 24) d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
    ∃ R a b W k, 2 ^ 24 ≤ W ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ∧
      (∀ d, PassCutC d R a b W) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) ∧
      steps (T - k) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t) := by
  obtain ⟨k₀, hk₀⟩ := blank_prefix_kernel
  rcases blank_halt_pass_from_close kernelPrefixWidth kernelPrefixWidth kernelPrefixWidth k₀ (by decide)
      (stepsBelow_self _) _ clean_entry_step_kernel_close (by decide) (Nat.le_refl _) hk₀ T hT with
      ⟨W, k, h1, h2, hcut, h3⟩ | ⟨R, a, b, W, k, -, h⟩
  · exact Or.inl ⟨W, k, h1, h2, fun hl d => (hcut d).1 hl, fun hl d => (hcut d).2 hl, h3⟩
  · exact Or.inr ⟨R, a, b, W, k, h⟩

/-! ## The open clean tapes, and past the loop's end from them -/

/-- **A halt from blank tape, after a prefix: an open clean tape, and past the loop's end from it, with the narrower
classes.**  `blank_halt_open_from` with loop entries of `EntryNoCloseC` and `entry_pass_halt_close`: if the machine
halts after T steps, then it reaches a clean tape of even width W ≥ B that is cut at every depth by the first notion,
halts from there, and either W is cut at every depth by the second too, and the mark model reaches a stuck configuration
from W; or the run from W reaches a pass start of width W₁ > W, W₁ ≥ 2²⁴, with every gap at least 448, that lies in a
cut leaf of its pass-start tree at every depth (`PassCutC`), halts from there, and the mark model reaches a stuck
configuration from there. -/
theorem blank_halt_open_from_close (A B W₀ k₀ : Nat) (h6 : 6 ≤ A) (hB : StepsBelow A B)
    (CutG CutE : Nat → Nat → Prop)
    (hStepG : ∀ d W, W % 2 = 0 → B ≤ W →
      ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
        steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
        (CutG d W ∨ (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W')))
    (hStepE : ∀ d W, W % 2 = 0 → B ≤ W →
      ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
        steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
        (CutE d W ∨ (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W') ∨ (EntryNoCloseC ms' W' ∧ W < W')))
    (hW₀ : W₀ % 2 = 0) (hAW₀ : A ≤ W₀) (hk₀ : steps k₀ ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W₀ - 2⟩] W₀))
    (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, B ≤ W ∧ W % 2 = 0 ∧ (∀ d, CutG d W) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      (((∀ d, CutE d W) ∧
          ∃ u, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ u ∧ u.wf ∧ (EndClose u ∨ InteriorContact u)) ∨
        ∃ R a b W₁ t, W < W₁ ∧ 2 ^ 24 ≤ W₁ ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R ∧
          (∀ d, PassCutC d R a b W₁) ∧
          steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ∧
          steps (T - k - t) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) = none ∧
          ∃ u, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩], W₁⟩ u ∧ u.wf ∧
            (EndClose u ∨ InteriorContact u)) := by
  obtain ⟨W, k, hBW, hW, hG, hk, hTW, h | ⟨ms, W', t, hlt, he, ht, R, ks, a₁, b₁, W₁, R₁, t', hch, hcut, ht', hT₁⟩⟩ :=
    blank_halt_open_of A B W₀ k₀ h6 hB CutG CutE EntryNoCloseC hStepG hStepE
      (fun ms W T' => ∃ R ks a₁ b₁ W₁ R₁ t, LoopChain ms W R ks [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧
        (∀ d, PassCutC d R₁ a₁ b₁ W₁) ∧
        steps t (roundStart ms W) = some (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) ∧
        steps (T' - t) (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) = none)
      (fun _ _ T' he hT' => entry_pass_halt_close he T' hT') hW₀ hAW₀ hk₀ T hT
  · exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inl h⟩
  · -- the chain only widens, from the entry's width W' ≥ 2²⁴
    obtain ⟨hle, hP₁, u, hu, huw, hus⟩ := hch.last_halt hT₁
    refine ⟨W, k, hBW, hW, hG, hk, hTW, Or.inr ⟨R₁, a₁, b₁, W₁, t + t', by omega, Nat.le_trans he.1 hle, hP₁, hcut,
      steps_seq ht ht', ?_, u, hu, huw, hus⟩⟩
    rw [show T - k - (t + t') = T - k - t - t' by omega]
    exact hT₁

/-- **What a halt from blank tape needs: an open clean tape, and past the loop's end from it, with the narrower
classes.**  `blank_halt_open` with `cleanTreeGEC` and `entry_pass_halt_close`: if the machine, started on blank tape,
halts after T steps, then it reaches a clean tape of even width W ≥ 2⁴¹ with W/2 in a cut class of
`cleanTreeG directWidth d` at every depth, and halts from there; and either W/2 is also in a cut class of
`cleanTreeGEC directWidth d` at every depth, and the mark model reaches a stuck configuration from W, or the run from W
reaches a pass start wider than W with every gap at least 448 that lies in a cut leaf of its pass-start tree at every
depth (`PassCutC`), halts from there, and the mark model reaches a stuck configuration from there. -/
theorem blank_halt_open_close (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      (((∀ d, (cleanTreeGEC directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
          ∃ u, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ u ∧ u.wf ∧ (EndClose u ∨ InteriorContact u)) ∨
        ∃ R a b W₁ t, W < W₁ ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R ∧
          (∀ d, PassCutC d R a b W₁) ∧
          steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ∧
          steps (T - k - t) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) = none ∧
          ∃ u, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩], W₁⟩ u ∧ u.wf ∧
            (EndClose u ∨ InteriorContact u)) := by
  obtain ⟨k₀, hk₀⟩ := blank_prefix
  obtain ⟨W, k, h1, h2, h3, h4, h5, h | ⟨R, a, b, W₁, t, hlt, -, h⟩⟩ :=
    blank_halt_open_from_close cleanGamma directWidth prefixWidth k₀ (by decide) stepsBelow_direct
      (fun d W => (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true)
      (fun d W => (cleanTreeGEC directWidth d).cutMem [(W : Int) / 2, 0] = true)
      (fun d W hW h => clean_tree_step_G directWidth d W (by decide) hW h)
      (fun d W hW h => clean_tree_entry_stepC directWidth d W (by decide) hW h) (by decide) (by decide) hk₀ T hT
  · exact ⟨W, k, h1, h2, h3, h4, h5, Or.inl h⟩
  · exact ⟨W, k, h1, h2, h3, h4, h5, Or.inr ⟨R, a, b, W₁, t, hlt, h⟩⟩

/-- **The same, checked by the kernel alone.**  `blank_halt_open_from_close` from the kernel's prefix to 2²⁰
(`blank_prefix_kernel`), with the clean-tape tree over the widths ≥ 2²⁰ and `clean_entry_step_kernel_close`: if the
machine, started on blank tape, halts after T steps, then it reaches a clean tape of even width W ≥ 2²⁰ with W/2 in a
cut class of `cleanTreeG 2²⁰ d` at every depth, and halts from there; and either, if W ≥ 2²⁴, W/2 is also in a cut
class of `cleanTreeGEC 2²⁴ d` at every depth, and the mark model reaches a stuck configuration from W, or the run from
W reaches a pass start wider than W and 2²⁴ with every gap at least 448 that lies in a cut leaf of its pass-start tree
at every depth (`PassCutC`), halts from there, and the mark model reaches a stuck configuration from there.  Nothing
here is evaluated by compiled code. -/
theorem blank_halt_open_kernel_close (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, kernelPrefixWidth ≤ W ∧ W % 2 = 0 ∧
      (∀ d, (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      (((2 ^ 24 ≤ W → ∀ d, (cleanTreeGEC (2 ^ 24) d).cutMem [(W : Int) / 2, 0] = true) ∧
          ∃ u, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ u ∧ u.wf ∧ (EndClose u ∨ InteriorContact u)) ∨
        ∃ R a b W₁ t, W < W₁ ∧ 2 ^ 24 ≤ W₁ ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R ∧
          (∀ d, PassCutC d R a b W₁) ∧
          steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ∧
          steps (T - k - t) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) = none ∧
          ∃ u, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩], W₁⟩ u ∧ u.wf ∧
            (EndClose u ∨ InteriorContact u)) := by
  obtain ⟨k₀, hk₀⟩ := blank_prefix_kernel
  obtain ⟨W, k, h1, h2, h3, h4, h5, ⟨hcut, h⟩ | h⟩ :=
    blank_halt_open_from_close kernelPrefixWidth kernelPrefixWidth kernelPrefixWidth k₀ (by decide)
      (stepsBelow_self _)
      (fun d W => (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) _
      (fun d W hW h => clean_tree_step_G kernelPrefixWidth d W (by decide) hW h) clean_entry_step_kernel_close
      (by decide) (Nat.le_refl _) hk₀ T hT
  · exact ⟨W, k, h1, h2, h3, h4, h5, Or.inl ⟨fun hl d => (hcut d).2 hl, h⟩⟩
  · exact ⟨W, k, h1, h2, h3, h4, h5, Or.inr h⟩

#print axioms entry_pass_halt_close
#print axioms blank_halt_pass_close
#print axioms blank_halt_pass_kernel_close
#print axioms blank_halt_open_close
#print axioms blank_halt_open_kernel_close
