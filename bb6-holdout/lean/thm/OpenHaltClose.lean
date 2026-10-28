import PassEntryHaltClose
import CleanTreesC
import BigEndHalt
open BB6 BB6.Sym

/-! # The small-end, wide, far and big-end halting theorems with the narrower closing classes

`thm/OpenSmallHalt.lean`, `thm/WideHalt.lean`, `thm/FarHalt.lean` and `thm/BigEndHalt.lean` with the narrower closing
classes of `closeClassC` on both sides of the loop's end: the clean-tape trees whose loop entries cannot close in a
class of `closeClassC` and pass the small-end, wide, far or big-end check (`cleanTreeGSC`, `cleanTreeGWC`,
`cleanTreeGFC`, `cleanTreeGBC`, `thm/CleanTreesC.lean`), and from those entries the chain to a last pass start cut at
every depth of its pass-start tree with the classes of `closeClassC` at its close leaves (`entry_pass_halt_close`,
`thm/PassEntryHaltClose.lean`).  That pass start has R ≥ 178 (`LoopChain.small_end`), where its tree is the tree for
every R ≥ 178, `passTreeSym`, as before (`passCutC_iff`).  So a halt from such an entry needs what a halt from the
older entries needs (`entry_small_halt_close`, `entry_wide_halt_close`, `entry_far_halt_close`, `entry_big_halt_close`,
with `SmallQ`, `WideQ`, `FarQ` and `BigQ` as before), and the pass starts left to rule out are those of
`never_halts_of_open`, `never_halts_of_wide`, `never_halts_of_far` and `never_halts_of_big`.  What changes is the
clean-tape tree with loop entries: it stops at least where the older one does, so its cut classes, the clean tapes left
to rule out with the plain tree's, are among the older tree's.  Nothing here is evaluated: the trees are built by the
proved explorer. -/

/-! ## From the loop entries -/

/-- **A halt from a loop entry that cannot close in a class of `closeClassC` nor end small.**  `entry_small_halt` with
`entry_pass_halt_close`: the chain's last pass start, cut at every depth of its pass-start tree, has right end
R₁ ≥ 178, where that tree is `passTreeSym` (`passCutC_iff`), so a halt needs what `entry_small_halt` says. -/
theorem entry_small_halt_close {ms : List Mark} {W : Nat} (hn : EntryNoCloseC ms W) (hs : EntryNoSmall ms W)
    (T : Nat) (hT : steps T (roundStart ms W) = none) :
    (∃ R ks a₁ b₁ W₁ R₁ t, LoopChain ms W R ks [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧ 178 ≤ R₁ ∧
      (∀ d, PassCut d R₁ a₁ b₁ W₁) ∧
      steps t (roundStart ms W) = some (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) ∧
      steps (T - t) (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) = none) ∨
    ∃ k W', 0 < k ∧ W < W' ∧ W' % 2 = 0 ∧
      steps k (roundStart ms W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧
      steps (T - k) (roundStart [⟨.M, W' - 2⟩] W') = none := by
  rcases entry_pass_halt_close hn T hT with ⟨R, ks, a₁, b₁, W₁, R₁, t, hch, hcut, ht, hT'⟩ | h
  · obtain ⟨a, b, hms, -, -, -, -, -, -, -, h3⟩ := hch.start
    obtain ⟨hs1, hs2⟩ := hs.2 R a b hms (by omega)
    have hR := hch.small_end hs.1 hs1 hs2
    exact Or.inl ⟨R, ks, a₁, b₁, W₁, R₁, t, hch, hR, fun d => (passCutC_iff hR).1 (hcut d), ht, hT'⟩
  · exact Or.inr h

/-- **A halt from a wide loop entry that cannot close in a class of `closeClassC` nor end small.**  `entry_wide_halt`
with `entry_small_halt_close`. -/
theorem entry_wide_halt_close {ms : List Mark} {W : Nat} (hn : EntryNoCloseC ms W) (hs : EntryNoSmall ms W)
    (hw : EntryWide ms W) (T : Nat) (hT : steps T (roundStart ms W) = none) :
    (∃ R ks a₁ b₁ W₁ R₁ t, LoopChain ms W R ks [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧ 178 ≤ R₁ ∧
      (W₁ ≤ 64 * R₁ + 6 ∨ 15 * W₁ ≤ 64 * (W₁ - b₁)) ∧ (∀ d, PassCut d R₁ a₁ b₁ W₁) ∧
      steps t (roundStart ms W) = some (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) ∧
      steps (T - t) (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) = none) ∨
    ∃ k W', 0 < k ∧ W < W' ∧ W' % 2 = 0 ∧
      steps k (roundStart ms W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧
      steps (T - k) (roundStart [⟨.M, W' - 2⟩] W') = none := by
  rcases entry_small_halt_close hn hs T hT with ⟨R, ks, a₁, b₁, W₁, R₁, t, hch, hR, hcut, ht, hT'⟩ | h
  · obtain ⟨a, b, hms, -, -, -, -, -, -, -, h3⟩ := hch.start
    have h32 := hw R a b hms (by omega)
    obtain ⟨a', b', hms', hsh⟩ := hch.wide_end ⟨a, b, hms, Or.inl (by omega)⟩ (fun _ => h32)
    simp only [List.cons.injEq, Mark.mk.injEq, true_and, and_true] at hms'
    obtain ⟨-, rfl⟩ := hms'
    exact Or.inl ⟨R, ks, a₁, b₁, W₁, R₁, t, hch, hR, hsh, hcut, ht, hT'⟩
  · exact Or.inr h

/-- **A halt from a far loop entry that cannot close in a class of `closeClassC` nor end small.**  `entry_far_halt`
with `entry_small_halt_close`. -/
theorem entry_far_halt_close {ms : List Mark} {W : Nat} (hn : EntryNoCloseC ms W) (hs : EntryNoSmall ms W)
    (hf : EntryFar ms W) (T : Nat) (hT : steps T (roundStart ms W) = none) :
    (∃ R ks a₁ b₁ W₁ R₁ t, LoopChain ms W R ks [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧ 178 ≤ R₁ ∧
      15 * W₁ ≤ 64 * (W₁ - b₁) ∧ (∀ d, PassCut d R₁ a₁ b₁ W₁) ∧
      steps t (roundStart ms W) = some (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) ∧
      steps (T - t) (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) = none) ∨
    ∃ k W', 0 < k ∧ W < W' ∧ W' % 2 = 0 ∧
      steps k (roundStart ms W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧
      steps (T - k) (roundStart [⟨.M, W' - 2⟩] W') = none := by
  rcases entry_small_halt_close hn hs T hT with ⟨R, ks, a₁, b₁, W₁, R₁, t, hch, hR, hcut, ht, hT'⟩ | h
  · obtain ⟨a, b, hms, -, -, -, -, -, -, -, h3⟩ := hch.start
    have hf' := hf R a b hms (by omega)
    obtain ⟨a', b', hms', hsh⟩ := hch.far_end ⟨a, b, hms, hf'.1⟩ (fun _ => ⟨a, b, hms, hf'.2⟩)
    simp only [List.cons.injEq, Mark.mk.injEq, true_and, and_true] at hms'
    obtain ⟨-, rfl⟩ := hms'
    exact Or.inl ⟨R, ks, a₁, b₁, W₁, R₁, t, hch, hR, hsh, hcut, ht, hT'⟩
  · exact Or.inr h

/-- **A halt from a loop entry that cannot close in a class of `closeClassC`, ends big and is far.**  `entry_big_halt`
with `entry_far_halt_close`. -/
theorem entry_big_halt_close {ms : List Mark} {W : Nat} (hn : EntryNoCloseC ms W) (hb : EntryBigEnd 769 ms W)
    (hf : EntryFar ms W) (T : Nat) (hT : steps T (roundStart ms W) = none) :
    (∃ R ks a₁ b₁ W₁ R₁ t, LoopChain ms W R ks [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧ 769 ≤ R₁ ∧
      15 * W₁ ≤ 64 * (W₁ - b₁) ∧ (∀ d, PassCut d R₁ a₁ b₁ W₁) ∧
      steps t (roundStart ms W) = some (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) ∧
      steps (T - t) (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) = none) ∨
    ∃ k W', 0 < k ∧ W < W' ∧ W' % 2 = 0 ∧
      steps k (roundStart ms W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧
      steps (T - k) (roundStart [⟨.M, W' - 2⟩] W') = none := by
  rcases entry_far_halt_close hn (hb.small (by decide)) hf T hT with
    ⟨R, ks, a₁, b₁, W₁, R₁, t, hch, -, hsh, hcut, ht, hT'⟩ | h
  · obtain ⟨a, b, hms, -, -, -, -, -, -, -, h3⟩ := hch.start
    obtain ⟨hb1, hb2⟩ := hb.2 R a b hms (by omega)
    exact Or.inl ⟨R, ks, a₁, b₁, W₁, R₁, t, hch, hch.big_end hb.1 hb1 hb2, hsh, hcut, ht, hT'⟩
  · exact Or.inr h

/-! ## The kernel's steps -/

/-- **The kernel's step, with the small-end check and the narrower classes.**  `clean_small_step_kernel` with
`cleanTreeGSC 2³⁷ d` above 2³⁷. -/
theorem clean_small_step_kernel_close (d W : Nat) (hW : W % 2 = 0) (h : kernelPrefixWidth ≤ W) :
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
      (((W < 2 ^ 37 → (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
          (2 ^ 37 ≤ W → (cleanTreeGSC (2 ^ 37) d).cutMem [(W : Int) / 2, 0] = true)) ∨
        (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W') ∨ ((EntryNoCloseC ms' W' ∧ EntryNoSmall ms' W') ∧ W < W')) := by
  by_cases hl : W < 2 ^ 37
  · obtain ⟨n, k, ms', W', hr, hk, hc⟩ := clean_tree_step_G kernelPrefixWidth d W (by decide) hW h
    refine ⟨n, k, ms', W', hr, hk, ?_⟩
    rcases hc with hc | hc
    · exact Or.inl ⟨fun _ => hc, fun h' => absurd h' (Nat.not_le.mpr hl)⟩
    · exact Or.inr (Or.inl hc)
  · obtain ⟨n, k, ms', W', hr, hk, hc⟩ := clean_tree_small_stepC (2 ^ 37) d W (by decide) hW (Nat.le_of_not_lt hl)
    refine ⟨n, k, ms', W', hr, hk, ?_⟩
    rcases hc with hc | hc | hc
    · exact Or.inl ⟨fun h' => absurd h' hl, fun _ => hc⟩
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr hc)

/-- **The kernel's step, with wide loop entries and the narrower classes.**  `clean_wide_step_kernel` with
`cleanTreeGWC 2³⁷ d` above 2³⁷. -/
theorem clean_wide_step_kernel_close (d W : Nat) (hW : W % 2 = 0) (h : kernelPrefixWidth ≤ W) :
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
      (((W < 2 ^ 37 → (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
          (2 ^ 37 ≤ W → (cleanTreeGWC (2 ^ 37) d).cutMem [(W : Int) / 2, 0] = true)) ∨
        (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W') ∨
        ((EntryNoCloseC ms' W' ∧ EntryNoSmall ms' W' ∧ EntryWide ms' W') ∧ W < W')) := by
  by_cases hl : W < 2 ^ 37
  · obtain ⟨n, k, ms', W', hr, hk, hc⟩ := clean_tree_step_G kernelPrefixWidth d W (by decide) hW h
    refine ⟨n, k, ms', W', hr, hk, ?_⟩
    rcases hc with hc | hc
    · exact Or.inl ⟨fun _ => hc, fun h' => absurd h' (Nat.not_le.mpr hl)⟩
    · exact Or.inr (Or.inl hc)
  · obtain ⟨n, k, ms', W', hr, hk, hc⟩ := clean_tree_wide_stepC (2 ^ 37) d W (by decide) hW (Nat.le_of_not_lt hl)
    refine ⟨n, k, ms', W', hr, hk, ?_⟩
    rcases hc with hc | hc | hc
    · exact Or.inl ⟨fun h' => absurd h' hl, fun _ => hc⟩
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr hc)

/-- **The kernel's step, with far loop entries and the narrower classes.**  `clean_far_step_kernel` with
`cleanTreeGFC 2³⁷ d` above 2³⁷. -/
theorem clean_far_step_kernel_close (d W : Nat) (hW : W % 2 = 0) (h : kernelPrefixWidth ≤ W) :
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
      (((W < 2 ^ 37 → (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
          (2 ^ 37 ≤ W → (cleanTreeGFC (2 ^ 37) d).cutMem [(W : Int) / 2, 0] = true)) ∨
        (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W') ∨
        ((EntryNoCloseC ms' W' ∧ EntryNoSmall ms' W' ∧ EntryFar ms' W') ∧ W < W')) := by
  by_cases hl : W < 2 ^ 37
  · obtain ⟨n, k, ms', W', hr, hk, hc⟩ := clean_tree_step_G kernelPrefixWidth d W (by decide) hW h
    refine ⟨n, k, ms', W', hr, hk, ?_⟩
    rcases hc with hc | hc
    · exact Or.inl ⟨fun _ => hc, fun h' => absurd h' (Nat.not_le.mpr hl)⟩
    · exact Or.inr (Or.inl hc)
  · obtain ⟨n, k, ms', W', hr, hk, hc⟩ := clean_tree_far_stepC (2 ^ 37) d W (by decide) hW (Nat.le_of_not_lt hl)
    refine ⟨n, k, ms', W', hr, hk, ?_⟩
    rcases hc with hc | hc | hc
    · exact Or.inl ⟨fun h' => absurd h' hl, fun _ => hc⟩
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr hc)

/-! ## From blank tape, with loop entries that cannot close nor end small -/

/-- **What a halt from blank tape needs, with the narrower classes: an open clean tape, then an open pass start with
R ≥ 178.**  `blank_halt_open_small` with `cleanTreeGSC` (`clean_tree_small_stepC`) for `cleanTreeGS` and
`entry_small_halt_close` at its loop entries: if the machine, started on blank tape, halts after T steps, then it
reaches a clean tape of even width W ≥ 2⁴¹ with W/2 in a cut class of `cleanTreeG directWidth d` at every depth, and
halts from there; and either W/2 is also in a cut class of `cleanTreeGSC directWidth d` at every depth, and the mark
model reaches a stuck configuration from W, or the run from W reaches a pass start wider than W with right end
R ≥ 178 and every gap at least 448 that lies in a cut leaf of `passTreeSym d` at every depth, halts from there, and
the mark model reaches a stuck configuration from there. -/
theorem blank_halt_open_small_close (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      (((∀ d, (cleanTreeGSC directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
          ∃ u, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ u ∧ u.wf ∧ (EndClose u ∨ InteriorContact u)) ∨
        ∃ R a b W₁ t, W < W₁ ∧ 178 ≤ R ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R ∧
          (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W₁ : Int) / 2, (R : Int) / 2] = true) ∧
          steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ∧
          steps (T - k - t) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) = none ∧
          ∃ u, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩], W₁⟩ u ∧ u.wf ∧
            (EndClose u ∨ InteriorContact u)) := by
  obtain ⟨k₀, hk₀⟩ := blank_prefix
  obtain ⟨W, k, hBW, hW, hG, hk, hTW, h | ⟨ms, W', t, hlt, -, ht, hq⟩⟩ :=
    blank_halt_open_of cleanGamma directWidth prefixWidth k₀ (by decide) stepsBelow_direct
      (fun d W => (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true)
      (fun d W => (cleanTreeGSC directWidth d).cutMem [(W : Int) / 2, 0] = true)
      (fun ms W => EntryNoCloseC ms W ∧ EntryNoSmall ms W)
      (fun d W hW h => clean_tree_step_G directWidth d W (by decide) hW h)
      (fun d W hW h => clean_tree_small_stepC directWidth d W (by decide) hW h) SmallQ
      (fun _ _ T' he hT' => entry_small_halt_close he.1 he.2 T' hT') (by decide) (by decide) hk₀ T hT
  · exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inl h⟩
  · obtain ⟨R, a, b, W₁, t₁, h1, -, h⟩ := SmallQ.pass hlt ht hq
    exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inr ⟨R, a, b, W₁, t₁, h1, h⟩⟩

/-- **The same, checked by the kernel alone.**  `blank_halt_open_small_kernel` with `clean_small_step_kernel_close`
(the plain tree below 2³⁷, `cleanTreeGSC 2³⁷` above) and `entry_small_halt_close`.  Nothing here is evaluated by
compiled code. -/
theorem blank_halt_open_small_kernel_close (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, kernelPrefixWidth ≤ W ∧ W % 2 = 0 ∧
      (∀ d, (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      (((2 ^ 37 ≤ W → ∀ d, (cleanTreeGSC (2 ^ 37) d).cutMem [(W : Int) / 2, 0] = true) ∧
          ∃ u, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ u ∧ u.wf ∧ (EndClose u ∨ InteriorContact u)) ∨
        ∃ R a b W₁ t, W < W₁ ∧ 2 ^ 37 ≤ W₁ ∧ 178 ≤ R ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R ∧
          (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W₁ : Int) / 2, (R : Int) / 2] = true) ∧
          steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ∧
          steps (T - k - t) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) = none ∧
          ∃ u, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩], W₁⟩ u ∧ u.wf ∧
            (EndClose u ∨ InteriorContact u)) := by
  obtain ⟨k₀, hk₀⟩ := blank_prefix_kernel
  obtain ⟨W, k, hBW, hW, hG, hk, hTW, ⟨hcut, h⟩ | ⟨ms, W', t, hlt, he, ht, hq⟩⟩ :=
    blank_halt_open_of kernelPrefixWidth kernelPrefixWidth kernelPrefixWidth k₀ (by decide) (stepsBelow_self _)
      (fun d W => (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) _
      (fun ms W => EntryNoCloseC ms W ∧ EntryNoSmall ms W)
      (fun d W hW h => clean_tree_step_G kernelPrefixWidth d W (by decide) hW h) clean_small_step_kernel_close SmallQ
      (fun _ _ T' he hT' => entry_small_halt_close he.1 he.2 T' hT') (by decide) (Nat.le_refl _) hk₀ T hT
  · exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inl ⟨fun hl d => (hcut d).2 hl, h⟩⟩
  · obtain ⟨R, a, b, W₁, t₁, h1, hle, h⟩ := SmallQ.pass hlt ht hq
    exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inr ⟨R, a, b, W₁, t₁, h1, Nat.le_trans he.2.1 hle, h⟩⟩

/-- **The open question, reduced, with the narrower classes.**  `never_halts_of_open` with `cleanTreeGSC` for
`cleanTreeGS`: the clean tapes left to rule out are those that both `cleanTreeG 2⁴¹ d` and `cleanTreeGSC 2⁴¹ d` leave
open at every depth, and the pass starts are those of `never_halts_of_open`. -/
theorem never_halts_of_open_close
    (hC : ∀ W, directWidth ≤ W → W % 2 = 0 → (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) →
      (∀ d, (cleanTreeGSC directWidth d).cutMem [(W : Int) / 2, 0] = true) →
      ∀ T, steps T (roundStart [⟨.M, W - 2⟩] W) ≠ none)
    (hP : ∀ W R a b W₁ t, directWidth ≤ W → W % 2 = 0 →
      (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) → W < W₁ → 178 ≤ R →
      PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R →
      (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W₁ : Int) / 2, (R : Int) / 2] = true) →
      steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) →
      ∀ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ≠ none) :
    ∀ T, steps T ⟨blank, blank, .A⟩ ≠ none := by
  intro T hT
  obtain ⟨W, k, hBW, hW, hG, -, hTW, ⟨hS, -⟩ | ⟨R, a, b, W₁, t, hlt, hR, hP₁, hcut, ht, hT₁, -⟩⟩ :=
    blank_halt_open_small_close T hT
  · exact hC W hBW hW hG hS _ hTW
  · exact hP W R a b W₁ t hBW hW hG hlt hR hP₁ hcut ht _ hT₁

/-! ## From blank tape, with wide loop entries -/

/-- **What a halt from blank tape needs, with the narrower classes: an open clean tape, then a wide open pass
start.**  `blank_halt_open_wide` with `cleanTreeGWC` (`clean_tree_wide_stepC`) for `cleanTreeGW` and
`entry_wide_halt_close` at its loop entries. -/
theorem blank_halt_open_wide_close (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      (((∀ d, (cleanTreeGWC directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
          ∃ u, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ u ∧ u.wf ∧ (EndClose u ∨ InteriorContact u)) ∨
        ∃ R a b W₁ t, W < W₁ ∧ 178 ≤ R ∧ (W₁ ≤ 64 * R + 6 ∨ 15 * W₁ ≤ 64 * (W₁ - b)) ∧
          PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R ∧
          (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W₁ : Int) / 2, (R : Int) / 2] = true) ∧
          steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ∧
          steps (T - k - t) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) = none ∧
          ∃ u, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩], W₁⟩ u ∧ u.wf ∧
            (EndClose u ∨ InteriorContact u)) := by
  obtain ⟨k₀, hk₀⟩ := blank_prefix
  obtain ⟨W, k, hBW, hW, hG, hk, hTW, h | ⟨ms, W', t, hlt, -, ht, hq⟩⟩ :=
    blank_halt_open_of cleanGamma directWidth prefixWidth k₀ (by decide) stepsBelow_direct
      (fun d W => (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true)
      (fun d W => (cleanTreeGWC directWidth d).cutMem [(W : Int) / 2, 0] = true)
      (fun ms W => EntryNoCloseC ms W ∧ EntryNoSmall ms W ∧ EntryWide ms W)
      (fun d W hW h => clean_tree_step_G directWidth d W (by decide) hW h)
      (fun d W hW h => clean_tree_wide_stepC directWidth d W (by decide) hW h) WideQ
      (fun _ _ T' he hT' => entry_wide_halt_close he.1 he.2.1 he.2.2 T' hT') (by decide) (by decide) hk₀ T hT
  · exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inl h⟩
  · obtain ⟨R, a, b, W₁, t₁, h1, -, h⟩ := WideQ.pass hlt ht hq
    exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inr ⟨R, a, b, W₁, t₁, h1, h⟩⟩

/-- **The same, checked by the kernel alone.**  `blank_halt_open_wide_kernel` with `clean_wide_step_kernel_close` and
`entry_wide_halt_close`. -/
theorem blank_halt_open_wide_kernel_close (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, kernelPrefixWidth ≤ W ∧ W % 2 = 0 ∧
      (∀ d, (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      (((2 ^ 37 ≤ W → ∀ d, (cleanTreeGWC (2 ^ 37) d).cutMem [(W : Int) / 2, 0] = true) ∧
          ∃ u, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ u ∧ u.wf ∧ (EndClose u ∨ InteriorContact u)) ∨
        ∃ R a b W₁ t, W < W₁ ∧ 2 ^ 37 ≤ W₁ ∧ 178 ≤ R ∧ (W₁ ≤ 64 * R + 6 ∨ 15 * W₁ ≤ 64 * (W₁ - b)) ∧
          PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R ∧
          (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W₁ : Int) / 2, (R : Int) / 2] = true) ∧
          steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ∧
          steps (T - k - t) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) = none ∧
          ∃ u, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩], W₁⟩ u ∧ u.wf ∧
            (EndClose u ∨ InteriorContact u)) := by
  obtain ⟨k₀, hk₀⟩ := blank_prefix_kernel
  obtain ⟨W, k, hBW, hW, hG, hk, hTW, ⟨hcut, h⟩ | ⟨ms, W', t, hlt, he, ht, hq⟩⟩ :=
    blank_halt_open_of kernelPrefixWidth kernelPrefixWidth kernelPrefixWidth k₀ (by decide) (stepsBelow_self _)
      (fun d W => (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) _
      (fun ms W => EntryNoCloseC ms W ∧ EntryNoSmall ms W ∧ EntryWide ms W)
      (fun d W hW h => clean_tree_step_G kernelPrefixWidth d W (by decide) hW h) clean_wide_step_kernel_close WideQ
      (fun _ _ T' he hT' => entry_wide_halt_close he.1 he.2.1 he.2.2 T' hT') (by decide) (Nat.le_refl _) hk₀ T hT
  · exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inl ⟨fun hl d => (hcut d).2 hl, h⟩⟩
  · obtain ⟨R, a, b, W₁, t₁, h1, hle, h⟩ := WideQ.pass hlt ht hq
    exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inr ⟨R, a, b, W₁, t₁, h1, Nat.le_trans he.2.1.1 hle, h⟩⟩

/-- **The open question, with the shape and the narrower classes.**  `never_halts_of_wide` with `cleanTreeGWC` for
`cleanTreeGW`. -/
theorem never_halts_of_wide_close
    (hC : ∀ W, directWidth ≤ W → W % 2 = 0 → (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) →
      (∀ d, (cleanTreeGWC directWidth d).cutMem [(W : Int) / 2, 0] = true) →
      ∀ T, steps T (roundStart [⟨.M, W - 2⟩] W) ≠ none)
    (hP : ∀ W R a b W₁ t, directWidth ≤ W → W % 2 = 0 →
      (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) → W < W₁ → 178 ≤ R →
      (W₁ ≤ 64 * R + 6 ∨ 15 * W₁ ≤ 64 * (W₁ - b)) →
      PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R →
      (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W₁ : Int) / 2, (R : Int) / 2] = true) →
      steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) →
      ∀ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ≠ none) :
    ∀ T, steps T ⟨blank, blank, .A⟩ ≠ none := by
  intro T hT
  obtain ⟨W, k, hBW, hW, hG, -, hTW, ⟨hS, -⟩ | ⟨R, a, b, W₁, t, hlt, hR, hsh, hP₁, hcut, ht, hT₁, -⟩⟩ :=
    blank_halt_open_wide_close T hT
  · exact hC W hBW hW hG hS _ hTW
  · exact hP W R a b W₁ t hBW hW hG hlt hR hsh hP₁ hcut ht _ hT₁

/-- **The run from blank tape halts through none of the 29 families, with the narrower classes.**
`blank_halt_not_family` with `blank_halt_open_wide_close`. -/
theorem blank_halt_not_family_close (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ((∀ d, (cleanTreeGWC directWidth d).cutMem [(W : Int) / 2, 0] = true) ∨
        ∃ R a b W₁ t, W < W₁ ∧ 178 ≤ R ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R ∧
          (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W₁ : Int) / 2, (R : Int) / 2] = true) ∧
          steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ∧
          steps (T - k - t) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) = none ∧
          ∀ F ∈ openHaltFams ++ reentryFams, ∀ s, ¬ (R = F.R0 ∧ b = F.b0 + 2 ^ F.k * s ∧ W₁ = F.W0 + 2 ^ F.k * s)) := by
  obtain ⟨W, k, hBW, hW, hG, hk, hTW, ⟨hS, -⟩ | ⟨R, a, b, W₁, t, hlt, hR, hsh, hP₁, hcut, ht, hT₁, -⟩⟩ :=
    blank_halt_open_wide_close T hT
  · exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inl hS⟩
  · refine ⟨W, k, hBW, hW, hG, hk, hTW, Or.inr ⟨R, a, b, W₁, t, hlt, hR, hP₁, hcut, ht, hT₁, ?_⟩⟩
    rintro F hF s ⟨rfl, rfl, rfl⟩
    have h41 : directWidth = 2199023255552 := rfl
    rcases List.mem_append.1 hF with hF | hF
    · have h58 := openHaltFams_wide hF s hsh
      generalize 2 ^ F.k * s = X at h58 hlt
      omega
    · have h35 := reentryFams_wide hF s hsh
      have e35 : (2 : Nat) ^ 35 = 34359738368 := rfl
      rw [e35] at h35
      generalize 2 ^ F.k * s = X at h35 hlt
      omega

/-! ## From blank tape, with far loop entries -/

/-- **What a halt from blank tape needs, with the narrower classes: an open clean tape, then an open pass start with
its middle wall far from the end.**  `blank_halt_open_far` with `cleanTreeGFC` (`clean_tree_far_stepC`) for
`cleanTreeGF` and `entry_far_halt_close` at its loop entries. -/
theorem blank_halt_open_far_close (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      (((∀ d, (cleanTreeGFC directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
          ∃ u, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ u ∧ u.wf ∧ (EndClose u ∨ InteriorContact u)) ∨
        ∃ R a b W₁ t, W < W₁ ∧ 178 ≤ R ∧ 15 * W₁ ≤ 64 * (W₁ - b) ∧
          PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R ∧
          (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W₁ : Int) / 2, (R : Int) / 2] = true) ∧
          steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ∧
          steps (T - k - t) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) = none ∧
          ∃ u, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩], W₁⟩ u ∧ u.wf ∧
            (EndClose u ∨ InteriorContact u)) := by
  obtain ⟨k₀, hk₀⟩ := blank_prefix
  obtain ⟨W, k, hBW, hW, hG, hk, hTW, h | ⟨ms, W', t, hlt, -, ht, hq⟩⟩ :=
    blank_halt_open_of cleanGamma directWidth prefixWidth k₀ (by decide) stepsBelow_direct
      (fun d W => (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true)
      (fun d W => (cleanTreeGFC directWidth d).cutMem [(W : Int) / 2, 0] = true)
      (fun ms W => EntryNoCloseC ms W ∧ EntryNoSmall ms W ∧ EntryFar ms W)
      (fun d W hW h => clean_tree_step_G directWidth d W (by decide) hW h)
      (fun d W hW h => clean_tree_far_stepC directWidth d W (by decide) hW h) FarQ
      (fun _ _ T' he hT' => entry_far_halt_close he.1 he.2.1 he.2.2 T' hT') (by decide) (by decide) hk₀ T hT
  · exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inl h⟩
  · obtain ⟨R, a, b, W₁, t₁, h1, -, h⟩ := FarQ.pass hlt ht hq
    exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inr ⟨R, a, b, W₁, t₁, h1, h⟩⟩

/-- **The same, checked by the kernel alone.**  `blank_halt_open_far_kernel` with `clean_far_step_kernel_close` and
`entry_far_halt_close`. -/
theorem blank_halt_open_far_kernel_close (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, kernelPrefixWidth ≤ W ∧ W % 2 = 0 ∧
      (∀ d, (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      (((2 ^ 37 ≤ W → ∀ d, (cleanTreeGFC (2 ^ 37) d).cutMem [(W : Int) / 2, 0] = true) ∧
          ∃ u, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ u ∧ u.wf ∧ (EndClose u ∨ InteriorContact u)) ∨
        ∃ R a b W₁ t, W < W₁ ∧ 2 ^ 37 ≤ W₁ ∧ 178 ≤ R ∧ 15 * W₁ ≤ 64 * (W₁ - b) ∧
          PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R ∧
          (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W₁ : Int) / 2, (R : Int) / 2] = true) ∧
          steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ∧
          steps (T - k - t) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) = none ∧
          ∃ u, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩], W₁⟩ u ∧ u.wf ∧
            (EndClose u ∨ InteriorContact u)) := by
  obtain ⟨k₀, hk₀⟩ := blank_prefix_kernel
  obtain ⟨W, k, hBW, hW, hG, hk, hTW, ⟨hcut, h⟩ | ⟨ms, W', t, hlt, he, ht, hq⟩⟩ :=
    blank_halt_open_of kernelPrefixWidth kernelPrefixWidth kernelPrefixWidth k₀ (by decide) (stepsBelow_self _)
      (fun d W => (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) _
      (fun ms W => EntryNoCloseC ms W ∧ EntryNoSmall ms W ∧ EntryFar ms W)
      (fun d W hW h => clean_tree_step_G kernelPrefixWidth d W (by decide) hW h) clean_far_step_kernel_close FarQ
      (fun _ _ T' he hT' => entry_far_halt_close he.1 he.2.1 he.2.2 T' hT') (by decide) (Nat.le_refl _) hk₀ T hT
  · exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inl ⟨fun hl d => (hcut d).2 hl, h⟩⟩
  · obtain ⟨R, a, b, W₁, t₁, h1, hle, h⟩ := FarQ.pass hlt ht hq
    exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inr ⟨R, a, b, W₁, t₁, h1, Nat.le_trans he.2.1.1 hle, h⟩⟩

/-- **The open question, with the far shape and the narrower classes.**  `never_halts_of_far` with `cleanTreeGFC` for
`cleanTreeGF`. -/
theorem never_halts_of_far_close
    (hC : ∀ W, directWidth ≤ W → W % 2 = 0 → (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) →
      (∀ d, (cleanTreeGFC directWidth d).cutMem [(W : Int) / 2, 0] = true) →
      ∀ T, steps T (roundStart [⟨.M, W - 2⟩] W) ≠ none)
    (hP : ∀ W R a b W₁ t, directWidth ≤ W → W % 2 = 0 →
      (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) → W < W₁ → 178 ≤ R →
      15 * W₁ ≤ 64 * (W₁ - b) → PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R →
      (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W₁ : Int) / 2, (R : Int) / 2] = true) →
      steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) →
      ∀ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ≠ none) :
    ∀ T, steps T ⟨blank, blank, .A⟩ ≠ none := by
  intro T hT
  obtain ⟨W, k, hBW, hW, hG, -, hTW, ⟨hS, -⟩ | ⟨R, a, b, W₁, t, hlt, hR, hsh, hP₁, hcut, ht, hT₁, -⟩⟩ :=
    blank_halt_open_far_close T hT
  · exact hC W hBW hW hG hS _ hTW
  · exact hP W R a b W₁ t hBW hW hG hlt hR hsh hP₁ hcut ht _ hT₁

/-! ## From blank tape, with loop entries that end big and are far -/

/-- **What a halt from blank tape needs, with the narrower classes: an open clean tape, then an open pass start with a
right end of at least 769 and its middle wall far from the end.**  `blank_halt_open_big` with `cleanTreeGBC`
(`clean_tree_big_stepC`) for `cleanTreeGB` and `entry_big_halt_close` at its loop entries. -/
theorem blank_halt_open_big_close (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      (((∀ d, (cleanTreeGBC directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
          ∃ u, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ u ∧ u.wf ∧ (EndClose u ∨ InteriorContact u)) ∨
        ∃ R a b W₁ t, W < W₁ ∧ 769 ≤ R ∧ 15 * W₁ ≤ 64 * (W₁ - b) ∧
          PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R ∧
          (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W₁ : Int) / 2, (R : Int) / 2] = true) ∧
          steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ∧
          steps (T - k - t) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) = none ∧
          ∃ u, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩], W₁⟩ u ∧ u.wf ∧
            (EndClose u ∨ InteriorContact u)) := by
  obtain ⟨k₀, hk₀⟩ := blank_prefix
  obtain ⟨W, k, hBW, hW, hG, hk, hTW, h | ⟨ms, W', t, hlt, -, ht, hq⟩⟩ :=
    blank_halt_open_of cleanGamma directWidth prefixWidth k₀ (by decide) stepsBelow_direct
      (fun d W => (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true)
      (fun d W => (cleanTreeGBC directWidth d).cutMem [(W : Int) / 2, 0] = true)
      (fun ms W => EntryNoCloseC ms W ∧ EntryBigEnd 769 ms W ∧ EntryFar ms W)
      (fun d W hW h => clean_tree_step_G directWidth d W (by decide) hW h)
      (fun d W hW h => clean_tree_big_stepC directWidth d W (by decide) hW h) BigQ
      (fun _ _ T' he hT' => entry_big_halt_close he.1 he.2.1 he.2.2 T' hT') (by decide) (by decide) hk₀ T hT
  · exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inl h⟩
  · obtain ⟨R, a, b, W₁, t₁, h1, -, h⟩ := BigQ.pass hlt ht hq
    exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inr ⟨R, a, b, W₁, t₁, h1, h⟩⟩

/-- **The open question, with a right end of at least 769 and the narrower classes.**  `never_halts_of_big` with
`cleanTreeGBC` for `cleanTreeGB`: the clean tapes left to rule out are those that both `cleanTreeG 2⁴¹ d` and
`cleanTreeGBC 2⁴¹ d` leave open at every depth, and the pass starts those with R ≥ 769 and 15W₁ ≤ 64(W₁ − b) that
`passTreeSym d` leaves open at every depth, as in `never_halts_of_big`. -/
theorem never_halts_of_big_close
    (hC : ∀ W, directWidth ≤ W → W % 2 = 0 → (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) →
      (∀ d, (cleanTreeGBC directWidth d).cutMem [(W : Int) / 2, 0] = true) →
      ∀ T, steps T (roundStart [⟨.M, W - 2⟩] W) ≠ none)
    (hP : ∀ W R a b W₁ t, directWidth ≤ W → W % 2 = 0 →
      (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) → W < W₁ → 769 ≤ R →
      15 * W₁ ≤ 64 * (W₁ - b) → PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R →
      (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W₁ : Int) / 2, (R : Int) / 2] = true) →
      steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) →
      ∀ T, steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ≠ none) :
    ∀ T, steps T ⟨blank, blank, .A⟩ ≠ none := by
  intro T hT
  obtain ⟨W, k, hBW, hW, hG, -, hTW, ⟨hS, -⟩ | ⟨R, a, b, W₁, t, hlt, hR, hsh, hP₁, hcut, ht, hT₁, -⟩⟩ :=
    blank_halt_open_big_close T hT
  · exact hC W hBW hW hG hS _ hTW
  · exact hP W R a b W₁ t hBW hW hG hlt hR hsh hP₁ hcut ht _ hT₁

#print axioms entry_small_halt_close
#print axioms entry_wide_halt_close
#print axioms entry_far_halt_close
#print axioms entry_big_halt_close
#print axioms blank_halt_open_small_close
#print axioms blank_halt_open_small_kernel_close
#print axioms never_halts_of_open_close
#print axioms blank_halt_open_wide_close
#print axioms blank_halt_open_wide_kernel_close
#print axioms never_halts_of_wide_close
#print axioms blank_halt_not_family_close
#print axioms blank_halt_open_far_close
#print axioms blank_halt_open_far_kernel_close
#print axioms never_halts_of_far_close
#print axioms blank_halt_open_big_close
#print axioms never_halts_of_big_close
