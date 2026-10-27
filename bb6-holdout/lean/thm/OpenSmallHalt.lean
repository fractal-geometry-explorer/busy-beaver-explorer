import SmallEndHalt
open BB6 BB6.Sym

/-! # An open clean tape first, then an open pass start with R ≥ 178

`blank_halt_open` (`thm/PassEntryHalt.lean`) follows a halting run from blank tape with the plain clean-tape tree
where that tree resolves a clean tape, and with the tree with loop entries where it does not, so the pass starts that
a halt may need come only after a clean tape that the plain tree leaves open at every depth.  `blank_halt_small`
(`thm/SmallEndHalt.lean`) uses a tree whose loop entries also pass the small-end check (`cleanTreeGS`), past which the
loop's chain ends at a right end of at least 178, so that the pass start a halt may need lies in the tree for every
R ≥ 178 (`passTreeSym`), where no round is decided as a halt at the depths measured.  `blank_halt_open_of` with that
tree and `entry_small_halt` puts the two together:

* `blank_halt_open_small`: a halt from blank tape needs a clean tape of width ≥ 2⁴¹ that `cleanTreeG 2⁴¹ d` leaves
  open at every depth, from which the machine halts; and either `cleanTreeGS 2⁴¹ d` leaves it open too, and the mark
  model reaches a stuck configuration from it, or the run from it passes a loop entry and reaches a pass start with
  R ≥ 178 that `passTreeSym d` leaves open at every depth, from which the machine halts, and the mark model reaches a
  stuck configuration from there.
* `blank_halt_open_small_kernel`: the same from 2²⁰, with nothing evaluated by compiled code (the tree with checked
  loop entries over the widths ≥ 2³⁷).
* `never_halts_of_open`: so the machine never halts from blank tape if it halts neither from a clean tape that both
  trees leave open at every depth nor from a pass start with R ≥ 178 left open at every depth that the run reaches from
  a clean tape that the plain tree leaves open at every depth. -/

/-- What a halt from a loop entry that cannot close nor end small needs (`entry_small_halt`), as `blank_halt_open_of`
takes it. -/
def SmallQ (ms : List Mark) (W T : Nat) : Prop :=
  ∃ R ks a₁ b₁ W₁ R₁ t, LoopChain ms W R ks [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧ 178 ≤ R₁ ∧
    (∀ d, PassCut d R₁ a₁ b₁ W₁) ∧
    steps t (roundStart ms W) = some (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) ∧
    steps (T - t) (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) = none

/-- From a loop entry with `SmallQ`, reached t steps after a clean tape of width W < W′ with T − k steps left: the pass
start it names is wider than W and at least as wide as the entry, it has R ≥ 178 and every gap at least 448, it lies
in a cut leaf of `passTreeSym d` at every depth, the run reaches it from the clean tape, the machine halts from it,
and the mark model reaches a stuck configuration from it. -/
theorem SmallQ.pass {ms : List Mark} {W W' T k t : Nat} (hlt : W < W')
    (ht : steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms W')) (hq : SmallQ ms W' (T - k - t)) :
    ∃ R a b W₁ t₁, W < W₁ ∧ W' ≤ W₁ ∧ 178 ≤ R ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R ∧
      (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W₁ : Int) / 2, (R : Int) / 2] = true) ∧
      steps t₁ (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ∧
      steps (T - k - t₁) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) = none ∧
      ∃ u, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩], W₁⟩ u ∧ u.wf ∧
        (EndClose u ∨ InteriorContact u) := by
  obtain ⟨R, ks, a₁, b₁, W₁, R₁, t', hch, hR, hcut, ht', hT₁⟩ := hq
  obtain ⟨hle, hP₁, u, hu, huw, hus⟩ := hch.last_halt hT₁
  refine ⟨R₁, a₁, b₁, W₁, t + t', by omega, hle, hR, hP₁, fun d => passCut_sym hR (hcut d), steps_seq ht ht', ?_,
    u, hu, huw, hus⟩
  rw [show T - k - (t + t') = T - k - t - t' by omega]
  exact hT₁

/-- **What a halt from blank tape needs: an open clean tape, then an open pass start with R ≥ 178.**
`blank_halt_open_of` with the prefix to 2³² (`blank_prefix`), the clean tapes of width in [2³², 2⁴¹) run one by one
(`stepsBelow_direct`), the clean-tape tree over the widths ≥ 2⁴¹ (`clean_tree_step_G`), the same tree with loop entries
that cannot close nor end small (`clean_tree_small_step`), and `entry_small_halt` at those entries: if the machine,
started on blank tape, halts after T steps, then it reaches a clean tape of even width W ≥ 2⁴¹ with W/2 in a cut class
of `cleanTreeG directWidth d` at every depth, and halts from there; and either W/2 is also in a cut class of
`cleanTreeGS directWidth d` at every depth, and the mark model reaches a stuck configuration from W, or the run from W
reaches a pass start wider than W with right end R ≥ 178 and every gap at least 448 that lies in a cut leaf of
`passTreeSym d` at every depth, halts from there, and the mark model reaches a stuck configuration from there. -/
theorem blank_halt_open_small (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      (((∀ d, (cleanTreeGS directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
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
      (fun d W => (cleanTreeGS directWidth d).cutMem [(W : Int) / 2, 0] = true)
      (fun ms W => EntryNoClose ms W ∧ EntryNoSmall ms W)
      (fun d W hW h => clean_tree_step_G directWidth d W (by decide) hW h)
      (fun d W hW h => clean_tree_small_step directWidth d W (by decide) hW h) SmallQ
      (fun _ _ T' he hT' => entry_small_halt he.1 he.2 T' hT') (by decide) (by decide) hk₀ T hT
  · exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inl h⟩
  · obtain ⟨R, a, b, W₁, t₁, h1, -, h⟩ := SmallQ.pass hlt ht hq
    exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inr ⟨R, a, b, W₁, t₁, h1, h⟩⟩

/-- **The same, checked by the kernel alone.**  `blank_halt_open_of` from the kernel's prefix to 2²⁰
(`blank_prefix_kernel`), with the clean-tape tree over the widths ≥ 2²⁰ and `clean_small_step_kernel` (the plain tree
below 2³⁷, the tree with checked loop entries `cleanTreeGS 2³⁷` above): if the machine, started on blank tape, halts
after T steps, then it reaches a clean tape of even width W ≥ 2²⁰ with W/2 in a cut class of `cleanTreeG 2²⁰ d` at
every depth, and halts from there; and either, if W ≥ 2³⁷, W/2 is also in a cut class of `cleanTreeGS 2³⁷ d` at every
depth, and the mark model reaches a stuck configuration from W, or the run from W reaches a pass start wider than W
and 2³⁷ with right end R ≥ 178 and every gap at least 448 that lies in a cut leaf of `passTreeSym d` at every depth,
halts from there, and the mark model reaches a stuck configuration from there.  Nothing here is evaluated by compiled
code. -/
theorem blank_halt_open_small_kernel (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, kernelPrefixWidth ≤ W ∧ W % 2 = 0 ∧
      (∀ d, (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      (((2 ^ 37 ≤ W → ∀ d, (cleanTreeGS (2 ^ 37) d).cutMem [(W : Int) / 2, 0] = true) ∧
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
      (fun ms W => EntryNoClose ms W ∧ EntryNoSmall ms W)
      (fun d W hW h => clean_tree_step_G kernelPrefixWidth d W (by decide) hW h) clean_small_step_kernel SmallQ
      (fun _ _ T' he hT' => entry_small_halt he.1 he.2 T' hT') (by decide) (Nat.le_refl _) hk₀ T hT
  · exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inl ⟨fun hl d => (hcut d).2 hl, h⟩⟩
  · obtain ⟨R, a, b, W₁, t₁, h1, hle, h⟩ := SmallQ.pass hlt ht hq
    exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inr ⟨R, a, b, W₁, t₁, h1, Nat.le_trans he.2.1 hle, h⟩⟩

/-- **The open question, reduced.**  If the machine halts from no clean tape of even width W ≥ 2⁴¹ that both
`cleanTreeG 2⁴¹ d` and `cleanTreeGS 2⁴¹ d` leave open at every depth, and from no pass start with right end R ≥ 178
and every gap at least 448 that `passTreeSym d` leaves open at every depth and that the run reaches from a clean tape
of even width W ≥ 2⁴¹ narrower than it that `cleanTreeG 2⁴¹ d` leaves open at every depth, then it does not halt from
blank tape. -/
theorem never_halts_of_open
    (hC : ∀ W, directWidth ≤ W → W % 2 = 0 → (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) →
      (∀ d, (cleanTreeGS directWidth d).cutMem [(W : Int) / 2, 0] = true) →
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
    blank_halt_open_small T hT
  · exact hC W hBW hW hG hS _ hTW
  · exact hP W R a b W₁ t hBW hW hG hlt hR hP₁ hcut ht _ hT₁

#print axioms blank_halt_open_small
#print axioms blank_halt_open_small_kernel
#print axioms never_halts_of_open
