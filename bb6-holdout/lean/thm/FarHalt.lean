import WideHalt
import CleanFarTheorem
open BB6 BB6.Sym

/-! # The pass start a halt needs has its middle wall far from the end

`blank_halt_open_wide` (`thm/WideHalt.lean`) gives the pass start a halt from blank tape needs the shape
W ≤ 64R + 6 or 15W ≤ 64(W − b).  The first case comes only from the half pass and the round-7 break, and both land with
the second too:

* A full pass lands with 64(W′ − b′) ≥ 15E + 144R′ + 735 (`step_wide`).
* A round-7 break lands with 32b′ = 3b + 16E − 6R + 446, so 64(W′ − b′) − 15W′ = 17E − 6b + 12R + 284 > 0: its middle
  wall is near the middle of the tape, b′ ≈ E/2 + 3b/32.
* A half pass, only ever the first step, lands with 2(W′ − b′) = W − b + R + 2, so with the second case when the loop
  entry has 15W + 26 ≤ 32(W − b + R).

The entry test `cleanFarOK` (`BB6/WideEntry.lean`) asks `EntryFar`: 15W ≤ 64(W − b) at the entry, for a chain with no
step, and 15W + 26 ≤ 32(W − b + R), for a half pass.  At 36 digits over the widths ≥ 2⁴¹ every one of the 28,660 loop
entries passes it (W − b > 0.4558W and R > W/29.02 there; `thm/CleanFarMass.lean` counts the same entries and cut
classes as for `cleanTreeGS`).  So the chain's last pass start has 15W ≤ 64(W − b) (`FarShape`, `LoopChain.far_end`),
and on a lane W − b + 2R + 22 = 2^m of the main halting route 15W + 128R + 1,408 ≤ 2^(m+6) (`farShape_pow2`).

`blank_halt_open_far` is `blank_halt_open_wide` with that shape, and `never_halts_of_far` the open question with it.
Nothing here is evaluated: the tree is built by the proved explorer. -/

/-! ## The shape of the chain's last pass start -/

/-- The pass start with walls a, b and W − R − 1 has its middle wall at least 15/64 of the width from the end. -/
def FarShape (ms : List Mark) (W R : Nat) : Prop :=
  ∃ a b, ms = [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] ∧ 15 * W ≤ 64 * (W - b)

/-- **Each step of the loop's chain lands far.**  From a pass start of width E with every gap at least 448, a full
pass and a round-7 break land with 15W′ ≤ 64(W′ − b′); a half pass does when 15E + 26 ≤ 32(E − b + R). -/
theorem step_far {k : StepKind} {n : Nat} {ms ms₁ : List Mark} {E R W₁ R₁ : Nat}
    (hP : PassStart448 ms E R) (hP₁ : PassStart448 ms₁ W₁ R₁)
    (hm : StepMap k n E R (passL1 ms E) W₁ R₁ (passL1 ms₁ W₁))
    (hh : E % 4 = 2 → ∃ a b, ms = [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] ∧ 15 * E + 26 ≤ 32 * (E - b + R)) :
    FarShape ms₁ W₁ R₁ := by
  obtain ⟨a, b, rfl, -, -, -, -, -, h1, h2, h3⟩ := hP
  obtain ⟨a₁, b₁, rfl, -, -, -, -, -, g1, g2, g3⟩ := hP₁
  refine ⟨a₁, b₁, rfl, ?_⟩
  rw [passL1_www a b E R (by omega), passL1_www a₁ b₁ W₁ R₁ (by omega)] at hm
  cases k with
  | full =>
    obtain ⟨-, e1, e2, e3⟩ := hm
    omega
  | half =>
    obtain ⟨-, e1, e2, e3, e4⟩ := hm
    obtain ⟨a', b', hms, hb⟩ := hh e4
    simp only [List.cons.injEq, Mark.mk.injEq, true_and, and_true] at hms
    obtain ⟨-, rfl⟩ := hms
    omega
  | break7 =>
    obtain ⟨-, e1, e2, e3⟩ := hm
    omega

/-- **The loop's chain ends far.**  From a pass start with the shape, and with 15W + 26 ≤ 32(W − b + R) if its width
is ≡ 2 (mod 4) (where a half pass can start the chain), every pass start of the chain has the shape (`step_far`; a
half pass is only ever the first step, since every landing has width ≡ 0 mod 4). -/
theorem LoopChain.far_end {ms : List Mark} {W R : Nat} {ks : List StepKind} {ms' : List Mark} {W' R' : Nat}
    (h : LoopChain ms W R ks ms' W' R') : FarShape ms W R →
    (W % 4 = 2 → ∃ a b, ms = [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] ∧ 15 * W + 26 ≤ 32 * (W - b + R)) →
    FarShape ms' W' R' := by
  induction h with
  | nil _ => intro hs _; exact hs
  | cons k n kk hP _ _ _ hW4 hmap tl ih =>
    intro _ hh
    exact ih (step_far hP tl.start hmap hh) (fun h4 => absurd h4 (by omega))

/-- **On a lane W − b + 2R + 22 = 2^m of the main halting route**, the shape needs 15W + 128R + 1,408 ≤ 2^(m+6). -/
theorem farShape_pow2 {b W R m : Nat} (h : 15 * W ≤ 64 * (W - b)) (hm : W - b + 2 * R + 22 = 2 ^ m) :
    15 * W + 128 * R + 1408 ≤ 2 ^ (m + 6) := by
  rw [Nat.pow_add]
  omega

/-! ## From a far loop entry -/

/-- **A halt from a far loop entry that cannot close nor end small.**  As `entry_small_halt`, and the chain's last pass
start has its middle wall far from the end: 15W₁ ≤ 64(W₁ − b₁). -/
theorem entry_far_halt {ms : List Mark} {W : Nat} (hn : EntryNoClose ms W) (hs : EntryNoSmall ms W)
    (hf : EntryFar ms W) (T : Nat) (hT : steps T (roundStart ms W) = none) :
    (∃ R ks a₁ b₁ W₁ R₁ t, LoopChain ms W R ks [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧ 178 ≤ R₁ ∧
      15 * W₁ ≤ 64 * (W₁ - b₁) ∧ (∀ d, PassCut d R₁ a₁ b₁ W₁) ∧
      steps t (roundStart ms W) = some (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) ∧
      steps (T - t) (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) = none) ∨
    ∃ k W', 0 < k ∧ W < W' ∧ W' % 2 = 0 ∧
      steps k (roundStart ms W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧
      steps (T - k) (roundStart [⟨.M, W' - 2⟩] W') = none := by
  rcases entry_small_halt hn hs T hT with ⟨R, ks, a₁, b₁, W₁, R₁, t, hch, hR, hcut, ht, hT'⟩ | h
  · obtain ⟨a, b, hms, -, -, -, -, -, -, -, h3⟩ := hch.start
    have hf' := hf R a b hms (by omega)
    obtain ⟨a', b', hms', hsh⟩ := hch.far_end ⟨a, b, hms, hf'.1⟩ (fun _ => ⟨a, b, hms, hf'.2⟩)
    simp only [List.cons.injEq, Mark.mk.injEq, true_and, and_true] at hms'
    obtain ⟨-, rfl⟩ := hms'
    exact Or.inl ⟨R, ks, a₁, b₁, W₁, R₁, t, hch, hR, hsh, hcut, ht, hT'⟩
  · exact Or.inr h

/-- What a halt from a far loop entry that cannot close nor end small needs (`entry_far_halt`), as
`blank_halt_open_of` takes it. -/
def FarQ (ms : List Mark) (W T : Nat) : Prop :=
  ∃ R ks a₁ b₁ W₁ R₁ t, LoopChain ms W R ks [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧ 178 ≤ R₁ ∧
    15 * W₁ ≤ 64 * (W₁ - b₁) ∧ (∀ d, PassCut d R₁ a₁ b₁ W₁) ∧
    steps t (roundStart ms W) = some (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) ∧
    steps (T - t) (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) = none

/-- From a loop entry with `FarQ`, reached t steps after a clean tape of width W < W′ with T − k steps left: as
`WideQ.pass`, with the far shape. -/
theorem FarQ.pass {ms : List Mark} {W W' T k t : Nat} (hlt : W < W')
    (ht : steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms W')) (hq : FarQ ms W' (T - k - t)) :
    ∃ R a b W₁ t₁, W < W₁ ∧ W' ≤ W₁ ∧ 178 ≤ R ∧ 15 * W₁ ≤ 64 * (W₁ - b) ∧
      PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R ∧
      (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W₁ : Int) / 2, (R : Int) / 2] = true) ∧
      steps t₁ (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ∧
      steps (T - k - t₁) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) = none ∧
      ∃ u, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩], W₁⟩ u ∧ u.wf ∧
        (EndClose u ∨ InteriorContact u) := by
  obtain ⟨R, ks, a₁, b₁, W₁, R₁, t', hch, hR, hsh, hcut, ht', hT₁⟩ := hq
  obtain ⟨hle, hP₁, u, hu, huw, hus⟩ := hch.last_halt hT₁
  refine ⟨R₁, a₁, b₁, W₁, t + t', by omega, hle, hR, hsh, hP₁, fun d => passCut_sym hR (hcut d),
    steps_seq ht ht', ?_, u, hu, huw, hus⟩
  rw [show T - k - (t + t') = T - k - t - t' by omega]
  exact hT₁

/-! ## From blank tape -/

/-- **What a halt from blank tape needs: an open clean tape, then an open pass start with its middle wall far from
the end.**  `blank_halt_open_wide` with the clean-tape tree whose loop entries are far (`clean_tree_far_step`) and
`entry_far_halt` at those entries: if the machine, started on blank tape, halts after T steps, then it reaches a
clean tape of even width W ≥ 2⁴¹ with W/2 in a cut class of `cleanTreeG directWidth d` at every depth, and halts
from there; and either W/2 is also in a cut class of `cleanTreeGF directWidth d` at every depth, and the mark model
reaches a stuck configuration from W, or the run from W reaches a pass start wider than W with right end R ≥ 178,
every gap at least 448 and 15W₁ ≤ 64(W₁ − b), that lies in a cut leaf of `passTreeSym d` at every depth, halts from
there, and the mark model reaches a stuck configuration from there. -/
theorem blank_halt_open_far (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      (((∀ d, (cleanTreeGF directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
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
      (fun d W => (cleanTreeGF directWidth d).cutMem [(W : Int) / 2, 0] = true)
      (fun ms W => EntryNoClose ms W ∧ EntryNoSmall ms W ∧ EntryFar ms W)
      (fun d W hW h => clean_tree_step_G directWidth d W (by decide) hW h)
      (fun d W hW h => clean_tree_far_step directWidth d W (by decide) hW h) FarQ
      (fun _ _ T' he hT' => entry_far_halt he.1 he.2.1 he.2.2 T' hT') (by decide) (by decide) hk₀ T hT
  · exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inl h⟩
  · obtain ⟨R, a, b, W₁, t₁, h1, -, h⟩ := FarQ.pass hlt ht hq
    exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inr ⟨R, a, b, W₁, t₁, h1, h⟩⟩

/-- **The kernel's step, with far loop entries.**  As `clean_wide_step_kernel`, with `cleanTreeGF 2³⁷ d` above
2³⁷. -/
theorem clean_far_step_kernel (d W : Nat) (hW : W % 2 = 0) (h : kernelPrefixWidth ≤ W) :
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
      (((W < 2 ^ 37 → (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
          (2 ^ 37 ≤ W → (cleanTreeGF (2 ^ 37) d).cutMem [(W : Int) / 2, 0] = true)) ∨
        (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W') ∨
        ((EntryNoClose ms' W' ∧ EntryNoSmall ms' W' ∧ EntryFar ms' W') ∧ W < W')) := by
  by_cases hl : W < 2 ^ 37
  · obtain ⟨n, k, ms', W', hr, hk, hc⟩ := clean_tree_step_G kernelPrefixWidth d W (by decide) hW h
    refine ⟨n, k, ms', W', hr, hk, ?_⟩
    rcases hc with hc | hc
    · exact Or.inl ⟨fun _ => hc, fun h' => absurd h' (Nat.not_le.mpr hl)⟩
    · exact Or.inr (Or.inl hc)
  · obtain ⟨n, k, ms', W', hr, hk, hc⟩ := clean_tree_far_step (2 ^ 37) d W (by decide) hW (Nat.le_of_not_lt hl)
    refine ⟨n, k, ms', W', hr, hk, ?_⟩
    rcases hc with hc | hc | hc
    · exact Or.inl ⟨fun h' => absurd h' hl, fun _ => hc⟩
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr hc)

/-- **The same, checked by the kernel alone.**  As `blank_halt_open_wide_kernel`, with the far shape. -/
theorem blank_halt_open_far_kernel (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, kernelPrefixWidth ≤ W ∧ W % 2 = 0 ∧
      (∀ d, (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      (((2 ^ 37 ≤ W → ∀ d, (cleanTreeGF (2 ^ 37) d).cutMem [(W : Int) / 2, 0] = true) ∧
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
      (fun ms W => EntryNoClose ms W ∧ EntryNoSmall ms W ∧ EntryFar ms W)
      (fun d W hW h => clean_tree_step_G kernelPrefixWidth d W (by decide) hW h) clean_far_step_kernel FarQ
      (fun _ _ T' he hT' => entry_far_halt he.1 he.2.1 he.2.2 T' hT') (by decide) (Nat.le_refl _) hk₀ T hT
  · exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inl ⟨fun hl d => (hcut d).2 hl, h⟩⟩
  · obtain ⟨R, a, b, W₁, t₁, h1, hle, h⟩ := FarQ.pass hlt ht hq
    exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inr ⟨R, a, b, W₁, t₁, h1, Nat.le_trans he.2.1.1 hle, h⟩⟩

/-- **The open question, with the far shape.**  As `never_halts_of_wide`, with the tree with far loop entries and
only the pass starts with 15W₁ ≤ 64(W₁ − b) to rule out. -/
theorem never_halts_of_far
    (hC : ∀ W, directWidth ≤ W → W % 2 = 0 → (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) →
      (∀ d, (cleanTreeGF directWidth d).cutMem [(W : Int) / 2, 0] = true) →
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
    blank_halt_open_far T hT
  · exact hC W hBW hW hG hS _ hTW
  · exact hP W R a b W₁ t hBW hW hG hlt hR hsh hP₁ hcut ht _ hT₁

#print axioms LoopChain.far_end
#print axioms entry_far_halt
#print axioms blank_halt_open_far
#print axioms blank_halt_open_far_kernel
#print axioms never_halts_of_far
