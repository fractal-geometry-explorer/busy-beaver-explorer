import WideHalt
import LoopFarHalt
open BB6 BB6.Sym

/-! # Where the chain's last pass start can come from

`thm/WideHalt.lean` shows that the last pass start of the loop's chain from a wide loop entry has W ≤ 64R + 6 or
15W ≤ 64(W − b).  That keeps one side of what each step gives.  Each kind of step, and the entry, fixes more:

* **A full pass** lands in a window with two sides.  The pass start it comes from has its middle wall at b ≥ 896
  (a ≥ 448 and b ≥ a + 448) and at most E − R − 449, and the landing's middle wall is b′ = (b + 48E − 8R + 1,250)/64,
  with R = 16R′ and E = W′ − 24.  So 15W′ + 144R′ + 375 ≤ 64(W′ − b′) ≤ 16W′ + 128R′ − 994.  The upper side was
  only in the untrusted shape check so far (`shape.py` in the halting-classes project files): a full pass puts the
  middle wall at about three quarters of the width or further, so W′ − b′ is at most about W′/4 + 2R′.
* **A round-7 break** lands with 32R′ ≥ 3E + 5R + 559, so W′ ≤ 32R′.
* **A half pass**, only ever the first step, from an entry with E ≤ 32R, lands with W′ ≤ 64R′ + 6 and, since
  2(W′ − b′) = E − b + R + 2 with b ≥ 896, with 2(W′ − b′) + 900 ≤ W′ + 2R′: its middle wall is at most about half the
  width from the end.
* **The loop entry itself** (a chain of no steps) has W ≤ 32R (`EntryWide`).

So the chain's last pass start has W ≤ 32R, or W ≤ 64R + 6 with 2(W − b) + 900 ≤ W + 2R, or lies in the full pass's
window (`WindowShape`, `step_window`, `LoopChain.window_end`).

A family with R and W − b fixed, whose width grows by 2^k, meets the window at most once, at a width between
4(W − b) − 8R + 62 and (64(W − b) − 144R − 375)/15, and the other two cases only below 64R + 7.  Six of the eight far
families of `thm/LoopFarHalt.lean` and PR #114's `thm/LoopFarCount.lean` have their base member below the window, the
next member far above it, and R below W/64 (`windowOutFams_out`): the families of `loop2_far_wide`, the first of
`loop3_far_wide`, `loop3_far_66`, `loop4_far_66`, `loop5_far_66` and `loop4_far_66c`, whose middle walls sit 0.37 to
0.61 of the width from the end.  So the run from blank tape halts through none of them, whatever the route after the
pass start (`blank_halt_not_window_family`).  The other two have W ≤ 32R: the second of `loop3_far_wide` (which PR
#114's count rules out, W ≡ 0 mod 6) and `loop5_far_66c`, which can only be the loop entry itself or a round-7
landing, and is no round-7 landing (32R < 3W).  Nothing here is evaluated but `windowOutFams_out`, by the kernel. -/

/-! ## The shape of the chain's last pass start -/

/-- The pass start with walls a, b and W − R − 1 has W ≤ 32R (a loop entry or a round-7 landing), or W ≤ 64R + 6 and
2(W − b) + 900 ≤ W + 2R (a half pass's landing), or lies in a full pass's landing window:
15W + 144R + 375 ≤ 64(W − b) ≤ 16W + 128R − 994. -/
def WindowShape (ms : List Mark) (W R : Nat) : Prop :=
  ∃ a b, ms = [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] ∧
    (W ≤ 32 * R ∨ (W ≤ 64 * R + 6 ∧ 2 * (W - b) + 900 ≤ W + 2 * R) ∨
      (15 * W + 144 * R + 375 ≤ 64 * (W - b) ∧ 64 * (W - b) + 994 ≤ 16 * W + 128 * R))

/-- **Each step of the loop's chain lands with the shape.**  A full pass lands with
15W′ + 144R′ + 375 ≤ 64(W′ − b′) ≤ 16W′ + 128R′ − 994 (the start's gaps, b ≥ 896 and b ≤ E − R − 449, through
b′ = (b + 48E − 8R + 1,250)/64); a round-7 break lands with 32R′ ≥ 3E + 5R + 559, so W′ ≤ 32R′; a half pass halves R,
so it lands with W′ ≤ 64R′ + 6 when E ≤ 32R, and with 2(W′ − b′) = E − b + R + 2 ≤ W′ + 2R′ − 900. -/
theorem step_window {k : StepKind} {n : Nat} {ms ms₁ : List Mark} {E R W₁ R₁ : Nat}
    (hP : PassStart448 ms E R) (hP₁ : PassStart448 ms₁ W₁ R₁)
    (hm : StepMap k n E R (passL1 ms E) W₁ R₁ (passL1 ms₁ W₁)) (hh : E % 4 = 2 → E ≤ 32 * R) :
    WindowShape ms₁ W₁ R₁ := by
  obtain ⟨a, b, rfl, -, -, -, -, -, h1, h2, h3⟩ := hP
  obtain ⟨a₁, b₁, rfl, -, -, -, -, -, g1, g2, g3⟩ := hP₁
  refine ⟨a₁, b₁, rfl, ?_⟩
  rw [passL1_www a b E R (by omega), passL1_www a₁ b₁ W₁ R₁ (by omega)] at hm
  cases k with
  | full =>
    obtain ⟨-, e1, e2, e3⟩ := hm
    right; right
    constructor <;> omega
  | half =>
    obtain ⟨-, e1, e2, e3, e4⟩ := hm
    have := hh e4
    right; left
    constructor <;> omega
  | break7 =>
    obtain ⟨-, e1, -, e3⟩ := hm
    left
    omega

/-- **The loop's chain ends with the shape.**  From a pass start with the shape, and with E ≤ 32R if its width
is ≡ 2 (mod 4), every pass start of the chain has the shape (`step_window`; a half pass is only ever the first
step). -/
theorem LoopChain.window_end {ms : List Mark} {W R : Nat} {ks : List StepKind} {ms' : List Mark} {W' R' : Nat}
    (h : LoopChain ms W R ks ms' W' R') :
    WindowShape ms W R → (W % 4 = 2 → W ≤ 32 * R) → WindowShape ms' W' R' := by
  induction h with
  | nil _ => intro hs _; exact hs
  | cons k n kk hP _ _ _ hW4 hmap tl ih =>
    intro _ hh
    exact ih (step_window hP tl.start hmap hh) (fun h4 => absurd h4 (by omega))

/-- **A family with R and W − b fixed meets the shape at most at its base member**, when its base member has R below
W/64 and is not in the window and its step 2^k is above 64(W₀ − b₀)/15. -/
theorem family_window {W₀ b₀ R₀ s X : Nat} (hb : b₀ ≤ W₀) (hw : 64 * R₀ + 6 < W₀)
    (hn : ¬ (15 * W₀ + 144 * R₀ + 375 ≤ 64 * (W₀ - b₀) ∧ 64 * (W₀ - b₀) + 994 ≤ 16 * W₀ + 128 * R₀))
    (hs : 64 * (W₀ - b₀) < 15 * s) (hX : X = 0 ∨ s ≤ X)
    (h : W₀ + X ≤ 32 * R₀ ∨ (W₀ + X ≤ 64 * R₀ + 6 ∧ 2 * (W₀ + X - (b₀ + X)) + 900 ≤ W₀ + X + 2 * R₀) ∨
      (15 * (W₀ + X) + 144 * R₀ + 375 ≤ 64 * (W₀ + X - (b₀ + X)) ∧
        64 * (W₀ + X - (b₀ + X)) + 994 ≤ 16 * (W₀ + X) + 128 * R₀)) : False := by
  omega

/-! ## From a wide loop entry -/

/-- **A halt from a wide loop entry that cannot close nor end small.**  As `entry_wide_halt`, and the chain's last pass
start has `WindowShape`'s shape. -/
theorem entry_window_halt {ms : List Mark} {W : Nat} (hn : EntryNoClose ms W) (hs : EntryNoSmall ms W)
    (hw : EntryWide ms W) (T : Nat) (hT : steps T (roundStart ms W) = none) :
    (∃ R ks a₁ b₁ W₁ R₁ t, LoopChain ms W R ks [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧ 178 ≤ R₁ ∧
      (W₁ ≤ 32 * R₁ ∨ (W₁ ≤ 64 * R₁ + 6 ∧ 2 * (W₁ - b₁) + 900 ≤ W₁ + 2 * R₁) ∨
        (15 * W₁ + 144 * R₁ + 375 ≤ 64 * (W₁ - b₁) ∧ 64 * (W₁ - b₁) + 994 ≤ 16 * W₁ + 128 * R₁)) ∧ (∀ d, PassCut d R₁ a₁ b₁ W₁) ∧
      steps t (roundStart ms W) = some (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) ∧
      steps (T - t) (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) = none) ∨
    ∃ k W', 0 < k ∧ W < W' ∧ W' % 2 = 0 ∧
      steps k (roundStart ms W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧
      steps (T - k) (roundStart [⟨.M, W' - 2⟩] W') = none := by
  rcases entry_small_halt hn hs T hT with ⟨R, ks, a₁, b₁, W₁, R₁, t, hch, hR, hcut, ht, hT'⟩ | h
  · obtain ⟨a, b, hms, -, -, -, -, -, -, -, h3⟩ := hch.start
    have h32 := hw R a b hms (by omega)
    obtain ⟨a', b', hms', hsh⟩ := hch.window_end ⟨a, b, hms, Or.inl h32⟩ (fun _ => h32)
    simp only [List.cons.injEq, Mark.mk.injEq, true_and, and_true] at hms'
    obtain ⟨-, rfl⟩ := hms'
    exact Or.inl ⟨R, ks, a₁, b₁, W₁, R₁, t, hch, hR, hsh, hcut, ht, hT'⟩
  · exact Or.inr h

/-- What a halt from a wide loop entry that cannot close nor end small needs (`entry_window_halt`), as
`blank_halt_open_of` takes it. -/
def WindowQ (ms : List Mark) (W T : Nat) : Prop :=
  ∃ R ks a₁ b₁ W₁ R₁ t, LoopChain ms W R ks [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧ 178 ≤ R₁ ∧
    (W₁ ≤ 32 * R₁ ∨ (W₁ ≤ 64 * R₁ + 6 ∧ 2 * (W₁ - b₁) + 900 ≤ W₁ + 2 * R₁) ∨
      (15 * W₁ + 144 * R₁ + 375 ≤ 64 * (W₁ - b₁) ∧ 64 * (W₁ - b₁) + 994 ≤ 16 * W₁ + 128 * R₁)) ∧ (∀ d, PassCut d R₁ a₁ b₁ W₁) ∧
    steps t (roundStart ms W) = some (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) ∧
    steps (T - t) (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) = none

/-- From a loop entry with `WindowQ`, reached t steps after a clean tape of width W < W′: as `WideQ.pass`. -/
theorem WindowQ.pass {ms : List Mark} {W W' T k t : Nat} (hlt : W < W')
    (ht : steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms W')) (hq : WindowQ ms W' (T - k - t)) :
    ∃ R a b W₁ t₁, W < W₁ ∧ W' ≤ W₁ ∧ 178 ≤ R ∧
      (W₁ ≤ 32 * R ∨ (W₁ ≤ 64 * R + 6 ∧ 2 * (W₁ - b) + 900 ≤ W₁ + 2 * R) ∨
        (15 * W₁ + 144 * R + 375 ≤ 64 * (W₁ - b) ∧ 64 * (W₁ - b) + 994 ≤ 16 * W₁ + 128 * R)) ∧
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

/-- **What a halt from blank tape needs, with the window.**  `blank_halt_open_wide` with the pass start in `WindowShape`'s
shape: W₁ ≤ 32R, or W₁ ≤ 64R + 6 and 2(W₁ − b) + 900 ≤ W₁ + 2R, or 15W₁ + 144R + 375 ≤ 64(W₁ − b) ≤ 16W₁ + 128R − 994. -/
theorem blank_halt_open_window (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      (((∀ d, (cleanTreeGW directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
          ∃ u, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ u ∧ u.wf ∧ (EndClose u ∨ InteriorContact u)) ∨
        ∃ R a b W₁ t, W < W₁ ∧ 178 ≤ R ∧
          (W₁ ≤ 32 * R ∨ (W₁ ≤ 64 * R + 6 ∧ 2 * (W₁ - b) + 900 ≤ W₁ + 2 * R) ∨
        (15 * W₁ + 144 * R + 375 ≤ 64 * (W₁ - b) ∧ 64 * (W₁ - b) + 994 ≤ 16 * W₁ + 128 * R)) ∧
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
      (fun d W => (cleanTreeGW directWidth d).cutMem [(W : Int) / 2, 0] = true)
      (fun ms W => EntryNoClose ms W ∧ EntryNoSmall ms W ∧ EntryWide ms W)
      (fun d W hW h => clean_tree_step_G directWidth d W (by decide) hW h)
      (fun d W hW h => clean_tree_wide_step directWidth d W (by decide) hW h) WindowQ
      (fun _ _ T' he hT' => entry_window_halt he.1 he.2.1 he.2.2 T' hT') (by decide) (by decide) hk₀ T hT
  · exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inl h⟩
  · obtain ⟨R, a, b, W₁, t₁, h1, -, h⟩ := WindowQ.pass hlt ht hq
    exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inr ⟨R, a, b, W₁, t₁, h1, h⟩⟩

/-- The six far families with R below W/64 and outside the window: those of `loop2_far_wide`, the first of
`loop3_far_wide`, `loop3_far_66`, `loop4_far_66` and `loop5_far_66` (`thm/LoopFarHalt.lean`), and of `loop4_far_66c`
(PR #114's `thm/LoopFarCount.lean`). -/
def windowOutFams : List Fam :=
  [⟨4929578547392, 12923998950, 2756403453598, 60, 78⟩, ⟨5413114788032, 83378934502, 3380852022942, 60, 78⟩,
   ⟨192745493072062232768, 3795450608325350, 118966107678443298462, 98, 128⟩,
   ⟨147950097082544601280, 18101603638022886, 74199323995024383646, 98, 128⟩,
   ⟨119580288664381470912, 725281227840787174, 47243874825895927454, 98, 128⟩,
   ⟨153220594947397302464, 1155616650921612006, 81744851954444263070, 98, 128⟩]

/-- Five of them are families of `loopFar` (`thm/LoopFarHalt.lean`). -/
theorem windowOutFams_loopFar :
    windowOutFams.take 5 = loopFar2 ++ loopFar3.take 1 ++ loopFar66 ++ loopFar4 ++ loopFar5 := rfl

/-- **None of the six meets the shape at any member**: its base member has 64R + 6 < W and is not in the window, and its
step 2^k is above 64(W₀ − b₀)/15. -/
theorem windowOutFams_out : windowOutFams.all (fun F => decide (F.b0 ≤ F.W0) && decide (64 * F.R0 + 6 < F.W0) &&
    !(decide (15 * F.W0 + 144 * F.R0 + 375 ≤ 64 * (F.W0 - F.b0)) &&
      decide (64 * (F.W0 - F.b0) + 994 ≤ 16 * F.W0 + 128 * F.R0)) &&
    decide (64 * (F.W0 - F.b0) < 15 * 2 ^ F.k)) = true := by decide +kernel

/-- **The run from blank tape halts through none of the six far families.**  If the machine halts from blank tape, it
reaches a clean tape that both trees leave open at every depth and halts from there, or the pass start that
`blank_halt_open_window` names is a member of none of `windowOutFams`, whatever its first wall. -/
theorem blank_halt_not_window_family (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ((∀ d, (cleanTreeGW directWidth d).cutMem [(W : Int) / 2, 0] = true) ∨
        ∃ R a b W₁ t, W < W₁ ∧ 178 ≤ R ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R ∧
          (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W₁ : Int) / 2, (R : Int) / 2] = true) ∧
          steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ∧
          steps (T - k - t) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) = none ∧
          ∀ F ∈ windowOutFams, ∀ s, ¬ (R = F.R0 ∧ b = F.b0 + 2 ^ F.k * s ∧ W₁ = F.W0 + 2 ^ F.k * s)) := by
  obtain ⟨W, k, hBW, hW, hG, hk, hTW, ⟨hS, -⟩ | ⟨R, a, b, W₁, t, hlt, hR, hsh, hP₁, hcut, ht, hT₁, -⟩⟩ :=
    blank_halt_open_window T hT
  · exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inl hS⟩
  · refine ⟨W, k, hBW, hW, hG, hk, hTW, Or.inr ⟨R, a, b, W₁, t, hlt, hR, hP₁, hcut, ht, hT₁, ?_⟩⟩
    rintro F hF s ⟨rfl, rfl, rfl⟩
    have hc := List.all_eq_true.1 windowOutFams_out F hF
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hb, hw⟩, hn⟩, hs⟩ := hc
    have hX : 2 ^ F.k * s = 0 ∨ 2 ^ F.k ≤ 2 ^ F.k * s := by
      rcases Nat.eq_zero_or_pos s with rfl | hs0
      · exact Or.inl (Nat.mul_zero _)
      · exact Or.inr (Nat.le_mul_of_pos_right _ hs0)
    have hn' : ¬ (15 * F.W0 + 144 * F.R0 + 375 ≤ 64 * (F.W0 - F.b0) ∧
        64 * (F.W0 - F.b0) + 994 ≤ 16 * F.W0 + 128 * F.R0) := by
      intro ⟨h1, h2⟩; simp_all
    exact family_window hb hw hn' hs hX hsh

#print axioms step_window
#print axioms LoopChain.window_end
#print axioms windowOutFams_out
#print axioms blank_halt_open_window
#print axioms blank_halt_not_window_family
