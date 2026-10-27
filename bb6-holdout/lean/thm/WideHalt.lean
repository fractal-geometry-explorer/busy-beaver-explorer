import OpenSmallHalt
import PassOpenHalt
import CleanWideTheorem
open BB6 BB6.Sym

/-! # The pass starts a halt can need are wide

`blank_halt_open_small` (`thm/OpenSmallHalt.lean`) leaves a halt from blank tape at a clean tape that both clean-tape
trees leave open at every depth, or at a pass start with R ≥ 178 that `passTreeSym` leaves open at every depth, the
last pass start of the loop's chain from a loop entry.  Pass starts of that kind halt (`open_halt_families`,
`thm/PassOpenHalt.lean`), in families with R and W − b fixed.  This file shows that the chain from a loop entry
reaches none of them above width 2⁴¹, from the steps' maps alone:

* A full pass lands with 64(W′ − b′) = 16E − b + 128R′ + 286 ≥ 15E + 144R′ + 735, so the landing's middle wall leaves
  at least 15/64 of the width to the end; a round-7 break lands with 32R′ = 4E + 4R − b + 110 ≥ 3E + 5R + 559, so its
  right end is at least 3/32 of the width; a half pass, only ever the first step, halves the entry's right end
  (`step_wide`).
* The loop entries of the clean-tape trees are early: their right end is a fixed fraction of the width.  The entry
  test `cleanWideOK` (`BB6/WideEntry.lean`) adds W ≤ 32R (`EntryWide`) to `cleanSmallOK`, and `cleanTreeGW`
  (`thm/CleanWideTheorem.lean`) is the clean-tape tree with it; at 36 digits over the widths ≥ 2⁴¹ every one of the
  28,660 entries passes it (`EntryForms.lean`, untrusted; `thm/CleanWideMass.lean` counts the same entries and cut
  classes as for `cleanTreeGS`).
* So the chain's last pass start has W ≤ 64R + 6 or 15W ≤ 64(W − b) (`WideShape`, `LoopChain.wide_end`), hence
  W ≤ 32(W − b + 2R) + 6 (`wideShape_bound`).

`blank_halt_open_wide` is `blank_halt_open_small` with that shape at the pass start, and `never_halts_of_wide` the
open question with it.  A family with R and W − b fixed meets the shape only at widths up to 32(W − b + 2R) + 6: none
of the eight families of `open_halt_families` above 58,502 (`openHaltFams_wide`), so the run from blank tape halts
through none of them (`blank_halt_not_family`).  The bound holds whatever the route from the pass start to the halt.
On the main route the run meets the end off the chain at (W − b + 2R + 14)/4 = 2^(m−2) − 2 and halves to 0, so
W − b + 2R + 22 = 2^m, and a pass start a halt needs is on that lane only if W ≤ 2^(m+5) + 6 (`wideShape_pow2`); other
routes meet the end more times before the halving starts.  Nothing here is evaluated: the tree is built by the proved
explorer. -/

/-! ## The shape of the chain's last pass start -/

/-- The pass start with walls a, b and W − R − 1 has its right end at least a 64th of the width (less 6), or its middle
wall at least 15/64 of the width from the end. -/
def WideShape (ms : List Mark) (W R : Nat) : Prop :=
  ∃ a b, ms = [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] ∧ (W ≤ 64 * R + 6 ∨ 15 * W ≤ 64 * (W - b))

/-- The left countdown of a pass start, with the last wall at W − R − 1. -/
theorem passL1_www (a b W R : Nat) (h : R + 1 ≤ W) :
    passL1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W = 147 * (b : Int) - 112 * W + 392 * R - 186 := by
  show loopL1 b (W - R - 1) W = _
  unfold loopL1
  omega

/-- **Each step of the loop's chain lands wide.**  From a pass start of width E with every gap at least 448, a full
pass lands with 64(W′ − b′) ≥ 15E + 144R′ + 735 and a round-7 break with 32R′ ≥ 3E + 5R + 559; a half pass halves R,
so it lands with W′ ≤ 64R′ + 6 when E ≤ 32R. -/
theorem step_wide {k : StepKind} {n : Nat} {ms ms₁ : List Mark} {E R W₁ R₁ : Nat}
    (hP : PassStart448 ms E R) (hP₁ : PassStart448 ms₁ W₁ R₁)
    (hm : StepMap k n E R (passL1 ms E) W₁ R₁ (passL1 ms₁ W₁)) (hh : E % 4 = 2 → E ≤ 32 * R) :
    WideShape ms₁ W₁ R₁ := by
  obtain ⟨a, b, rfl, -, -, -, -, -, h1, h2, h3⟩ := hP
  obtain ⟨a₁, b₁, rfl, -, -, -, -, -, g1, g2, g3⟩ := hP₁
  refine ⟨a₁, b₁, rfl, ?_⟩
  rw [passL1_www a b E R (by omega), passL1_www a₁ b₁ W₁ R₁ (by omega)] at hm
  cases k with
  | full =>
    obtain ⟨-, e1, e2, e3⟩ := hm
    right
    omega
  | half =>
    obtain ⟨-, e1, -, e3, e4⟩ := hm
    have := hh e4
    left
    omega
  | break7 =>
    obtain ⟨-, e1, -, e3⟩ := hm
    left
    omega

/-- **The loop's chain ends wide.**  From a pass start with the shape, and with E ≤ 32R if its width is ≡ 2 (mod 4)
(where a half pass can start the chain), every pass start of the chain has the shape: after a full pass or a round-7
break by `step_wide`, after a half pass by the hypothesis (a half pass is only ever the first step, since every
landing has width ≡ 0 mod 4). -/
theorem LoopChain.wide_end {ms : List Mark} {W R : Nat} {ks : List StepKind} {ms' : List Mark} {W' R' : Nat}
    (h : LoopChain ms W R ks ms' W' R') :
    WideShape ms W R → (W % 4 = 2 → W ≤ 32 * R) → WideShape ms' W' R' := by
  induction h with
  | nil _ => intro hs _; exact hs
  | cons k n kk hP _ _ _ hW4 hmap tl ih =>
    intro _ hh
    exact ih (step_wide hP tl.start hmap hh) (fun h4 => absurd h4 (by omega))

/-- **The shape bounds the width**: W ≤ 32(W − b + 2R) + 6. -/
theorem wideShape_bound {b W R : Nat} (hb : b ≤ W) (h : W ≤ 64 * R + 6 ∨ 15 * W ≤ 64 * (W - b)) :
    W ≤ 32 * (W - b + 2 * R) + 6 := by
  omega

/-- **On a class whose W − b + 2R + 22 is a power of two 2^m**, as on the main route of the halting landings (the run
meets the end off the chain at (W − b + 2R + 14)/4 = 2^(m−2) − 2, then halves to 0), the shape needs
W ≤ 2^(m+5) + 6. -/
theorem wideShape_pow2 {b W R m : Nat} (hb : b ≤ W) (h : W ≤ 64 * R + 6 ∨ 15 * W ≤ 64 * (W - b))
    (hm : W - b + 2 * R + 22 = 2 ^ m) : W ≤ 2 ^ (m + 5) + 6 := by
  have := wideShape_bound hb h
  rw [Nat.pow_add]
  omega

/-- **The eight families meet the shape only below width 58,502**: their right ends are at most 914 and their
W − b at most 3,702. -/
theorem openHaltFams_wide {F : Fam} (hF : F ∈ openHaltFams) (t : Nat)
    (h : F.W0 + 2 ^ F.k * t ≤ 64 * F.R0 + 6 ∨
      15 * (F.W0 + 2 ^ F.k * t) ≤ 64 * (F.W0 + 2 ^ F.k * t - (F.b0 + 2 ^ F.k * t))) :
    F.W0 + 2 ^ F.k * t ≤ 58502 := by
  have hc : F.R0 ≤ 914 ∧ F.b0 ≤ F.W0 ∧ F.W0 - F.b0 ≤ 3702 := by
    simp only [openHaltFams, List.mem_cons, List.mem_nil_iff, or_false] at hF
    rcases hF with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  generalize 2 ^ F.k * t = X at h ⊢
  omega

/-! ## From a wide loop entry -/

/-- **A halt from a wide loop entry that cannot close nor end small.**  As `entry_small_halt`, and the chain's last pass
start has the shape: W₁ ≤ 64R₁ + 6 or 15W₁ ≤ 64(W₁ − b₁). -/
theorem entry_wide_halt {ms : List Mark} {W : Nat} (hn : EntryNoClose ms W) (hs : EntryNoSmall ms W)
    (hw : EntryWide ms W) (T : Nat) (hT : steps T (roundStart ms W) = none) :
    (∃ R ks a₁ b₁ W₁ R₁ t, LoopChain ms W R ks [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧ 178 ≤ R₁ ∧
      (W₁ ≤ 64 * R₁ + 6 ∨ 15 * W₁ ≤ 64 * (W₁ - b₁)) ∧ (∀ d, PassCut d R₁ a₁ b₁ W₁) ∧
      steps t (roundStart ms W) = some (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) ∧
      steps (T - t) (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) = none) ∨
    ∃ k W', 0 < k ∧ W < W' ∧ W' % 2 = 0 ∧
      steps k (roundStart ms W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧
      steps (T - k) (roundStart [⟨.M, W' - 2⟩] W') = none := by
  rcases entry_small_halt hn hs T hT with ⟨R, ks, a₁, b₁, W₁, R₁, t, hch, hR, hcut, ht, hT'⟩ | h
  · obtain ⟨a, b, hms, -, -, -, -, -, -, -, h3⟩ := hch.start
    have h32 := hw R a b hms (by omega)
    obtain ⟨a', b', hms', hsh⟩ := hch.wide_end ⟨a, b, hms, Or.inl (by omega)⟩ (fun _ => h32)
    simp only [List.cons.injEq, Mark.mk.injEq, true_and, and_true] at hms'
    obtain ⟨-, rfl⟩ := hms'
    exact Or.inl ⟨R, ks, a₁, b₁, W₁, R₁, t, hch, hR, hsh, hcut, ht, hT'⟩
  · exact Or.inr h

/-- What a halt from a wide loop entry that cannot close nor end small needs (`entry_wide_halt`), as
`blank_halt_open_of` takes it. -/
def WideQ (ms : List Mark) (W T : Nat) : Prop :=
  ∃ R ks a₁ b₁ W₁ R₁ t, LoopChain ms W R ks [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧ 178 ≤ R₁ ∧
    (W₁ ≤ 64 * R₁ + 6 ∨ 15 * W₁ ≤ 64 * (W₁ - b₁)) ∧ (∀ d, PassCut d R₁ a₁ b₁ W₁) ∧
    steps t (roundStart ms W) = some (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) ∧
    steps (T - t) (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) = none

/-- From a loop entry with `WideQ`, reached t steps after a clean tape of width W < W′ with T − k steps left: as
`SmallQ.pass`, and the pass start has the shape. -/
theorem WideQ.pass {ms : List Mark} {W W' T k t : Nat} (hlt : W < W')
    (ht : steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms W')) (hq : WideQ ms W' (T - k - t)) :
    ∃ R a b W₁ t₁, W < W₁ ∧ W' ≤ W₁ ∧ 178 ≤ R ∧ (W₁ ≤ 64 * R + 6 ∨ 15 * W₁ ≤ 64 * (W₁ - b)) ∧
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

/-- **What a halt from blank tape needs: an open clean tape, then a wide open pass start.**  `blank_halt_open_small`
with the clean-tape tree whose loop entries are also wide (`clean_tree_wide_step`) and `entry_wide_halt` at those
entries: if the machine, started on blank tape, halts after T steps, then it reaches a clean tape of even width
W ≥ 2⁴¹ with W/2 in a cut class of `cleanTreeG directWidth d` at every depth, and halts from there; and either W/2 is
also in a cut class of `cleanTreeGW directWidth d` at every depth, and the mark model reaches a stuck configuration
from W, or the run from W reaches a pass start wider than W with right end R ≥ 178, every gap at least 448 and
W₁ ≤ 64R + 6 or 15W₁ ≤ 64(W₁ − b), that lies in a cut leaf of `passTreeSym d` at every depth, halts from there, and
the mark model reaches a stuck configuration from there. -/
theorem blank_halt_open_wide (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      (((∀ d, (cleanTreeGW directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
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
      (fun d W => (cleanTreeGW directWidth d).cutMem [(W : Int) / 2, 0] = true)
      (fun ms W => EntryNoClose ms W ∧ EntryNoSmall ms W ∧ EntryWide ms W)
      (fun d W hW h => clean_tree_step_G directWidth d W (by decide) hW h)
      (fun d W hW h => clean_tree_wide_step directWidth d W (by decide) hW h) WideQ
      (fun _ _ T' he hT' => entry_wide_halt he.1 he.2.1 he.2.2 T' hT') (by decide) (by decide) hk₀ T hT
  · exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inl h⟩
  · obtain ⟨R, a, b, W₁, t₁, h1, -, h⟩ := WideQ.pass hlt ht hq
    exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inr ⟨R, a, b, W₁, t₁, h1, h⟩⟩

/-- **The kernel's step, with wide loop entries.**  As `clean_small_step_kernel`, with `cleanTreeGW 2³⁷ d` above
2³⁷. -/
theorem clean_wide_step_kernel (d W : Nat) (hW : W % 2 = 0) (h : kernelPrefixWidth ≤ W) :
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
      (((W < 2 ^ 37 → (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
          (2 ^ 37 ≤ W → (cleanTreeGW (2 ^ 37) d).cutMem [(W : Int) / 2, 0] = true)) ∨
        (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W') ∨
        ((EntryNoClose ms' W' ∧ EntryNoSmall ms' W' ∧ EntryWide ms' W') ∧ W < W')) := by
  by_cases hl : W < 2 ^ 37
  · obtain ⟨n, k, ms', W', hr, hk, hc⟩ := clean_tree_step_G kernelPrefixWidth d W (by decide) hW h
    refine ⟨n, k, ms', W', hr, hk, ?_⟩
    rcases hc with hc | hc
    · exact Or.inl ⟨fun _ => hc, fun h' => absurd h' (Nat.not_le.mpr hl)⟩
    · exact Or.inr (Or.inl hc)
  · obtain ⟨n, k, ms', W', hr, hk, hc⟩ := clean_tree_wide_step (2 ^ 37) d W (by decide) hW (Nat.le_of_not_lt hl)
    refine ⟨n, k, ms', W', hr, hk, ?_⟩
    rcases hc with hc | hc | hc
    · exact Or.inl ⟨fun h' => absurd h' hl, fun _ => hc⟩
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr hc)

/-- **The same, checked by the kernel alone.**  As `blank_halt_open_small_kernel`, with the pass start's shape. -/
theorem blank_halt_open_wide_kernel (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, kernelPrefixWidth ≤ W ∧ W % 2 = 0 ∧
      (∀ d, (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      (((2 ^ 37 ≤ W → ∀ d, (cleanTreeGW (2 ^ 37) d).cutMem [(W : Int) / 2, 0] = true) ∧
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
      (fun ms W => EntryNoClose ms W ∧ EntryNoSmall ms W ∧ EntryWide ms W)
      (fun d W hW h => clean_tree_step_G kernelPrefixWidth d W (by decide) hW h) clean_wide_step_kernel WideQ
      (fun _ _ T' he hT' => entry_wide_halt he.1 he.2.1 he.2.2 T' hT') (by decide) (Nat.le_refl _) hk₀ T hT
  · exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inl ⟨fun hl d => (hcut d).2 hl, h⟩⟩
  · obtain ⟨R, a, b, W₁, t₁, h1, hle, h⟩ := WideQ.pass hlt ht hq
    exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inr ⟨R, a, b, W₁, t₁, h1, Nat.le_trans he.2.1.1 hle, h⟩⟩

/-- **The open question, with the shape.**  As `never_halts_of_open`, with the tree with wide loop entries and only
the pass starts with W₁ ≤ 64R + 6 or 15W₁ ≤ 64(W₁ − b) to rule out. -/
theorem never_halts_of_wide
    (hC : ∀ W, directWidth ≤ W → W % 2 = 0 → (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) →
      (∀ d, (cleanTreeGW directWidth d).cutMem [(W : Int) / 2, 0] = true) →
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
    blank_halt_open_wide T hT
  · exact hC W hBW hW hG hS _ hTW
  · exact hP W R a b W₁ t hBW hW hG hlt hR hsh hP₁ hcut ht _ hT₁

/-- **The run from blank tape halts through none of the eight families.**  If the machine halts from blank tape, it
reaches a clean tape that both trees leave open at every depth and halts from there, or the pass start that
`blank_halt_open_wide` names is a member of none of the families of `open_halt_families`: it is wider than 2⁴¹, and
they meet the shape only below 58,502. -/
theorem blank_halt_not_family (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ((∀ d, (cleanTreeGW directWidth d).cutMem [(W : Int) / 2, 0] = true) ∨
        ∃ R a b W₁ t, W < W₁ ∧ 178 ≤ R ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R ∧
          (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W₁ : Int) / 2, (R : Int) / 2] = true) ∧
          steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ∧
          steps (T - k - t) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) = none ∧
          ∀ F ∈ openHaltFams, ∀ s, ¬ (R = F.R0 ∧ b = F.b0 + 2 ^ F.k * s ∧ W₁ = F.W0 + 2 ^ F.k * s)) := by
  obtain ⟨W, k, hBW, hW, hG, hk, hTW, ⟨hS, -⟩ | ⟨R, a, b, W₁, t, hlt, hR, hsh, hP₁, hcut, ht, hT₁, -⟩⟩ :=
    blank_halt_open_wide T hT
  · exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inl hS⟩
  · refine ⟨W, k, hBW, hW, hG, hk, hTW, Or.inr ⟨R, a, b, W₁, t, hlt, hR, hP₁, hcut, ht, hT₁, ?_⟩⟩
    rintro F hF s ⟨rfl, rfl, rfl⟩
    have h58 := openHaltFams_wide hF s hsh
    have h41 : directWidth = 2199023255552 := rfl
    generalize 2 ^ F.k * s = X at h58 hlt
    omega

#print axioms LoopChain.wide_end
#print axioms entry_wide_halt
#print axioms blank_halt_open_wide
#print axioms blank_halt_open_wide_kernel
#print axioms never_halts_of_wide
#print axioms blank_halt_not_family
