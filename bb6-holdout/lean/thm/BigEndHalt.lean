import FarHalt
import CleanBigTheorem
open BB6 BB6.Sym

/-! # The pass start a halt needs has a right end of at least 769

`blank_halt_open_far` (`thm/FarHalt.lean`) gives the pass start a halt from blank tape needs a right end R ≥ 178,
from `LoopChain.small_end`.  Nothing in that argument needs 178 but the round-7 break, and from a width of 2⁴¹ the
break lands higher:

* A full pass divides R by 16 and the left countdown L₁ by 64, so it keeps `NoEndBelow N` (`noEnd_full`); a half pass
  is only ever the first step, and the entry check covers it.
* A round-7 break from a pass start of width E ≥ 2⁴¹ lands with 32R′ > S = 3E + 5R ≥ 3 · 2⁴¹ and
  0 < 96L₁′ < 385 · 32R′.  To end at a right end r ≤ 768 after p full passes, R′ = 16^p · r and L₁′ = 64^p · ℓ with
  ℓ ≡ 3 (mod 7), so ℓ ≥ 3.  For p ≤ 7 that makes 32R′ ≤ 2³³ · 768 = 3 · 2⁴¹, too small, and for p ≥ 8 it needs
  96 · 4^p · ℓ < 12,320 · r, but the left side is at least 96 · 4⁸ · 3 (`break7_noEnd769`).  The bound
  R′³/L₁′² ≥ S/527,023 of `break7_noSmall` folds the two into one and gives only 483.
* The last pass start of the chain has `NoEndBelow 769` with p = 0, so its right end is at least 769 (`noEnd_end`).

The loop entries of the clean-tape tree are wider than 2⁴¹ and far above these right ends (R > W/29.02 at 36
digits), so ending below 769 takes at least 7 exact full passes from the entry, and `bigEntryOK 769` checks on each
entry class that no run of them does, as `smallEntryOK` does below 178.  Every one of the 28,660 loop entries at 36
digits passes (`thm/CleanBigMass.lean`).  So the chain's last pass start has R ≥ 769 as well as 15W ≤ 64(W − b)
(`LoopChain.big_end`, `entry_big_halt`, `blank_halt_open_big`): every halting class with R below 769 is out of its
reach, whatever the class's route to the close, and with it every class the census of pass starts found at R from
178 to 262, 294 and 486.

There is no kernel-only version: its clean-tape tree starts at 2³⁷, where a round-7 break clears only 383. -/

/-! ## The chain's last right end -/

/-- A full pass keeps `NoEndBelow N`: a run of full passes from its landing is one from its start, one pass longer. -/
theorem noEnd_full {N : Nat} {R L R' L' : Int} (h : NoEndBelow N R L) (hR : R = 16 * R') (hL : L = 64 * L') :
    NoEndBelow N R' L' := by
  intro p r ℓ hr hR' hL' h7
  refine h (p + 1) r ℓ hr ?_ ?_ h7
  · rw [hR, hR', Int.pow_succ, Int.mul_comm ((16 : Int) ^ p) 16, Int.mul_assoc]
  · rw [hL, hL', Int.pow_succ, Int.mul_comm ((64 : Int) ^ p) 64, Int.mul_assoc]

/-- At a pass start with `NoEndBelow N` the right end is at least N (no passes at all). -/
theorem noEnd_end {N R : Nat} {L : Int} (h : NoEndBelow N R L) (h7 : L % 7 = 3) : N ≤ R := by
  apply Nat.le_of_not_lt
  intro hlt
  exact h 0 R L hlt (by simp) (by simp) h7

/-- **A round-7 break from a pass start of width at least 2⁴¹ lands above the right ends below 769**, for every run
of full passes after it: it lands with 32R′ > 3 · 2⁴¹ and 0 < 96L₁′ < 12,320R′.  After p ≤ 7 full passes to r ≤ 768,
32R′ = 2^(4p+5) · r ≤ 3 · 2⁴¹; after p ≥ 8, 96 · 4^p · ℓ < 12,320 · r with ℓ ≥ 3, though 96 · 4⁸ · 3 > 12,320 · 768. -/
theorem break7_noEnd769 {ms : List Mark} {E R : Nat} (hP : PassStart448 ms E R) {n W R' : Nat} {L' : Int}
    (hm : StepMap .break7 n E R (passL1 ms E) W R' L') (hE : 2 ^ 41 ≤ E) : NoEndBelow 769 R' L' := by
  obtain ⟨a, b, rfl, -, -, -, -, -, h1, h2, h3⟩ := hP
  obtain ⟨-, hR', hL', -⟩ := hm
  have hL : passL1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E = 147 * (b : Int) - 112 * E + 392 * R - 186 := by
    show loopL1 b (E - R - 1) E = _
    unfold loopL1
    omega
  rw [hL] at hR' hL'
  have hE' : 2199023255552 ≤ E := hE
  have hx : 6597069766656 < 32 * R' := by omega
  have hy : 96 * L' < 12320 * (R' : Int) := by omega
  have hpos : 0 < L' := by omega
  intro p r ℓ hr hR hLp h7
  rcases Nat.lt_or_ge p 8 with hp | hp
  · have hRn : R' = 16 ^ p * r := by exact_mod_cast hR
    have h16 : 16 ^ p ≤ 16 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
    have hle : R' ≤ 16 ^ 7 * 768 := by rw [hRn]; exact Nat.mul_le_mul h16 (by omega)
    have : (16 : Nat) ^ 7 * 768 = 206158430208 := by decide
    omega
  · have e64 : (64 : Int) ^ p = 16 ^ p * 4 ^ p := by rw [← Int.mul_pow]; rfl
    have hX : (0 : Int) < 16 ^ p := Int.pow_pos (by decide)
    have hY : (0 : Int) < 4 ^ p := Int.pow_pos (by decide)
    rw [hLp, hR, e64] at hy
    rw [hLp, e64] at hpos
    have hy' : 16 ^ p * (96 * (4 ^ p * ℓ)) < 16 ^ p * (12320 * (r : Int)) := by
      rw [Int.mul_left_comm (16 ^ p) 96, Int.mul_left_comm (16 ^ p) 12320, ← Int.mul_assoc (16 ^ p) (4 ^ p) ℓ]
      exact hy
    have hz := Int.lt_of_mul_lt_mul_left hy' (Int.le_of_lt hX)
    have hℓ : 0 < ℓ := by
      rcases Int.lt_or_le 0 ℓ with h | h
      · exact h
      · have := Int.mul_nonpos_of_nonneg_of_nonpos (Int.le_of_lt (Int.mul_pos hX hY)) h
        omega
    have h4 : (4 : Int) ^ 8 ≤ 4 ^ p := by exact_mod_cast Nat.pow_le_pow_right (show 0 < 4 by decide) hp
    have hm : (4 : Int) ^ 8 * 3 ≤ 4 ^ p * ℓ := Int.mul_le_mul h4 (by omega) (by decide) (Int.le_of_lt hY)
    have : (4 : Int) ^ 8 = 65536 := by decide
    generalize 4 ^ p * ℓ = A at hz hm
    omega

namespace LoopChain

/-- **The loop's chain from a start of width at least 2⁴¹ with `NoEndBelow 769` ends at a right end of at least
769.**  As `small_end`: every pass start of the chain after the first again has `NoEndBelow 769`, after a full pass
by `noEnd_full`, after a half pass by the hypothesis (a half pass is only ever the first step), after a round-7 break
by `break7_noEnd769`; so the last one has R′ ≥ 769. -/
theorem big_end {ms : List Mark} {W R : Nat} {ks : List StepKind} {ms' : List Mark} {W' R' : Nat}
    (h : LoopChain ms W R ks ms' W' R') : 2 ^ 41 ≤ W → NoEndBelow 769 R (passL1 ms W) →
    (W % 4 = 2 → ∀ R₁ L₁ : Int, 2 * R₁ = (R : Int) → 2 * L₁ = passL1 ms W + 35 * (W : Int) - 147 * (R : Int) - 60 →
      NoEndBelow 769 R₁ L₁) → 769 ≤ R' := by
  induction h with
  | nil hP =>
    intro _ hs _
    obtain ⟨a, b, rfl, -⟩ := hP
    exact noEnd_end hs (loopL1_mod7 _ _ _)
  | cons k n kk hP _ _ _ hW4 hmap _ ih =>
    intro hW hs hh
    refine ih ?_ ?_ (fun h4 => absurd h4 (by omega))
    · cases k <;> simp only [StepMap] at hmap <;> omega
    · cases k with
      | full =>
        obtain ⟨-, h16, h64, -⟩ := hmap
        exact noEnd_full hs (by omega) h64.symm
      | half =>
        obtain ⟨-, h2, h2L, -, hE4⟩ := hmap
        exact hh hE4 _ _ (by omega) h2L
      | break7 => exact break7_noEnd769 hP hmap hW

end LoopChain

/-! ## From a loop entry that ends big and far -/

/-- **A halt from a loop entry that cannot close, ends big and is far.**  As `entry_far_halt`, and the chain's last
pass start has right end R₁ ≥ 769. -/
theorem entry_big_halt {ms : List Mark} {W : Nat} (hn : EntryNoClose ms W) (hb : EntryBigEnd 769 ms W)
    (hf : EntryFar ms W) (T : Nat) (hT : steps T (roundStart ms W) = none) :
    (∃ R ks a₁ b₁ W₁ R₁ t, LoopChain ms W R ks [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧ 769 ≤ R₁ ∧
      15 * W₁ ≤ 64 * (W₁ - b₁) ∧ (∀ d, PassCut d R₁ a₁ b₁ W₁) ∧
      steps t (roundStart ms W) = some (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) ∧
      steps (T - t) (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) = none) ∨
    ∃ k W', 0 < k ∧ W < W' ∧ W' % 2 = 0 ∧
      steps k (roundStart ms W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧
      steps (T - k) (roundStart [⟨.M, W' - 2⟩] W') = none := by
  rcases entry_far_halt hn (hb.small (by decide)) hf T hT with
    ⟨R, ks, a₁, b₁, W₁, R₁, t, hch, -, hsh, hcut, ht, hT'⟩ | h
  · obtain ⟨a, b, hms, -, -, -, -, -, -, -, h3⟩ := hch.start
    obtain ⟨hb1, hb2⟩ := hb.2 R a b hms (by omega)
    exact Or.inl ⟨R, ks, a₁, b₁, W₁, R₁, t, hch, hch.big_end hb.1 hb1 hb2, hsh, hcut, ht, hT'⟩
  · exact Or.inr h

/-- What a halt from a loop entry that cannot close, ends big and is far needs (`entry_big_halt`), as
`blank_halt_open_of` takes it. -/
def BigQ (ms : List Mark) (W T : Nat) : Prop :=
  ∃ R ks a₁ b₁ W₁ R₁ t, LoopChain ms W R ks [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧ 769 ≤ R₁ ∧
    15 * W₁ ≤ 64 * (W₁ - b₁) ∧ (∀ d, PassCut d R₁ a₁ b₁ W₁) ∧
    steps t (roundStart ms W) = some (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) ∧
    steps (T - t) (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) = none

/-- From a loop entry with `BigQ`, reached t steps after a clean tape of width W < W′ with T − k steps left: as
`FarQ.pass`, with R ≥ 769. -/
theorem BigQ.pass {ms : List Mark} {W W' T k t : Nat} (hlt : W < W')
    (ht : steps t (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms W')) (hq : BigQ ms W' (T - k - t)) :
    ∃ R a b W₁ t₁, W < W₁ ∧ W' ≤ W₁ ∧ 769 ≤ R ∧ 15 * W₁ ≤ 64 * (W₁ - b) ∧
      PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁ R ∧
      (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W₁ : Int) / 2, (R : Int) / 2] = true) ∧
      steps t₁ (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) ∧
      steps (T - k - t₁) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩] W₁) = none ∧
      ∃ u, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W₁ - R - 1⟩], W₁⟩ u ∧ u.wf ∧
        (EndClose u ∨ InteriorContact u) := by
  obtain ⟨R, ks, a₁, b₁, W₁, R₁, t', hch, hR, hsh, hcut, ht', hT₁⟩ := hq
  obtain ⟨hle, hP₁, u, hu, huw, hus⟩ := hch.last_halt hT₁
  refine ⟨R₁, a₁, b₁, W₁, t + t', by omega, hle, hR, hsh, hP₁, fun d => passCut_sym (by omega) (hcut d),
    steps_seq ht ht', ?_, u, hu, huw, hus⟩
  rw [show T - k - (t + t') = T - k - t - t' by omega]
  exact hT₁

/-! ## From blank tape -/

/-- **What a halt from blank tape needs: an open clean tape, then an open pass start with a right end of at least 769
and its middle wall far from the end.**  `blank_halt_open_far` with the clean-tape tree whose loop entries end big and
are far (`clean_tree_big_step`) and `entry_big_halt` at those entries: if the machine, started on blank tape, halts
after T steps, then it reaches a clean tape of even width W ≥ 2⁴¹ with W/2 in a cut class of
`cleanTreeG directWidth d` at every depth, and halts from there; and either W/2 is also in a cut class of
`cleanTreeGB directWidth d` at every depth, and the mark model reaches a stuck configuration from W, or the run from
W reaches a pass start wider than W with right end R ≥ 769, every gap at least 448 and 15W₁ ≤ 64(W₁ − b), that lies
in a cut leaf of `passTreeSym d` at every depth, halts from there, and the mark model reaches a stuck configuration
from there. -/
theorem blank_halt_open_big (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    ∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      (((∀ d, (cleanTreeGB directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
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
      (fun d W => (cleanTreeGB directWidth d).cutMem [(W : Int) / 2, 0] = true)
      (fun ms W => EntryNoClose ms W ∧ EntryBigEnd 769 ms W ∧ EntryFar ms W)
      (fun d W hW h => clean_tree_step_G directWidth d W (by decide) hW h)
      (fun d W hW h => clean_tree_big_step directWidth d W (by decide) hW h) BigQ
      (fun _ _ T' he hT' => entry_big_halt he.1 he.2.1 he.2.2 T' hT') (by decide) (by decide) hk₀ T hT
  · exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inl h⟩
  · obtain ⟨R, a, b, W₁, t₁, h1, -, h⟩ := BigQ.pass hlt ht hq
    exact ⟨W, k, hBW, hW, hG, hk, hTW, Or.inr ⟨R, a, b, W₁, t₁, h1, h⟩⟩

/-- **The open question, with a right end of at least 769.**  As `never_halts_of_far`, with the tree whose loop
entries end big and are far, and only the pass starts with R ≥ 769 and 15W₁ ≤ 64(W₁ − b) to rule out. -/
theorem never_halts_of_big
    (hC : ∀ W, directWidth ≤ W → W % 2 = 0 → (∀ d, (cleanTreeG directWidth d).cutMem [(W : Int) / 2, 0] = true) →
      (∀ d, (cleanTreeGB directWidth d).cutMem [(W : Int) / 2, 0] = true) →
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
    blank_halt_open_big T hT
  · exact hC W hBW hW hG hS _ hTW
  · exact hP W R a b W₁ t hBW hW hG hlt hR hsh hP₁ hcut ht _ hT₁

#print axioms LoopChain.big_end
#print axioms entry_big_halt
#print axioms blank_halt_open_big
#print axioms never_halts_of_big
