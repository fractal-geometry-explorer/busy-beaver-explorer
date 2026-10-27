import PassEntryHalt
import CleanSmallTheorem
open BB6 BB6.Sym

/-! # The run from blank tape reaches no small right end past the loop

`blank_halt_pass` (`thm/PassEntryHalt.lean`) leaves a halt from blank tape at a clean tape cut at every depth, or at
a pass start, reached through a loop entry and the loop's chain, that its pass-start tree cuts at every depth.  The
trees for the right ends R < 178 hold real halts (1/8 of the pass starts with R = 6, `pass_r6_halt`; every round the
model leaves uncovered in a sample of pass starts came for R in {4, 6, 8, 16, 32, 48, 64}).  This file shows that the
run from blank tape does not reach them: past a loop entry that passes the small-end check (`EntryNoSmall`,
`BB6/SmallEnd.lean`), the loop's chain ends at a right end R ≥ 178 (`LoopChain.small_end`).

* A full pass divides R by 16 and the left countdown L₁ by 64, so it keeps `NoSmallAt` (`noSmall_full`); a half pass
  is only ever the first step, and the entry check covers it.
* A round-7 break from a pass start of width E ≥ 2³⁷ lands with 32R′ ≥ S = 3E + 5R and 0 < 96L₁′ ≤ 385S
  (`break7_sigma`'s bounds), so R′³/L₁′² ≥ S/527,023 > 177³/9.  Full passes keep R³/L₁² (16³ = 64²), and at a right
  end r < 178 with |ℓ| ≥ 3 (ℓ ≡ 3 mod 7) it is r³/ℓ² ≤ 177³/9.  So no run of full passes after a round-7 break ends
  below 178 (`noSmall_sigma`, `break7_noSmall`).
* The last pass start of the chain has `NoSmallAt` with p = 0, so its right end is at least 178 (`noSmall_end`).

The clean-tape tree whose loop entries also pass the small-end check (`cleanTreeGS`, the proved explorer with the
entry test `cleanSmallOK`) leaves the same classes open as `cleanTreeGE` at 36 digits over the widths ≥ 2⁴¹: every one
of its 28,660 loop entries passes the check (`thm/CleanSmallMass.lean`).  With it, `blank_halt_small` is
`blank_halt_pass` with the pass start's right end at least 178, so its pass-start tree is the one for every R ≥ 178
(`passTreeSym`), whose cuts at the depths measured are all depth cuts, none at a round decided as a halt;
`blank_halt_small_kernel` is the same from 2²⁰ with nothing evaluated by compiled code (the plain clean-tape tree below
2³⁷, `cleanTreeGS 2³⁷` above). -/

/-! ## The chain's last right end -/

/-- A full pass keeps `NoSmallAt`: a run of full passes from its landing is one from its start, one pass longer. -/
theorem noSmall_full {R L R' L' : Int} (h : NoSmallAt R L) (hR : R = 16 * R') (hL : L = 64 * L') :
    NoSmallAt R' L' := by
  intro p r ℓ hr hR' hL' h7
  refine h (p + 1) r ℓ hr ?_ ?_ h7
  · rw [hR, hR', Int.pow_succ, Int.mul_comm ((16 : Int) ^ p) 16, Int.mul_assoc]
  · rw [hL, hL', Int.pow_succ, Int.mul_comm ((64 : Int) ^ p) 64, Int.mul_assoc]

/-- At a pass start with `NoSmallAt` the right end is at least 178 (no passes at all). -/
theorem noSmall_end {R : Nat} {L : Int} (h : NoSmallAt R L) (h7 : L % 7 = 3) : 178 ≤ R := by
  apply Nat.le_of_not_lt
  intro hlt
  exact h 0 R L hlt (by simp) (by simp) h7

/-- **R³/L₁² above 177³/9 keeps the small right ends out.**  After p full passes to a right end r < 178 with left
countdown ℓ ≡ 3 (mod 7), so |ℓ| ≥ 3, R³/L² = r³/ℓ² ≤ 177³/9. -/
theorem noSmall_sigma {R L : Int} (hσ : 177 ^ 3 * L ^ 2 < 9 * R ^ 3) : NoSmallAt R L := by
  intro p r ℓ hr hR hL h7
  have e1 : R ^ 3 = (4096 : Int) ^ p * (r : Int) ^ 3 := by
    rw [hR, Int.mul_pow, ← Int.pow_mul, Nat.mul_comm, Int.pow_mul]; rfl
  have e2 : L ^ 2 = (4096 : Int) ^ p * ℓ ^ 2 := by
    rw [hL, Int.mul_pow, ← Int.pow_mul, Nat.mul_comm, Int.pow_mul]; rfl
  have hX : (0 : Int) < 4096 ^ p := Int.pow_pos (by decide)
  have hℓ : 9 ≤ ℓ ^ 2 := by
    have hm : 3 ≤ ℓ.natAbs := by omega
    have h9 : 9 ≤ ℓ.natAbs * ℓ.natAbs := Nat.mul_le_mul hm hm
    have e : ℓ ^ 2 = ((ℓ.natAbs * ℓ.natAbs : Nat) : Int) := by rw [int_sq, Int.natCast_mul, Int.natAbs_mul_self']
    omega
  have hr3 : (r : Int) ^ 3 ≤ 5545233 := by
    have h1 : r ^ 3 ≤ 177 ^ 3 := Nat.pow_le_pow_left (show r ≤ 177 by omega) 3
    have h2 : (177 : Nat) ^ 3 = 5545233 := by decide
    have h3 : ((r ^ 3 : Nat) : Int) = (r : Int) ^ 3 := Int.natCast_pow r 3
    omega
  rw [e1, e2] at hσ
  have h1 : (4096 : Int) ^ p * (177 ^ 3 * ℓ ^ 2) < 4096 ^ p * (9 * (r : Int) ^ 3) := by
    rw [Int.mul_left_comm, Int.mul_left_comm (4096 ^ p)]; exact hσ
  have h2 := Int.lt_of_mul_lt_mul_left h1 (Int.le_of_lt hX)
  generalize ℓ ^ 2 = A at hℓ h2
  generalize (r : Int) ^ 3 = B at hr3 h2
  omega

/-- **A round-7 break from a pass start of width at least 2³⁷ lands above the small right ends**, for every run of
full passes after it: 32R′ ≥ S and 0 < 96L₁′ ≤ 385S with S = 3E + 5R ≥ 3·2³⁷, so 177³·L₁′² < 9·R′³. -/
theorem break7_noSmall {ms : List Mark} {E R : Nat} (hP : PassStart448 ms E R) {n W R' : Nat} {L' : Int}
    (hm : StepMap .break7 n E R (passL1 ms E) W R' L') (hE : 2 ^ 37 ≤ E) : NoSmallAt R' L' := by
  obtain ⟨a, b, rfl, -, -, -, -, -, h1, h2, h3⟩ := hP
  obtain ⟨-, hR', hL', -⟩ := hm
  have hL : passL1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E = 147 * (b : Int) - 112 * E + 392 * R - 186 := by
    show loopL1 b (E - R - 1) E = _
    unfold loopL1
    omega
  rw [hL] at hR' hL'
  obtain ⟨l, rfl⟩ : ∃ l : Nat, L' = l := ⟨L'.toNat, by omega⟩
  obtain ⟨S, hS⟩ : ∃ S, S = 3 * E + 5 * R := ⟨_, rfl⟩
  have hx : S ≤ 32 * R' := by omega
  have hy : 96 * l ≤ 385 * S := by omega
  have c1 : S ^ 3 ≤ 32768 * R' ^ 3 := by
    have := Nat.pow_le_pow_left hx 3
    rwa [Nat.mul_pow] at this
  have c2 : 9216 * l ^ 2 ≤ 148225 * S ^ 2 := by
    have := Nat.pow_le_pow_left hy 2
    rwa [Nat.mul_pow, Nat.mul_pow] at this
  have hE' : 137438953472 ≤ E := hE
  have hS' : 412316860416 ≤ S := by omega
  have m : S ^ 2 * 412316860416 ≤ S ^ 3 := by
    rw [Nat.pow_succ S 2]
    exact Nat.mul_le_mul_left _ hS'
  have hpos : 0 < S ^ 2 := Nat.pow_pos (Nat.lt_of_lt_of_le (by decide) hS')
  have key : 177 ^ 3 * l ^ 2 < 9 * R' ^ 3 := by
    generalize S ^ 3 = A at c1 m
    generalize S ^ 2 = B at c2 m hpos
    generalize R' ^ 3 = X at c1 ⊢
    generalize l ^ 2 = Y at c2 ⊢
    clear hR' hL' hx hy hS hS' h1 h2 h3 hE hE' hL
    omega
  apply noSmall_sigma
  have := (Int.ofNat_lt (n := 177 ^ 3 * l ^ 2) (m := 9 * R' ^ 3)).mpr key
  simp only [Int.natCast_mul, Int.natCast_pow] at this
  exact this

namespace LoopChain

/-- **The loop's chain from a wide start with `NoSmallAt` ends at a right end of at least 178.**  From a pass start of
width at least 2³⁷ from which no run of full passes ends below 178, nor one after a half pass (when W ≡ 2 mod 4),
every pass start of the chain after the first again has `NoSmallAt`: after a full pass by `noSmall_full`, after a half
pass by the hypothesis (a half pass is only ever the first step), after a round-7 break by `break7_noSmall`; so the
last one has R′ ≥ 178. -/
theorem small_end {ms : List Mark} {W R : Nat} {ks : List StepKind} {ms' : List Mark} {W' R' : Nat}
    (h : LoopChain ms W R ks ms' W' R') : 2 ^ 37 ≤ W → NoSmallAt R (passL1 ms W) →
    (W % 4 = 2 → ∀ R₁ L₁ : Int, 2 * R₁ = (R : Int) → 2 * L₁ = passL1 ms W + 35 * (W : Int) - 147 * (R : Int) - 60 →
      NoSmallAt R₁ L₁) → 178 ≤ R' := by
  induction h with
  | nil hP =>
    intro _ hs _
    obtain ⟨a, b, rfl, -⟩ := hP
    exact noSmall_end hs (loopL1_mod7 _ _ _)
  | cons k n kk hP _ _ _ hW4 hmap _ ih =>
    intro hW hs hh
    refine ih ?_ ?_ (fun h4 => absurd h4 (by omega))
    · cases k <;> simp only [StepMap] at hmap <;> omega
    · cases k with
      | full =>
        obtain ⟨-, h16, h64, -⟩ := hmap
        exact noSmall_full hs (by omega) h64.symm
      | half =>
        obtain ⟨-, h2, h2L, -, hE4⟩ := hmap
        exact hh hE4 _ _ (by omega) h2L
      | break7 => exact break7_noSmall hP hmap hW

end LoopChain

/-- **A halt from a loop entry that cannot close nor end small.**  As `entry_pass_halt`, and the chain's last pass
start, cut at every depth of its pass-start tree, has right end R₁ ≥ 178, so its tree is `passTreeSym`. -/
theorem entry_small_halt {ms : List Mark} {W : Nat} (hn : EntryNoClose ms W) (hs : EntryNoSmall ms W) (T : Nat)
    (hT : steps T (roundStart ms W) = none) :
    (∃ R ks a₁ b₁ W₁ R₁ t, LoopChain ms W R ks [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧ 178 ≤ R₁ ∧
      (∀ d, PassCut d R₁ a₁ b₁ W₁) ∧
      steps t (roundStart ms W) = some (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) ∧
      steps (T - t) (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) = none) ∨
    ∃ k W', 0 < k ∧ W < W' ∧ W' % 2 = 0 ∧
      steps k (roundStart ms W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧
      steps (T - k) (roundStart [⟨.M, W' - 2⟩] W') = none := by
  rcases entry_pass_halt hn T hT with ⟨R, ks, a₁, b₁, W₁, R₁, t, hch, hcut, ht, hT'⟩ | h
  · obtain ⟨a, b, hms, -, -, -, -, -, -, -, h3⟩ := hch.start
    obtain ⟨hs1, hs2⟩ := hs.2 R a b hms (by omega)
    exact Or.inl ⟨R, ks, a₁, b₁, W₁, R₁, t, hch, hch.small_end hs.1 hs1 hs2, hcut, ht, hT'⟩
  · exact Or.inr h

/-! ## From blank tape -/

/-- `clean_entry_chain` (`thm/CleanEntryHalt.lean`) for any property `Ent` of the loop entries in place of
`EntryNoClose`: the chain over clean tapes by strong induction on the halting time, with the step at each width ≥ B
and what a halt from an entry needs as hypotheses. -/
theorem clean_entry_chain_of (A B : Nat) (h6 : 6 ≤ A) (hB : StepsBelow A B)
    (Cut : Nat → Nat → Prop) (Ent : List Mark → Nat → Prop)
    (hStep : ∀ d W, W % 2 = 0 → B ≤ W →
      ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
        steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
        (Cut d W ∨ (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W') ∨ (Ent ms' W' ∧ W < W')))
    (Q : List Mark → Nat → Nat → Prop)
    (hQ : ∀ ms W T, Ent ms W → steps T (roundStart ms W) = none →
      Q ms W T ∨ ∃ k W', 0 < k ∧ W < W' ∧ W' % 2 = 0 ∧
        steps k (roundStart ms W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧
        steps (T - k) (roundStart [⟨.M, W' - 2⟩] W') = none)
    (T : Nat) : ∀ W, W % 2 = 0 → A ≤ W → steps T (roundStart [⟨.M, W - 2⟩] W) = none →
      (∃ W' k, W ≤ W' ∧ B ≤ W' ∧ W' % 2 = 0 ∧ (∀ d, Cut d W') ∧
        steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart [⟨.M, W' - 2⟩] W') ∧
        steps (T - k) (roundStart [⟨.M, W' - 2⟩] W') = none) ∨
      ∃ ms' W' k, W < W' ∧ B < W' ∧ Ent ms' W' ∧
        steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧ Q ms' W' (T - k) := by
  induction T using Nat.strongRecOn with
  | ind T ih =>
    intro W hW hA hT
    have hG6 : 6 ≤ W := by omega
    by_cases hstop : B ≤ W ∧ ∀ d, Cut d W
    · exact Or.inl ⟨W, 0, Nat.le_refl _, hstop.1, hW, hstop.2, rfl, by simpa using hT⟩
    suffices hnext : (∃ ms' W' k, W < W' ∧ B < W' ∧ Ent ms' W' ∧
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

/-- **A halt from blank tape, after a prefix, past the loop's end, at a right end of at least 178.**  As
`blank_halt_pass_from`, with a clean-tape tree whose loop entries also satisfy `EntryNoSmall`: the pass start a halt
needs has right end R ≥ 178. -/
theorem blank_halt_small_from (A B W₀ k₀ : Nat) (h6 : 6 ≤ A) (hB : StepsBelow A B)
    (Cut : Nat → Nat → Prop)
    (hStep : ∀ d W, W % 2 = 0 → B ≤ W →
      ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
        steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
        (Cut d W ∨ (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W') ∨
          ((EntryNoClose ms' W' ∧ EntryNoSmall ms' W') ∧ W < W')))
    (hW₀ : W₀ % 2 = 0) (hAW₀ : A ≤ W₀) (hk₀ : steps k₀ ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W₀ - 2⟩] W₀))
    (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    (∃ W k, B ≤ W ∧ W % 2 = 0 ∧ (∀ d, Cut d W) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
    ∃ R a b W k, B < W ∧ 2 ^ 37 ≤ W ∧ 178 ≤ R ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ∧
      (∀ d, PassCut d R a b W) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) ∧
      steps (T - k) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t) := by
  obtain ⟨-, hT₀⟩ := steps_none_split hT hk₀
  rcases clean_entry_chain_of A B h6 hB Cut (fun ms W => EntryNoClose ms W ∧ EntryNoSmall ms W) hStep
      (fun ms W T' => ∃ R ks a₁ b₁ W₁ R₁ t, LoopChain ms W R ks [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁ R₁ ∧
        178 ≤ R₁ ∧ (∀ d, PassCut d R₁ a₁ b₁ W₁) ∧
        steps t (roundStart ms W) = some (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) ∧
        steps (T' - t) (roundStart [⟨.W, a₁⟩, ⟨.W, b₁⟩, ⟨.W, W₁ - R₁ - 1⟩] W₁) = none)
      (fun _ _ T' he hT' => entry_small_halt he.1 he.2 T' hT') (T - k₀) W₀ hW₀ hAW₀ hT₀ with
      ⟨W, k, hle, hBW, hW, hcut, hk, hTW⟩ | ⟨ms, W, k, -, hBW, he, hk, R, ks, a₁, b₁, W₁, R₁, t, hch, hR, hcut, ht, hT₁⟩
  · have hG6 : 6 ≤ W := by omega
    obtain ⟨u, hu, huw, hus⟩ := round_halt_needs_contact [⟨.M, W - 2⟩] W _ (roundWF_one.mpr ⟨hG6, hW⟩)
      (noG_one _) hTW
    refine Or.inl ⟨W, k₀ + k, hBW, hW, hcut, steps_seq hk₀ hk, ?_, u, hu, huw, stuck_cases hus⟩
    rw [show T - (k₀ + k) = T - k₀ - k by omega]
    exact hTW
  · -- the chain only widens, from the entry's width W ≥ 2³⁷
    have hW₁ := hch.width
    have h37 : 2 ^ 37 ≤ W₁ := Nat.le_trans he.2.1 (by omega)
    have hP₁ := hch.last
    obtain ⟨hwf, hG⟩ := hP₁.wf
    obtain ⟨u, hu, huw, hus⟩ := round_halt_needs_contact _ W₁ _ hwf hG hT₁
    refine Or.inr ⟨R₁, a₁, b₁, W₁, k₀ + k + t, by omega, h37, hR, hP₁, hcut, steps_seq (steps_seq hk₀ hk) ht, ?_,
      u, hu, huw, stuck_cases hus⟩
    rw [show T - (k₀ + k + t) = T - k₀ - k - t by omega]
    exact hT₁

/-- At a right end of at least 178, `PassCut` is the cut of the tree for every R ≥ 178. -/
theorem passCut_sym {d R a b W : Nat} (hR : 178 ≤ R) (h : PassCut d R a b W) :
    (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2, (R : Int) / 2] = true := by
  simpa only [PassCut, show ¬ R < 178 by omega, ↓reduceIte] using h

/-- **What a halt from blank tape needs: no small right end past the loop.**  `blank_halt_small_from` with the prefix
to 2³² (`blank_prefix`), the clean tapes of width in [2³², 2⁴¹) run one by one (`stepsBelow_direct`) and the clean-tape
tree with the small-end check over the widths ≥ 2⁴¹ (`clean_tree_small_step`): if the machine, started on blank tape,
halts after T steps, then either it reaches a clean tape of even width W ≥ 2⁴¹ with W/2 in a cut class of
`cleanTreeGS directWidth d` at every depth, or a pass start of width W > 2⁴¹ with right end R ≥ 178 and every gap at
least 448 that lies in a cut leaf of the pass-start tree for every R ≥ 178 (`passTreeSym`) at every depth; it halts
from there, and the mark model reaches a stuck configuration from there. -/
theorem blank_halt_small (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    (∃ W k, directWidth ≤ W ∧ W % 2 = 0 ∧ (∀ d, (cleanTreeGS directWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
    ∃ R a b W k, directWidth < W ∧ 178 ≤ R ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ∧
      (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2, (R : Int) / 2] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) ∧
      steps (T - k) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t) := by
  obtain ⟨k₀, hk₀⟩ := blank_prefix
  rcases blank_halt_small_from cleanGamma directWidth prefixWidth k₀ (by decide) stepsBelow_direct
      (fun d W => (cleanTreeGS directWidth d).cutMem [(W : Int) / 2, 0] = true)
      (fun d W hW h => clean_tree_small_step directWidth d W (by decide) hW h) (by decide) (by decide) hk₀ T hT with
      h | ⟨R, a, b, W, k, hlt, -, hR, hP, hcut, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨R, a, b, W, k, hlt, hR, hP, fun d => passCut_sym hR (hcut d), h⟩

/-- **The kernel's step, with the small-end check.**  For every clean tape of even width W ≥ 2²⁰ and every depth d,
with the plain clean-tape tree over the widths ≥ 2²⁰ if W < 2³⁷ (`clean_tree_step_G`) and the tree with the small-end
check over the widths ≥ 2³⁷ if not (`clean_tree_small_step`): W/2 is in a cut class of that tree, or the run reaches
a wider clean tape after at least one round, or a wider loop entry that cannot close nor end small. -/
theorem clean_small_step_kernel (d W : Nat) (hW : W % 2 = 0) (h : kernelPrefixWidth ≤ W) :
    ∃ n k ms' W', roundsZ 1000 n [⟨.M, W - 2⟩] W = .newRound ms' W' ∧
      steps k (roundStart [⟨.M, W - 2⟩] W) = some (roundStart ms' W') ∧
      (((W < 2 ^ 37 → (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
          (2 ^ 37 ≤ W → (cleanTreeGS (2 ^ 37) d).cutMem [(W : Int) / 2, 0] = true)) ∨
        (0 < n ∧ ms' = [⟨.M, W' - 2⟩] ∧ W < W') ∨ ((EntryNoClose ms' W' ∧ EntryNoSmall ms' W') ∧ W < W')) := by
  by_cases hl : W < 2 ^ 37
  · obtain ⟨n, k, ms', W', hr, hk, hc⟩ := clean_tree_step_G kernelPrefixWidth d W (by decide) hW h
    refine ⟨n, k, ms', W', hr, hk, ?_⟩
    rcases hc with hc | hc
    · exact Or.inl ⟨fun _ => hc, fun h' => absurd h' (Nat.not_le.mpr hl)⟩
    · exact Or.inr (Or.inl hc)
  · obtain ⟨n, k, ms', W', hr, hk, hc⟩ := clean_tree_small_step (2 ^ 37) d W (by decide) hW (Nat.le_of_not_lt hl)
    refine ⟨n, k, ms', W', hr, hk, ?_⟩
    rcases hc with hc | hc | hc
    · exact Or.inl ⟨fun h' => absurd h' hl, fun _ => hc⟩
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr hc)

/-- **The same, checked by the kernel alone.**  `blank_halt_small_from` from the kernel's prefix to 2²⁰
(`blank_prefix_kernel`) with `clean_small_step_kernel`: if the machine, started on blank tape, halts after T steps,
then either it reaches a clean tape of even width W ≥ 2²⁰ that is cut at every depth, by `cleanTreeG 2²⁰ d` if
W < 2³⁷ and by `cleanTreeGS 2³⁷ d` if not, or a pass start of width W ≥ 2³⁷ with right end R ≥ 178 and every gap at
least 448 that lies in a cut leaf of `passTreeSym d` at every depth; it halts from there, and the mark model reaches a
stuck configuration from there.  Nothing here is evaluated by compiled code. -/
theorem blank_halt_small_kernel (T : Nat) (hT : steps T ⟨blank, blank, .A⟩ = none) :
    (∃ W k, kernelPrefixWidth ≤ W ∧ W % 2 = 0 ∧
      (W < 2 ^ 37 → ∀ d, (cleanTreeG kernelPrefixWidth d).cutMem [(W : Int) / 2, 0] = true) ∧
      (2 ^ 37 ≤ W → ∀ d, (cleanTreeGS (2 ^ 37) d).cutMem [(W : Int) / 2, 0] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.M, W - 2⟩] W) ∧
      steps (T - k) (roundStart [⟨.M, W - 2⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.M, W - 2⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
    ∃ R a b W k, 2 ^ 37 ≤ W ∧ 178 ≤ R ∧ PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ∧
      (∀ d, (passTreeSym d).cutMem [((a : Int) - 1) / 2, (b : Int) / 2, (W : Int) / 2, (R : Int) / 2] = true) ∧
      steps k ⟨blank, blank, .A⟩ = some (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) ∧
      steps (T - k) (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none ∧
      ∃ t, Reach ⟨[], 1, [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩], W⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t) := by
  obtain ⟨k₀, hk₀⟩ := blank_prefix_kernel
  rcases blank_halt_small_from kernelPrefixWidth kernelPrefixWidth kernelPrefixWidth k₀ (by decide)
      (stepsBelow_self _) _ clean_small_step_kernel (by decide) (Nat.le_refl _) hk₀ T hT with
      ⟨W, k, h1, h2, hcut, h3⟩ | ⟨R, a, b, W, k, -, h37, hR, hP, hcut, h⟩
  · exact Or.inl ⟨W, k, h1, h2, fun hl d => (hcut d).1 hl, fun hl d => (hcut d).2 hl, h3⟩
  · exact Or.inr ⟨R, a, b, W, k, h37, hR, hP, fun d => passCut_sym hR (hcut d), h⟩

#print axioms LoopChain.small_end
#print axioms entry_small_halt
#print axioms blank_halt_small
#print axioms blank_halt_small_kernel
