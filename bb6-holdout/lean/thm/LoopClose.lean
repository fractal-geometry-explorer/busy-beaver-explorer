import LoopHalt
import EndgameCloseTheorem

/-!
# The loop's chain with end meetings at distance 2 passed

`loop_chain_halt` (`LoopHalt.lean`) ends the loop's chain at a closing class of `closeClass` or at a `LoopEnd`
reached close-free (every end meeting at distance at least 3).  The endgame trees behind it stop at every end meeting
at a constant distance ≤ 2.  An end meeting at distance 2 is not a close: the chain puts the next one at 0, and when it
is anywhere else, the run has left the halving chain.  `endgame_stretch_close` (`EndgameCloseTheorem.lean`) passes these
meetings.  Its closes need the classes of `closeClassC`: L₁ even for R = 2 and 4, L₁ ≡ 0 mod 32 for R = 8, mod 64 for
R = 16 and mod 128 for R = 32 and 48, and no close from R = 24, 64 or 176.  Its other stretches end at an end event
with every end meeting at distance at least 3, or, with every end meeting at distance at least 2, where the run has
left phase 0 or the halving chain at a round start that is not three walls (`EndEventC`).  Such a stretch is never a
step of the chain, which only goes on from a landing.

So `loop_chain_halt_close` is `loop_chain_halt` with the chain's closing classes narrowed to `InCloseClassC`, and the
end meetings of its last stretch at distance at least 2 instead of 3.  Each class of `closeClassC` lies in the class
of `closeClass` (`InCloseClassC.closeClass`).  With L₁ ≡ 3 (mod 7) the narrower classes give R³/L₁² ≤ 4 at a close
instead of 176³/256² (`sigma_closeC`): log₂W ≤ σ + 2 at the start of the chain's last run of full passes
(`LoopChain.sigmaC`, `loop_halt_sigma_close`).  At a round-7 landing that bound needs a width below 2²⁰
(`break7_sigmaC`), so from a pass start of width at least 2²⁰ a close through the loop is p full passes after at most
one half pass (`LoopChain.close_wideC`, `loop_halt_wide_close`, `loop_halt_leaves_close`).
-/

open BB6 BB6.Sym

/-- At the pass start, R is in the closing set of `closeClassC` (2, 4, 8, 16, 32 and 48) and the left countdown L₁ is
in R's class. -/
def InCloseClassC (ms : List Mark) (W R : Nat) : Prop :=
  ∃ a b m c, ms = [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] ∧ closeClassC R = some (m, c) ∧ loopL1 b (W - R - 1) W % m = c

/-- Each class of `closeClassC` lies in R's class of `closeClass`. -/
theorem InCloseClassC.closeClass {ms : List Mark} {W R : Nat} (h : InCloseClassC ms W R) : InCloseClass ms W R := by
  obtain ⟨a, b, m, c, rfl, hc, hl⟩ := h
  obtain ⟨m', c', hc', hl'⟩ := closeClassC_sub hc hl
  exact ⟨a, b, m', c', rfl, hc', hl'⟩

/-- The right ends of `InCloseClassC`: 2, 4, 8, 16, 32 and 48. -/
theorem InCloseClassC.closing {ms : List Mark} {W R : Nat} (h : InCloseClassC ms W R) :
    R = 2 ∨ R = 4 ∨ R = 8 ∨ R = 16 ∨ R = 32 ∨ R = 48 := by
  obtain ⟨-, -, m, c, -, hc, -⟩ := h
  exact closeClassC_closing hc

/-- **One step of the loop's chain, with end meetings at distance 2 passed.**  From every phase-0 pass start with
right end R and every gap at least 448, either R is in the closing set of `closeClassC` and the left countdown is in
R's class, or the machine runs n rounds without halting to the round start that `roundsZ` computes, where the stretch
ends at an end event with every end meeting at distance at least 3, or, with every end meeting at distance at least 2,
where the run has left phase 0 or the halving chain at a round start that is not three walls (`EndEventC`). -/
theorem loop_step_close (R : Nat) (ms : List Mark) (W : Nat) (hP : PassStart448 ms W R) :
    InCloseClassC ms W R ∨
    ∃ n kk ms' W', steps kk (roundStart ms W) = some (roundStart ms' W') ∧
      roundsZ 1000 n ms W = .newRound ms' W' ∧ EndEventC W R (passL1 ms W) n (meetsRounds 1000 n ms W) ms' W' := by
  obtain ⟨a, b, rfl, ha, hb, hW, hR, hR2, h1, h2, h3⟩ := hP
  rcases endgame_stretch_close R hR hR2 a b W ha hb hW h1 h2 h3 with ⟨m, c, hc, hl⟩ | h
  · exact Or.inl ⟨a, b, m, c, rfl, hc, hl⟩
  · exact Or.inr h

/-! ## The σ bound with the classes of `closeClassC` -/

/-- R³/L² ≤ 4, the value at a close from R = 4 with |L₁| = 4.  At a pass start of width W with right end R and left
countdown L, with s = log₂(W/R), λ = log₂(|L|/W) and σ = 3s + 2λ, this is log₂W ≤ σ + 2. -/
def SigmaOKC (R : Nat) (L : Int) : Prop := (R : Int) ^ 3 ≤ 4 * L ^ 2

/-- **The classes of `closeClassC` keep R³/L₁² ≤ 4.**  With L₁ ≡ 3 (mod 7) (`loopL1_mod7`), the class of each R bounds
|L₁| from below: by 4 for R = 2 and 4 (L₁ ≡ 10 mod 14), 32 for 8 (L₁ ≡ 192 mod 224), 192 for 16 (L₁ ≡ 192 mod 448)
and 256 for 32 and 48 (L₁ ≡ 640 mod 896); R³/L₁² is largest, 4, at R = 4. -/
theorem sigma_closeC {ms : List Mark} {W R : Nat} (h : InCloseClassC ms W R) : SigmaOKC R (passL1 ms W) := by
  obtain ⟨a, b, m, c, rfl, hc, hl⟩ := h
  have h7 := loopL1_mod7 b (W - R - 1) W
  show SigmaOKC R (loopL1 b (W - R - 1) W)
  generalize loopL1 b (W - R - 1) W = L at hl h7 ⊢
  unfold SigmaOKC
  rcases closeClassC_closing hc with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show closeClassC 2 = some (2, 0) from rfl] at hc; cases hc
    have := sq_ge (L := L) (k := 4) (by omega); omega
  · rw [show closeClassC 4 = some (2, 0) from rfl] at hc; cases hc
    have := sq_ge (L := L) (k := 4) (by omega); omega
  · rw [show closeClassC 8 = some (32, 0) from rfl] at hc; cases hc
    have := sq_ge (L := L) (k := 32) (by omega); omega
  · rw [show closeClassC 16 = some (64, 0) from rfl] at hc; cases hc
    have := sq_ge (L := L) (k := 192) (by omega); omega
  · rw [show closeClassC 32 = some (128, 0) from rfl] at hc; cases hc
    have := sq_ge (L := L) (k := 256) (by omega); omega
  · rw [show closeClassC 48 = some (128, 0) from rfl] at hc; cases hc
    have := sq_ge (L := L) (k := 256) (by omega); omega

/-- A full pass divides R³ and L₁² by the same factor, 16³ = 64² = 4096. -/
theorem sigma_passC (R : Nat) (L : Int) (h : SigmaOKC R L) : SigmaOKC (16 * R) (64 * L) := by
  unfold SigmaOKC at *
  have e1 : ((16 * R : Nat) : Int) ^ 3 = 4096 * (R : Int) ^ 3 := by rw [Int.natCast_mul, Int.mul_pow]; rfl
  have e2 : (64 * L) ^ 2 = 4096 * L ^ 2 := by rw [Int.mul_pow]; rfl
  rw [e1, e2]
  omega

theorem sigma_passesC (p R : Nat) (L : Int) (h : SigmaOKC R L) : SigmaOKC (16 ^ p * R) (64 ^ p * L) := by
  induction p with
  | zero => simpa using h
  | succ p ih =>
    have := sigma_passC _ _ ih
    rwa [Nat.pow_succ, Int.pow_succ, Nat.mul_comm (16 ^ p) 16, Nat.mul_assoc, Int.mul_comm ((64 : Int) ^ p) 64,
      Int.mul_assoc]

/-- **σ at a round-7 landing, with the classes of `closeClassC`.**  As in `break7_sigma`, a round-7 break from a pass
start of width E with right end R and every gap at least 448 lands with 32 R′ ≥ S and 0 < 96 L₁′ ≤ 385 S, where
S = 3E + 5R.  So R′³/L₁′² ≤ 4 there needs 9216 S ≤ 4 · 32768 · 385², that is S ≤ 2,108,088: E < 2²⁰
(E ≤ 702,696). -/
theorem break7_sigmaC {ms : List Mark} {E R : Nat} (hP : PassStart448 ms E R) {n W R' : Nat} {L' : Int}
    (hm : StepMap .break7 n E R (passL1 ms E) W R' L') (hσ : SigmaOKC R' L') : E < 2 ^ 20 := by
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
  have c3 : R' ^ 3 ≤ 4 * l ^ 2 := by
    unfold SigmaOKC at hσ
    have e : ((R' ^ 3 : Nat) : Int) ≤ ((4 * l ^ 2 : Nat) : Int) := by
      rw [Int.natCast_mul, Int.natCast_pow, Int.natCast_pow]
      exact hσ
    exact Int.ofNat_le.mp e
  apply Nat.lt_of_not_le
  intro hE
  have hE' : 1048576 ≤ E := hE
  have hS' : 3145728 ≤ S := by omega
  have m : S ^ 2 * 3145728 ≤ S ^ 3 := by
    rw [Nat.pow_succ S 2]
    exact Nat.mul_le_mul_left _ hS'
  have hpos : 0 < S ^ 2 := Nat.pow_pos (Nat.lt_of_lt_of_le (by decide) hS')
  generalize S ^ 3 = A at c1 m
  generalize S ^ 2 = B at c2 m hpos
  generalize R' ^ 3 = X at c1 c3
  generalize l ^ 2 = Y at c2 c3
  clear hσ hR' hL' hx hy hS hS' h1 h2 h3 hE hE'
  omega

namespace LoopChain

variable {ms : List Mark} {W R : Nat} {ks : List StepKind} {ms' : List Mark} {W' R' : Nat}

/-- σ through a run of full passes: R³/L₁² is the same at every pass start of the run. -/
theorem sigma_fullsC (p : Nat) (h : LoopChain ms W R (List.replicate p .full) ms' W' R')
    (hσ : SigmaOKC R' (passL1 ms' W')) : SigmaOKC R (passL1 ms W) := by
  obtain ⟨hR, hL⟩ := fulls p h
  rw [hR, hL]
  exact sigma_passesC p _ _ hσ

/-- **σ through the chain, with the classes of `closeClassC`.**  A chain that ends in a class of `closeClassC` is a
chain `ks₁` that does not end with a full pass, to a pass start with R³/L₁² ≤ 4 (`SigmaOKC`: log₂W ≤ σ + 2 there),
followed by p full passes. -/
theorem sigmaC (h : LoopChain ms W R ks ms' W' R') (hc : InCloseClassC ms' W' R') :
    ∃ ks₁ p ms₁ W₁ R₁, ks = ks₁ ++ List.replicate p .full ∧ (ks₁ = [] ∨ ∃ ks₀ k, ks₁ = ks₀ ++ [k] ∧ k ≠ .full) ∧
      LoopChain ms W R ks₁ ms₁ W₁ R₁ ∧ LoopChain ms₁ W₁ R₁ (List.replicate p .full) ms' W' R' ∧
      SigmaOKC R₁ (passL1 ms₁ W₁) := by
  obtain ⟨ks₁, p, rfl, hl⟩ := split_fulls ks
  obtain ⟨ms₁, W₁, R₁, h₁, h₂⟩ := split ks₁ h
  exact ⟨ks₁, p, ms₁, W₁, R₁, rfl, hl, h₁, h₂, sigma_fullsC p h₂ (sigma_closeC hc)⟩

/-- A chain of full passes only that ends in a class of `closeClassC` has R³/L₁² ≤ 4 at its start. -/
theorem sigma_all_fullC (h : LoopChain ms W R ks ms' W' R') (hc : InCloseClassC ms' W' R')
    (hf : ∀ k ∈ ks, k = .full) : SigmaOKC R (passL1 ms W) := by
  have e : ks = List.replicate ks.length .full := List.eq_replicate_iff.mpr ⟨rfl, hf⟩
  rw [e] at h
  exact sigma_fullsC _ h (sigma_closeC hc)

/-- **From a pass start of width at least 2²⁰, a close of `closeClassC` makes no round-7 break.**  `close_wide` with
the classes of `closeClassC`, from width 2²⁰ instead of 2²⁴ (`break7_sigmaC`): the chain to the close is p full passes,
with R = 16^p R′ and L₁ = 64^p L₁′, or a half pass (from W ≡ 2 mod 4) and then p full passes, with R = 2 · 16^p R′ and
2 · 64^p L₁′ = L₁ + 35 W − 147 R − 60. -/
theorem close_wideC (h : LoopChain ms W R ks ms' W' R') (hc : InCloseClassC ms' W' R') (hW : 2 ^ 20 ≤ W) :
    ∃ p, (ks = List.replicate p .full ∧ R = 16 ^ p * R' ∧ passL1 ms W = 64 ^ p * passL1 ms' W') ∨
      (ks = .half :: List.replicate p .full ∧ W % 4 = 2 ∧ R = 2 * 16 ^ p * R' ∧
        2 * 64 ^ p * passL1 ms' W' = passL1 ms W + 35 * (W : Int) - 147 * (R : Int) - 60) := by
  obtain ⟨ks₁, p, ms₁, W₁, R₁, rfl, hl, h₁, h₂, hσ⟩ := h.sigmaC hc
  obtain ⟨hR, hL⟩ := fulls p h₂
  rcases hl with rfl | ⟨ks₀, k, rfl, hk⟩
  · obtain ⟨rfl, rfl, rfl⟩ := nil_eq h₁
    exact ⟨p, Or.inl ⟨rfl, hR, hL⟩⟩
  · obtain ⟨ms₀, W₀, R₀, h₀, hk₁⟩ := split ks₀ h₁
    have hW₀ : W ≤ W₀ := by have := h₀.width; omega
    cases hk₁ with
    | cons _ n kk hP₀ _ _ _ _ hmap tl =>
      obtain ⟨rfl, rfl, rfl⟩ := nil_eq tl
      cases k with
      | full => exact absurd rfl hk
      | break7 => exact absurd (break7_sigmaC hP₀ hmap hσ) (by omega)
      | half =>
        -- a half pass is only the first step: ks₀ = []
        cases ks₀ with
        | cons k₀ ks₀ =>
          have := (h₀.append (.cons .half n kk hP₀ ‹_› ‹_› ‹_› ‹_› hmap tl)).half_first
          exact absurd (List.mem_append_right ks₀ (List.mem_singleton_self StepKind.half)) this
        | nil =>
          obtain ⟨rfl, rfl, rfl⟩ := nil_eq h₀
          obtain ⟨-, h2, h2L, -, hW4⟩ := hmap
          refine ⟨p, Or.inr ⟨rfl, hW4, ?_, ?_⟩⟩
          · rw [← h2, hR, Nat.mul_assoc]
          · rw [Int.mul_assoc, ← hL, h2L]

end LoopChain

namespace BB6

/-- **A halt from a pass start: the loop's chain, with end meetings at distance 2 passed.**  If the machine halts T
steps after a phase-0 pass start with right end R and every gap at least 448, then its run from there follows the
loop's chain (`LoopChain`), as in `loop_chain_halt`, up to its last pass start `ms₁ W₁` with right end R₁.  From there,
either R₁ is 2, 4, 8, 16, 32 or 48 and the left countdown is in R₁'s class of `closeClassC` (`InCloseClassC`), and the
mark model, run on from `ms₁ W₁`, reaches a stuck configuration; or the model covers a further stretch, with every end
meeting at distance at least 2, to where the chain ends (`LoopEnd`), and reaches a stuck configuration from there: a
close at the right end or an interior contact. -/
theorem loop_chain_halt_close (T : Nat) : ∀ (R : Nat) (ms : List Mark) (W : Nat), PassStart448 ms W R →
    steps T (roundStart ms W) = none →
    ∃ ks ms₁ W₁ R₁, LoopChain ms W R ks ms₁ W₁ R₁ ∧
      ((InCloseClassC ms₁ W₁ R₁ ∧ ∃ t, Reach ⟨[], 1, ms₁, W₁⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
        ∃ n ms' W', roundsZ 1000 n ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n ms₁ W₁, 2 ≤ d) ∧
          LoopEnd W₁ R₁ (passL1 ms₁ W₁) n (meetsRounds 1000 n ms₁ W₁) ms' W' ∧
          ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) := by
  induction T using Nat.strongRecOn with
  | ind T ih =>
    intro R ms W hP hT
    obtain ⟨hwf, hG⟩ := hP.wf
    rcases loop_step_close R ms W hP with hc | ⟨n, kk, ms', W', hk, hr, hev⟩
    · obtain ⟨t, ht, htw, hts⟩ := round_halt_needs_contact ms W T hwf hG hT
      exact ⟨[], ms, W, R, .nil hP, Or.inl ⟨hc, t, ht, htw, stuck_cases hts⟩⟩
    · obtain ⟨k, hkT, hk', hT', -, t, ht, htw, hts⟩ := halt_after_rounds 1000 n ms W ms' W' hwf hG hr T hT
      by_cases hc : ∃ R', PassStart448 ms' W' R'
      · -- the stretch ends at a pass start with every gap at least 448: a landing, reached close-free; follow the
        -- chain on from it
        obtain ⟨R', hP'⟩ := hc
        have hl : (∀ d ∈ meetsRounds 1000 n ms W, 3 ≤ d) ∧ Landing n W R (passL1 ms W) ms' W' := by
          rcases hev with ⟨hm, ⟨-, hn⟩ | hl⟩ | ⟨-, -, hn⟩
          · exact absurd hn (PassStart448.www hP')
          · exact ⟨hm, hl⟩
          · exact absurd hn (PassStart448.www hP')
        obtain ⟨hm, hl⟩ := hl
        obtain ⟨hW4, kind, hmap⟩ := landing_passStart hl hP'
        -- the step takes at least one machine step: the width grows
        have hlt : W < W' := by cases kind <;> simp only [StepMap] at hmap <;> omega
        have hk1 : 0 < k := by
          rcases Nat.eq_zero_or_pos k with rfl | h0
          · simp only [steps, Option.some.injEq] at hk'
            exact absurd hk' (passStart_ne hP hP' hlt)
          · exact h0
        obtain ⟨ks, ms₁, W₁, R₁, hch, hend⟩ := ih (T - k) (by omega) R' ms' W' hP' hT'
        exact ⟨kind :: ks, ms₁, W₁, R₁, .cons kind n kk hP hk hr hm hW4 hmap hch, hend⟩
      · exact ⟨[], ms, W, R, .nil hP, Or.inr ⟨n, ms', W', hr, hev.ge2, ⟨hev.endEvent, hc⟩, t, ht, htw,
          stuck_cases hts⟩⟩

/-- **The σ bound, with end meetings at distance 2 passed.**  If the machine halts from a phase-0 pass start with right
end R, every gap at least 448 and R³/L₁² > 4 (log₂W > σ + 2), then it does not close through full passes alone: the
loop's chain from there (`loop_chain_halt_close`) either makes a half pass or a round-7 break before it reaches a class
of `closeClassC`, or it ends (`LoopEnd`) and the halt needs a stuck configuration after that. -/
theorem loop_halt_sigma_close (R : Nat) (ms : List Mark) (W : Nat) (hP : PassStart448 ms W R)
    (hσ : ¬ SigmaOKC R (passL1 ms W)) (T : Nat) (hT : steps T (roundStart ms W) = none) :
    ∃ ks ms₁ W₁ R₁, LoopChain ms W R ks ms₁ W₁ R₁ ∧
      ((InCloseClassC ms₁ W₁ R₁ ∧ (StepKind.half ∈ ks ∨ StepKind.break7 ∈ ks) ∧
          ∃ t, Reach ⟨[], 1, ms₁, W₁⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
        ∃ n ms' W', roundsZ 1000 n ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n ms₁ W₁, 2 ≤ d) ∧
          LoopEnd W₁ R₁ (passL1 ms₁ W₁) n (meetsRounds 1000 n ms₁ W₁) ms' W' ∧
          ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) := by
  obtain ⟨ks, ms₁, W₁, R₁, hch, ⟨hc, ht⟩ | he⟩ := loop_chain_halt_close T R ms W hP hT
  · refine ⟨ks, ms₁, W₁, R₁, hch, Or.inl ⟨hc, ?_, ht⟩⟩
    apply Classical.byContradiction
    intro hn
    apply hσ
    refine hch.sigma_all_fullC hc fun k hk => ?_
    cases k with
    | full => rfl
    | half => exact absurd (Or.inl hk) hn
    | break7 => exact absurd (Or.inr hk) hn
  · exact ⟨ks, ms₁, W₁, R₁, hch, Or.inr he⟩

/-- **From a wide pass start, a close through the loop makes no round-7 break; with end meetings at distance 2
passed.**  `loop_halt_wide` with the closing classes of `closeClassC` (`InCloseClassC`), from width 2²⁰ instead of
2²⁴ (`LoopChain.close_wideC`), and with the end meetings of the chain's last stretch at distance at least 2: if the
machine halts from a phase-0 pass start of width W ≥ 2²⁰ with right end R and every gap at least 448, then the loop's
chain from there either reaches a class of `closeClassC` at
`ms₁ W₁` (right end R₁) through p full passes, with R = 16^p R₁ and L₁ = 64^p L₁′, or through a half pass (from
W ≡ 2 mod 4) and then p full passes, with R = 2 · 16^p R₁ and 2 · 64^p L₁′ = L₁ + 35 W − 147 R − 60, and the mark
model, run on from `ms₁ W₁`, reaches a stuck configuration; or it ends (`LoopEnd`) and the halt needs a stuck
configuration after that. -/
theorem loop_halt_wide_close (R : Nat) (ms : List Mark) (W : Nat) (hP : PassStart448 ms W R) (hW : 2 ^ 20 ≤ W)
    (T : Nat) (hT : steps T (roundStart ms W) = none) :
    ∃ ks ms₁ W₁ R₁, LoopChain ms W R ks ms₁ W₁ R₁ ∧
      ((InCloseClassC ms₁ W₁ R₁ ∧
          (∃ p, (ks = List.replicate p .full ∧ R = 16 ^ p * R₁ ∧ passL1 ms W = 64 ^ p * passL1 ms₁ W₁) ∨
            (ks = .half :: List.replicate p .full ∧ W % 4 = 2 ∧ R = 2 * 16 ^ p * R₁ ∧
              2 * 64 ^ p * passL1 ms₁ W₁ = passL1 ms W + 35 * (W : Int) - 147 * (R : Int) - 60)) ∧
          ∃ t, Reach ⟨[], 1, ms₁, W₁⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
        ∃ n ms' W', roundsZ 1000 n ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n ms₁ W₁, 2 ≤ d) ∧
          LoopEnd W₁ R₁ (passL1 ms₁ W₁) n (meetsRounds 1000 n ms₁ W₁) ms' W' ∧
          ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) := by
  obtain ⟨ks, ms₁, W₁, R₁, hch, ⟨hc, ht⟩ | he⟩ := loop_chain_halt_close T R ms W hP hT
  · exact ⟨ks, ms₁, W₁, R₁, hch, Or.inl ⟨hc, hch.close_wideC hc hW, ht⟩⟩
  · exact ⟨ks, ms₁, W₁, R₁, hch, Or.inr he⟩

/-- **From a wide pass start, the loop's chain ends where the run leaves three walls; with end meetings at distance 2
passed.**  `loop_halt_leaves` with the closing classes of `closeClassC` and the end meetings of the chain's last
stretch at distance at least 2, from width 2²⁰: if the machine halts from a phase-0 pass start of width W ≥ 2²⁰ with
walls at a, b, W − R − 1 and every gap at least 448 (and, if W ≡ 2 mod 4, the middle wall at least 896 from the
end), then the chain either reaches a class of `closeClassC` through p full passes, after at most one half pass, or
it ends where the run, with every end meeting at distance at least 2, has left phase 0 or the halving chain at a
round start that is not three walls, and the halt needs a stuck configuration after that. -/
theorem loop_halt_leaves_close (R a b W : Nat) (hP : PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R)
    (hW : 2 ^ 20 ≤ W) (hh : W % 4 = 2 → b + 896 ≤ W) (T : Nat)
    (hT : steps T (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = none) :
    ∃ ks ms₁ W₁ R₁, LoopChain [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R ks ms₁ W₁ R₁ ∧
      ((InCloseClassC ms₁ W₁ R₁ ∧
          (∃ p, (ks = List.replicate p .full ∧ R = 16 ^ p * R₁ ∧
              passL1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W = 64 ^ p * passL1 ms₁ W₁) ∨
            (ks = .half :: List.replicate p .full ∧ W % 4 = 2 ∧ R = 2 * 16 ^ p * R₁ ∧
              2 * 64 ^ p * passL1 ms₁ W₁ =
                passL1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W + 35 * (W : Int) - 147 * (R : Int) - 60)) ∧
          ∃ t, Reach ⟨[], 1, ms₁, W₁⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
        ∃ n ms' W', roundsZ 1000 n ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n ms₁ W₁, 2 ≤ d) ∧
          (LeftPhase0 n ms' ∨ ChainBreak (meetsRounds 1000 n ms₁ W₁)) ∧ NotWWW ms' ∧
          ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) := by
  obtain ⟨ks, ms₁, W₁, R₁, hch, hc | ⟨n, ms', W', hr, hm, he, ht⟩⟩ := loop_halt_wide_close R _ W hP hW T hT
  · exact ⟨ks, ms₁, W₁, R₁, hch, Or.inl hc⟩
  · obtain ⟨a₁, b₁, rfl, -⟩ := id hch.stop
    have hW₁ : W ≤ W₁ := by have := hch.width; omega
    have hh₁ : W₁ % 4 = 2 → b₁ + 896 ≤ W₁ := by
      rcases hch.stop_mod with ⟨hms, rfl, rfl⟩ | h4
      · simp only [List.cons.injEq, Mark.mk.injEq, true_and, and_true] at hms
        obtain ⟨-, rfl⟩ := hms
        exact hh
      · omega
    have hl := loopEnd_wide hch.stop (Nat.le_trans (by decide : 2 ^ 13 ≤ 2 ^ 20) (Nat.le_trans hW hW₁)) hh₁ he
    exact ⟨ks, _, W₁, R₁, hch, Or.inr ⟨n, ms', W', hr, hm, hl.1, hl.2, ht⟩⟩

#print axioms loop_chain_halt_close
#print axioms loop_halt_sigma_close
#print axioms loop_halt_wide_close
#print axioms loop_halt_leaves_close

end BB6
