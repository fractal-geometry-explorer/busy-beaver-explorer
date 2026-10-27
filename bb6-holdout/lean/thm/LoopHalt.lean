import LoopTheorem
import BB6.HaltStretch

/-!
# A halt from a pass start: the loop's chain, then a contact

`loop_step` with `halt_after_rounds`, by induction on the halting time: if the machine halts from a phase-0 pass start
whose gaps are all at least 448 (`PassStart448`), its run follows the loop's chain (`LoopChain`) through full passes,
round-7 breaks and a half pass (only as the first step), each with its exact map on the width, the right end and the
left countdown, each to a pass start whose gaps are again all at least 448, to the last of them, `ms₁ W₁` with right
end R₁.  Each step takes at least one machine step, since the width grows (`passStart_ne`), so the chain is finite.
From the last pass start, either R₁ is in the closing set and the left countdown is in R₁'s class (`InCloseClass`), and
the mark model, run on from `ms₁ W₁`, reaches a stuck configuration; or the run goes on close-free to where the chain
ends (`LoopEnd`: a round start that is not three walls, or a landing with a gap below 448), and the model reaches a
stuck configuration from there.  A stuck configuration is a close at the right end or an interior contact
(`stuck_cases`).

`loop_halt_sigma` is the σ bound: from a pass start with R³/L₁² > 176³/256² (log₂W > σ + 6.38), a close through the
loop needs a half pass or a round-7 break on the way.  `loop_halt_wide`: from a pass start of width at least 2²⁷, a
close through the loop makes no round-7 break; the chain to it is p full passes, after at most one half pass at the
start (`LoopChain.close_wide`).
-/

namespace BB6
open BB6.Sym

/-- A pass start with every gap at least 448 is a well-formed round start without gap marks. -/
theorem PassStart448.wf {ms : List Mark} {W R : Nat} (h : PassStart448 ms W R) : roundWF ms W ∧ noG ms := by
  obtain ⟨a, b, rfl, ha, hb, hW, hR, hR2, h1, h2, h3⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [roundWF, rightOK, mval, mlen, iff_true]
    omega
  · intro m hm
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp

/-! ## Round starts of different widths are different -/

theorem stripe_cell_lt (b : Bool) (s : Tape) : ∀ (n i : Nat), i < n →
    stripe b n s i = (if i % 2 = 0 then b else !b)
  | 0, i, h => absurd h (Nat.not_lt_zero i)
  | n + 1, 0, _ => by simp [stripe, cons]
  | n + 1, i + 1, h => by
    simp only [stripe, cons]
    rw [stripe_cell_lt (!b) s n i (by omega)]
    by_cases hi : i % 2 = 0
    · have : (i + 1) % 2 = 1 := by omega
      simp [hi, this]
    · have : (i + 1) % 2 = 0 := by omega
      simp [hi, this]

theorem stripe_cell_ge (b : Bool) (s : Tape) : ∀ (n j : Nat), stripe b n s (n + j) = s j
  | 0, j => by simp
  | n + 1, j => by
    simp only [stripe, cons]
    rw [show n + 1 + j = (n + j) + 1 by omega]
    exact stripe_cell_ge (!b) s n j

theorem app_two (x y : Bool) (s : Tape) (j : Nat) : app [x, y] s (j + 2) = s j := rfl

/-- The cell at W − 1 of a three-wall round start (index W − 5 of the stream from cell 4) whose right end W − c − 1 is
even: the last cell of the stripe after the last wall, set. -/
theorem www_cell (a b c W : Nat) (h1 : 4 ≤ a) (h2 : a + 2 ≤ b) (h3 : b + 2 ≤ c) (h4 : c + 3 ≤ W)
    (hR : (W - c - 1) % 2 = 0) : build false 4 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] W (W - 5) = true := by
  simp only [build, mcells, mval, mlen, Bool.not_false]
  rw [show W - 5 = (a - 4) + ((W - 3 - a) + 2) by omega, stripe_cell_ge, app_two,
    show W - 3 - a = (b - (a + 2)) + ((W - 3 - b) + 2) by omega, stripe_cell_ge, app_two,
    show W - 3 - b = (c - (b + 2)) + ((W - 3 - c) + 2) by omega, stripe_cell_ge, app_two,
    stripe_cell_lt true _ (W - (c + 2)) (W - 3 - c) (by omega)]
  have : (W - 3 - c) % 2 = 0 := by omega
  simp [this]

/-- A three-wall round start is blank from W on. -/
theorem www_blank (a b c W : Nat) (h1 : 4 ≤ a) (h2 : a + 2 ≤ b) (h3 : b + 2 ≤ c) (h4 : c + 2 ≤ W) (j : Nat) :
    build false 4 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, c⟩] W (W - 4 + j) = false := by
  simp only [build, mcells, mval, mlen, Bool.not_false]
  rw [show W - 4 + j = (a - 4) + ((W - 2 - a + j) + 2) by omega, stripe_cell_ge, app_two,
    show W - 2 - a + j = (b - (a + 2)) + ((W - 2 - b + j) + 2) by omega, stripe_cell_ge, app_two,
    show W - 2 - b + j = (c - (b + 2)) + ((W - 2 - c + j) + 2) by omega, stripe_cell_ge, app_two,
    show W - 2 - c + j = (W - (c + 2)) + j by omega, stripe_cell_ge]
  rfl

/-- Pass starts of different widths are different round starts. -/
theorem passStart_ne {ms ms' : List Mark} {W R W' R' : Nat} (hP : PassStart448 ms W R)
    (hP' : PassStart448 ms' W' R') (hlt : W < W') : roundStart ms W ≠ roundStart ms' W' := by
  obtain ⟨a, b, rfl, -, -, -, -, hR2, h1, h2, h3⟩ := hP
  obtain ⟨a', b', rfl, -, -, -, hR', hR2', h1', h2', h3'⟩ := hP'
  intro h
  have hr := congrArg (fun c => c.r (W' - 5 + 1)) h
  simp only [roundStart, cons] at hr
  rw [www_cell a' b' (W' - R' - 1) W' (by omega) (by omega) (by omega) (by omega) (by omega),
    show W' - 5 = W - 4 + (W' - W - 1) by omega,
    www_blank a b (W - R - 1) W (by omega) (by omega) (by omega) (by omega)] at hr
  cases hr

/-! ## The chain to a halt -/

/-- **A halt from a pass start: the loop's chain.**  If the machine halts T steps after a phase-0 pass start with
right end R and every gap at least 448, then its run from there follows the loop's chain (`LoopChain`): full passes,
round-7 breaks and a half pass (only as the first step), each close-free, with its exact map on the width, the right
end and the left countdown, and each to a pass start whose gaps are again all at least 448, up to the last of them,
`ms₁ W₁` with right end R₁.  From there, either R₁ is in the closing set {2, 4, 8, 16, 24, 32, 48, 64, 176} and the
left countdown is in R₁'s class (`InCloseClass`), and the mark model, run on from `ms₁ W₁`, reaches a stuck
configuration; or the model covers a further close-free stretch to where the chain ends (`LoopEnd`: a round start that
is not three walls after the run left phase 0 or the halving chain, or a landing of the chain with a gap below 448)
and reaches a stuck configuration from there: a close at the right end or an interior contact. -/
theorem loop_chain_halt (T : Nat) : ∀ (R : Nat) (ms : List Mark) (W : Nat), PassStart448 ms W R →
    steps T (roundStart ms W) = none →
    ∃ ks ms₁ W₁ R₁, LoopChain ms W R ks ms₁ W₁ R₁ ∧
      ((InCloseClass ms₁ W₁ R₁ ∧ ∃ t, Reach ⟨[], 1, ms₁, W₁⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
        ∃ n ms' W', roundsZ 1000 n ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n ms₁ W₁, 3 ≤ d) ∧
          LoopEnd W₁ R₁ (passL1 ms₁ W₁) n (meetsRounds 1000 n ms₁ W₁) ms' W' ∧
          ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) := by
  induction T using Nat.strongRecOn with
  | ind T ih =>
    intro R ms W hP hT
    obtain ⟨hwf, hG⟩ := hP.wf
    rcases loop_step R ms W hP with hc | ⟨n, kk, ms', W', hk, hr, hm, hev⟩
    · obtain ⟨t, ht, htw, hts⟩ := round_halt_needs_contact ms W T hwf hG hT
      exact ⟨[], ms, W, R, .nil hP, Or.inl ⟨hc, t, ht, htw, stuck_cases hts⟩⟩
    · obtain ⟨k, hkT, hk', hT', -, t, ht, htw, hts⟩ := halt_after_rounds 1000 n ms W ms' W' hwf hG hr T hT
      by_cases hc : ∃ R', PassStart448 ms' W' R'
      · -- the end event is a landing at a pass start with every gap at least 448: follow the chain on from it
        obtain ⟨R', hP'⟩ := hc
        have hl : Landing n W R (passL1 ms W) ms' W' := by
          rcases hev with ⟨-, hn⟩ | hl
          · exact absurd hn (PassStart448.www hP')
          · exact hl
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
      · exact ⟨[], ms, W, R, .nil hP, Or.inr ⟨n, ms', W', hr, hm, ⟨hev, hc⟩, t, ht, htw, stuck_cases hts⟩⟩

/-- **The σ bound.**  If the machine halts from a phase-0 pass start with right end R, every gap at least 448 and
R³/L₁² > 176³/256² (with s = log₂(W/R), λ = log₂(|L₁|/W) and σ = 3s + 2λ: log₂W > σ + 6.38), then it does not close
through full passes alone: the loop's chain from there (`loop_chain_halt`) either makes a half pass or a round-7 break
before it reaches a closing class, or it ends (`LoopEnd`) and the halt needs a stuck configuration after that. -/
theorem loop_halt_sigma (R : Nat) (ms : List Mark) (W : Nat) (hP : PassStart448 ms W R)
    (hσ : ¬ SigmaOK R (passL1 ms W)) (T : Nat) (hT : steps T (roundStart ms W) = none) :
    ∃ ks ms₁ W₁ R₁, LoopChain ms W R ks ms₁ W₁ R₁ ∧
      ((InCloseClass ms₁ W₁ R₁ ∧ (StepKind.half ∈ ks ∨ StepKind.break7 ∈ ks) ∧
          ∃ t, Reach ⟨[], 1, ms₁, W₁⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
        ∃ n ms' W', roundsZ 1000 n ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n ms₁ W₁, 3 ≤ d) ∧
          LoopEnd W₁ R₁ (passL1 ms₁ W₁) n (meetsRounds 1000 n ms₁ W₁) ms' W' ∧
          ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) := by
  obtain ⟨ks, ms₁, W₁, R₁, hch, ⟨hc, ht⟩ | he⟩ := loop_chain_halt T R ms W hP hT
  · refine ⟨ks, ms₁, W₁, R₁, hch, Or.inl ⟨hc, ?_, ht⟩⟩
    apply Classical.byContradiction
    intro hn
    apply hσ
    refine hch.sigma_all_full hc fun k hk => ?_
    cases k with
    | full => rfl
    | half => exact absurd (Or.inl hk) hn
    | break7 => exact absurd (Or.inr hk) hn
  · exact ⟨ks, ms₁, W₁, R₁, hch, Or.inr he⟩

/-- **From a wide pass start, a close through the loop makes no round-7 break.**  If the machine halts from a phase-0
pass start of width W ≥ 2²⁷ with right end R and every gap at least 448, then the loop's chain from there
(`loop_chain_halt`) either ends (`LoopEnd`) and the halt needs a stuck configuration after that, or it reaches a
closing class at `ms₁ W₁` (right end R₁) through p full passes, with R = 16^p R₁ and L₁ = 64^p L₁′, or through a half
pass (from W ≡ 2 mod 4) and then p full passes, with R = 2 · 16^p R₁ and 2 · 64^p L₁′ = L₁ + 35 W − 147 R − 60 (L₁ and
L₁′ the left countdowns at `ms W` and `ms₁ W₁`), and the mark model, run on from `ms₁ W₁`, reaches a stuck
configuration. -/
theorem loop_halt_wide (R : Nat) (ms : List Mark) (W : Nat) (hP : PassStart448 ms W R) (hW : 2 ^ 27 ≤ W) (T : Nat)
    (hT : steps T (roundStart ms W) = none) :
    ∃ ks ms₁ W₁ R₁, LoopChain ms W R ks ms₁ W₁ R₁ ∧
      ((InCloseClass ms₁ W₁ R₁ ∧
          (∃ p, (ks = List.replicate p .full ∧ R = 16 ^ p * R₁ ∧ passL1 ms W = 64 ^ p * passL1 ms₁ W₁) ∨
            (ks = .half :: List.replicate p .full ∧ W % 4 = 2 ∧ R = 2 * 16 ^ p * R₁ ∧
              2 * 64 ^ p * passL1 ms₁ W₁ = passL1 ms W + 35 * (W : Int) - 147 * (R : Int) - 60)) ∧
          ∃ t, Reach ⟨[], 1, ms₁, W₁⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) ∨
        ∃ n ms' W', roundsZ 1000 n ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n ms₁ W₁, 3 ≤ d) ∧
          LoopEnd W₁ R₁ (passL1 ms₁ W₁) n (meetsRounds 1000 n ms₁ W₁) ms' W' ∧
          ∃ t, Reach ⟨[], 1, ms', W'⟩ t ∧ t.wf ∧ (EndClose t ∨ InteriorContact t)) := by
  obtain ⟨ks, ms₁, W₁, R₁, hch, ⟨hc, ht⟩ | he⟩ := loop_chain_halt T R ms W hP hT
  · exact ⟨ks, ms₁, W₁, R₁, hch, Or.inl ⟨hc, hch.close_wide hc hW, ht⟩⟩
  · exact ⟨ks, ms₁, W₁, R₁, hch, Or.inr he⟩

#print axioms loop_chain_halt
#print axioms loop_halt_sigma
#print axioms loop_halt_wide

end BB6
