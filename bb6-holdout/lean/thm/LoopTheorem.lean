import EndgameTheorem
open BB6 BB6.Sym

/-! # The loop's run from a pass start, through its passes

`endgame_stretch` covers every pass start with gaps ≥ 448 (one tree for R ≥ 178, one per R below): a close needs R
in the closing set and L₁ in R's class; otherwise the run is close-free up to an end event.  When the run is at a pass
start there whose gaps are again all ≥ 448 (whichever end event the tree reports: a half pass leaves phase 0 at its
second round, where it is at a pass start again), its right end is smaller, and the run is followed on from there:
strong induction on R.  `loop_stretch` is the result, checked by Lean's kernel (through `endgame_stretch`). -/

/-- At the pass start, R is in the closing set and the left countdown L₁ is in R's class (`closeClass`). -/
def InCloseClass (ms : List Mark) (W R : Nat) : Prop :=
  ∃ a b m c, ms = [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] ∧ closeClass R = some (m, c) ∧ loopL1 b (W - R - 1) W % m = c

/-- **The loop's run from a pass start.**  From every phase-0 pass start with right end R and every gap at least 448
(`PassStart448`), the machine runs without halting, and with every end meeting at distance at least 3, through the pass
starts it reaches whose gaps are again all at least 448, each with a smaller right end, to the last of them, ms₁ W₁ with
right end R₁ ≤ R; from there, either R₁ is in the closing set and L₁ is in R₁'s class, or the run goes on close-free and
without halting to where it leaves the loop (`LoopEnd`): an end event (it leaves phase 0, its end meetings leave the
halving chain, or it reaches the next pass start) at which it is not at a pass start with every gap at least 448.  So
within the loop, a close comes only from a pass start whose right end is in the closing set and whose L₁ is in that
right end's class. -/
theorem loop_stretch : ∀ (R : Nat) (ms : List Mark) (W : Nat), PassStart448 ms W R →
    ∃ n₁ kk₁ ms₁ W₁ R₁, steps kk₁ (roundStart ms W) = some (roundStart ms₁ W₁) ∧
      roundsZ 1000 n₁ ms W = .newRound ms₁ W₁ ∧ (∀ d ∈ meetsRounds 1000 n₁ ms W, 3 ≤ d) ∧
      PassStart448 ms₁ W₁ R₁ ∧ R₁ ≤ R ∧
      (InCloseClass ms₁ W₁ R₁ ∨
        ∃ n₂ kk₂ ms' W', steps kk₂ (roundStart ms₁ W₁) = some (roundStart ms' W') ∧
          roundsZ 1000 n₂ ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n₂ ms₁ W₁, 3 ≤ d) ∧
          LoopEnd 1000 R₁ n₂ (meetsRounds 1000 n₂ ms₁ W₁) ms' W') := by
  intro R
  induction R using Nat.strongRecOn with
  | ind R ih =>
    intro ms W hP
    obtain ⟨a, b, rfl, ha, hb, hW, hR, hR2, h1, h2, h3⟩ := hP
    have hP : PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R := ⟨a, b, rfl, ha, hb, hW, hR, hR2, h1, h2, h3⟩
    have hm0 : ∀ d ∈ meetsRounds 1000 0 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W, 3 ≤ d := by simp [meetsRounds]
    rcases endgame_stretch R hR hR2 a b W ha hb hW h1 h2 h3 with ⟨m, c, hc, hl⟩ | ⟨n, kk, ms', W', hk, hr, hm, hev⟩
    · exact ⟨0, 0, _, W, R, rfl, rfl, hm0, hP, Nat.le_refl R, Or.inl ⟨a, b, m, c, rfl, hc, hl⟩⟩
    · have stop : LoopEnd 1000 R n (meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) ms' W' →
          ∃ n₁ kk₁ ms₁ W₁ R₁, steps kk₁ (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W) = some (roundStart ms₁ W₁) ∧
            roundsZ 1000 n₁ [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W = .newRound ms₁ W₁ ∧
            (∀ d ∈ meetsRounds 1000 n₁ [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W, 3 ≤ d) ∧
            PassStart448 ms₁ W₁ R₁ ∧ R₁ ≤ R ∧
            (InCloseClass ms₁ W₁ R₁ ∨
              ∃ n₂ kk₂ ms' W', steps kk₂ (roundStart ms₁ W₁) = some (roundStart ms' W') ∧
                roundsZ 1000 n₂ ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n₂ ms₁ W₁, 3 ≤ d) ∧
                LoopEnd 1000 R₁ n₂ (meetsRounds 1000 n₂ ms₁ W₁) ms' W') :=
        fun he => ⟨0, 0, _, W, R, rfl, rfl, hm0, hP, Nat.le_refl R, Or.inr ⟨n, kk, ms', W', hk, hr, hm, he⟩⟩
      by_cases hc : PassStart 1000 R ms' W' ∧ ∃ R', PassStart448 ms' W' R'
      · -- at a pass start with every gap at least 448: follow the run on from it
        obtain ⟨⟨a', b', c', R', hms', -, -, -, hc', -, -, hlt, -⟩, R'', hP'⟩ := hc
        have hR' : R'' = R' := by
          obtain ⟨a₂, b₂, hms₂, -, -, -, -, -, -, -, g3⟩ := hP'
          rw [hms'] at hms₂
          simp only [List.cons.injEq, Mark.mk.injEq, true_and, and_true] at hms₂
          omega
        rw [hR'] at hP'
        obtain ⟨n₁, kk₁, ms₁, W₁, R₁, hk₁, hr₁, hm₁, hP₁, hle, hrest⟩ := ih R' hlt ms' W' hP'
        refine ⟨n + n₁, kk + kk₁, ms₁, W₁, R₁, steps_seq hk hk₁, ?_, ?_, hP₁, by omega, hrest⟩
        · rw [roundsZ_add 1000 n n₁ _ _ _ _ hr]; exact hr₁
        · rw [meetsRounds_append 1000 n n₁ _ _ _ _ hr]
          intro d hd
          rcases List.mem_append.mp hd with hd | hd
          · exact hm d hd
          · exact hm₁ d hd
      · -- not at a pass start with every gap at least 448: the run leaves the loop's certified part here
        exact stop ⟨hev, hc⟩

/-- `loop_stretch` for a pass start given by its walls. -/
theorem loop_stretch_walls (R a b E : Nat) (hR : R % 2 = 0) (hR2 : 2 ≤ R) (ha : a % 2 = 1) (hb : b % 2 = 0)
    (hE : E % 2 = 0) (h1 : 448 ≤ a) (h2 : a + 448 ≤ b) (h3 : b + 448 + R + 1 ≤ E) :
    ∃ n₁ kk₁ ms₁ W₁ R₁, steps kk₁ (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E) = some (roundStart ms₁ W₁) ∧
      roundsZ 1000 n₁ [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E = .newRound ms₁ W₁ ∧
      (∀ d ∈ meetsRounds 1000 n₁ [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E, 3 ≤ d) ∧
      PassStart448 ms₁ W₁ R₁ ∧ R₁ ≤ R ∧
      (InCloseClass ms₁ W₁ R₁ ∨
        ∃ n₂ kk₂ ms' W', steps kk₂ (roundStart ms₁ W₁) = some (roundStart ms' W') ∧
          roundsZ 1000 n₂ ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n₂ ms₁ W₁, 3 ≤ d) ∧
          LoopEnd 1000 R₁ n₂ (meetsRounds 1000 n₂ ms₁ W₁) ms' W') :=
  loop_stretch R _ E ⟨a, b, rfl, ha, hb, hE, hR, hR2, h1, h2, h3⟩
