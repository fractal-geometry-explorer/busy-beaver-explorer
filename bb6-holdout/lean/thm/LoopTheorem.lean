import EndgameTheorem
open BB6 BB6.Sym

/-! # The loop's run from a pass start, through its passes

`endgame_stretch` covers every pass start with gaps ≥ 448 (one tree for R ≥ 178, one per R below): a close needs R
in the closing set and L₁ in R's class; otherwise the run is close-free up to an end event.  When the run is at a pass
start there after a full pass (right end R/16, left countdown L₁/64: `PassStart`) whose gaps are again all ≥ 448, it is
followed on from there: strong induction on R.  `loop_stretch` is the result, checked by Lean's kernel (through
`endgame_stretch`): from a pass start with right end R and left countdown L₁, the run makes some number p of full
passes, to a pass start with right end R/16^p and left countdown L₁/64^p, and from there either the right end is in
the closing set with the left countdown in its class, or the run goes on close-free until it leaves the loop.

A pass divides R³ and L₁² by the same factor 4096, so R³/L₁² is the same at every pass start of the run, and at a
close it is at most 176³/256² (`sigma_close`: |L₁| ≥ 256 in the class of R = 176, and the smaller R of the closing
set allow less).  So a close through the loop needs R³/L₁² ≤ 176³/256² at the first pass start already
(`sigma_through_passes`).  With s = log₂(W/R) and λ = log₂(|L₁|/W) at that pass start (W the width) and σ = 3s + 2λ,
this is the notes' bound log₂W ≤ σ + 6.38 (3 log₂ 176 − 2 log₂ 256 = 6.378). -/

/-- At the pass start, R is in the closing set and the left countdown L₁ is in R's class (`closeClass`). -/
def InCloseClass (ms : List Mark) (W R : Nat) : Prop :=
  ∃ a b m c, ms = [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] ∧ closeClass R = some (m, c) ∧ loopL1 b (W - R - 1) W % m = c

/-- **The loop's run from a pass start.**  From every phase-0 pass start with right end R and every gap at least 448
(`PassStart448`), the machine runs without halting, and with every end meeting at distance at least 3, through p ≥ 0
full passes, each to a pass start whose gaps are again all at least 448, to the last of them, ms₁ W₁ with right end
R₁ = R/16^p and left countdown L₁/64^p (`passL1`); from there, either R₁ is in the closing set and the left countdown
is in R₁'s class, or the run goes on close-free and without halting to where it leaves the loop (`LoopEnd`): an end
event (it leaves phase 0, its end meetings leave the halving chain, or it makes a full pass) at which it is not at a
pass start with every gap at least 448 after a full pass.  So within the loop, a close comes only from a pass start
whose right end is in the closing set and whose left countdown is in that right end's class. -/
theorem loop_stretch : ∀ (R : Nat) (ms : List Mark) (W : Nat), PassStart448 ms W R →
    ∃ n₁ kk₁ ms₁ W₁ R₁ p, steps kk₁ (roundStart ms W) = some (roundStart ms₁ W₁) ∧
      roundsZ 1000 n₁ ms W = .newRound ms₁ W₁ ∧ (∀ d ∈ meetsRounds 1000 n₁ ms W, 3 ≤ d) ∧
      PassStart448 ms₁ W₁ R₁ ∧ R = 16 ^ p * R₁ ∧ passL1 ms W = 64 ^ p * passL1 ms₁ W₁ ∧
      (InCloseClass ms₁ W₁ R₁ ∨
        ∃ n₂ kk₂ ms' W', steps kk₂ (roundStart ms₁ W₁) = some (roundStart ms' W') ∧
          roundsZ 1000 n₂ ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n₂ ms₁ W₁, 3 ≤ d) ∧
          LoopEnd 1000 R₁ (passL1 ms₁ W₁) n₂ (meetsRounds 1000 n₂ ms₁ W₁) ms' W') := by
  intro R
  induction R using Nat.strongRecOn with
  | ind R ih =>
    intro ms W hP
    obtain ⟨a, b, rfl, ha, hb, hW, hR, hR2, h1, h2, h3⟩ := hP
    have hP : PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W R := ⟨a, b, rfl, ha, hb, hW, hR, hR2, h1, h2, h3⟩
    have hm0 : ∀ d ∈ meetsRounds 1000 0 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] W, 3 ≤ d := by simp [meetsRounds]
    have hR0 : R = 16 ^ 0 * R := by simp
    have hL0 : ∀ L : Int, L = 64 ^ 0 * L := by simp
    rcases endgame_stretch R hR hR2 a b W ha hb hW h1 h2 h3 with ⟨m, c, hc, hl⟩ | ⟨n, kk, ms', W', hk, hr, hm, hev⟩
    · exact ⟨0, 0, _, W, R, 0, rfl, rfl, hm0, hP, hR0, hL0 _, Or.inl ⟨a, b, m, c, rfl, hc, hl⟩⟩
    · by_cases hc : PassStart 1000 R (loopL1 b (W - R - 1) W) ms' W' ∧ ∃ R', PassStart448 ms' W' R'
      · -- at a pass start after a full pass, with every gap at least 448: follow the run on from it
        obtain ⟨⟨a', b', c', R', hms', -, -, -, hc', -, hR2', h16, h64, -⟩, R'', hP'⟩ := hc
        have hR' : R'' = R' := by
          obtain ⟨a₂, b₂, hms₂, -, -, -, -, -, -, -, g3⟩ := hP'
          rw [hms'] at hms₂
          simp only [List.cons.injEq, Mark.mk.injEq, true_and, and_true] at hms₂
          omega
        rw [hR'] at hP'
        obtain ⟨n₁, kk₁, ms₁, W₁, R₁, p, hk₁, hr₁, hm₁, hP₁, hRp, hLp, hrest⟩ := ih R' (by omega) ms' W' hP'
        refine ⟨n + n₁, kk + kk₁, ms₁, W₁, R₁, p + 1, steps_seq hk hk₁, ?_, ?_, hP₁, ?_, ?_, hrest⟩
        · rw [roundsZ_add 1000 n n₁ _ _ _ _ hr]; exact hr₁
        · rw [meetsRounds_append 1000 n n₁ _ _ _ _ hr]
          intro d hd
          rcases List.mem_append.mp hd with hd | hd
          · exact hm d hd
          · exact hm₁ d hd
        · rw [← h16, hRp, Nat.pow_succ, Nat.mul_comm (16 ^ p) 16, Nat.mul_assoc]
        · rw [hms'] at hLp
          show loopL1 b (W - R - 1) W = _
          rw [← h64, show loopL1 b' c' W' = passL1 [⟨.W, a'⟩, ⟨.W, b'⟩, ⟨.W, c'⟩] W' from rfl, hLp, Int.pow_succ,
            Int.mul_comm ((64 : Int) ^ p) 64, Int.mul_assoc]
      · -- not at a pass start after a full pass with every gap at least 448: the run leaves the loop here
        exact ⟨0, 0, _, W, R, 0, rfl, rfl, hm0, hP, hR0, hL0 _, Or.inr ⟨n, kk, ms', W', hk, hr, hm, hev, hc⟩⟩

/-- `loop_stretch` for a pass start given by its walls. -/
theorem loop_stretch_walls (R a b E : Nat) (hR : R % 2 = 0) (hR2 : 2 ≤ R) (ha : a % 2 = 1) (hb : b % 2 = 0)
    (hE : E % 2 = 0) (h1 : 448 ≤ a) (h2 : a + 448 ≤ b) (h3 : b + 448 + R + 1 ≤ E) :
    ∃ n₁ kk₁ ms₁ W₁ R₁ p, steps kk₁ (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E) = some (roundStart ms₁ W₁) ∧
      roundsZ 1000 n₁ [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E = .newRound ms₁ W₁ ∧
      (∀ d ∈ meetsRounds 1000 n₁ [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E, 3 ≤ d) ∧
      PassStart448 ms₁ W₁ R₁ ∧ R = 16 ^ p * R₁ ∧ loopL1 b (E - R - 1) E = 64 ^ p * passL1 ms₁ W₁ ∧
      (InCloseClass ms₁ W₁ R₁ ∨
        ∃ n₂ kk₂ ms' W', steps kk₂ (roundStart ms₁ W₁) = some (roundStart ms' W') ∧
          roundsZ 1000 n₂ ms₁ W₁ = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n₂ ms₁ W₁, 3 ≤ d) ∧
          LoopEnd 1000 R₁ (passL1 ms₁ W₁) n₂ (meetsRounds 1000 n₂ ms₁ W₁) ms' W') :=
  loop_stretch R _ E ⟨a, b, rfl, ha, hb, hE, hR, hR2, h1, h2, h3⟩

/-! ## The σ bound -/

/-- R³/L² ≤ 176³/256², the value at a close from R = 176 with |L₁| = 256.  At a pass start of width W with right end
R and left countdown L, with s = log₂(W/R), λ = log₂(|L|/W) and σ = 3s + 2λ, this is log₂W ≤ σ + 6.38
(log₂W = σ + 3 log₂R − 2 log₂|L|, and 3 log₂ 176 − 2 log₂ 256 = 6.378). -/
def SigmaOK (R : Nat) (L : Int) : Prop := 256 ^ 2 * (R : Int) ^ 3 ≤ 176 ^ 3 * L ^ 2

theorem int_sq (x : Int) : x ^ 2 = x * x := by rw [Int.pow_succ, Int.pow_succ, Int.pow_zero, Int.one_mul]

theorem sq_ge {L : Int} {k : Nat} (h : (k : Int) ≤ L ∨ L ≤ -(k : Int)) : (k : Int) ^ 2 ≤ L ^ 2 := by
  have h1 : (k : Int) ≤ (L.natAbs : Int) := by omega
  rw [← Int.natAbs_pow_two L, int_sq, int_sq]
  exact Int.mul_self_le_mul_self (by omega) h1

/-- **The closing classes keep R³/L₁² ≤ 176³/256².**  With L₁ ≡ 3 (mod 7) (`loopL1_mod7`), the class of each R in
the closing set bounds |L₁| from below: by 4 for R = 2 and 4 (L₁ ≡ 10 mod 14), 24 for 8, 32 for 16 and 24, 192 for
32 and 256 for 48, 64 and 176 (L₁ ≡ 640 mod 896); R³/L₁² is largest, 176³/256², at R = 176. -/
theorem sigma_close {ms : List Mark} {W R : Nat} (h : InCloseClass ms W R) : SigmaOK R (passL1 ms W) := by
  obtain ⟨a, b, m, c, rfl, hc, hl⟩ := h
  have h7 := loopL1_mod7 b (W - R - 1) W
  show SigmaOK R (loopL1 b (W - R - 1) W)
  generalize loopL1 b (W - R - 1) W = L at hl h7 ⊢
  have hR := closeClass_closing hc
  have hR' : R = 2 ∨ R = 4 ∨ R = 8 ∨ R = 16 ∨ R = 24 ∨ R = 32 ∨ R = 48 ∨ R = 64 ∨ R = 176 := by
    simpa [closingSet] using hR
  unfold SigmaOK
  rcases hR' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show closeClass 2 = some (2, 0) from rfl] at hc; cases hc
    have := sq_ge (L := L) (k := 4) (by omega); omega
  · rw [show closeClass 4 = some (2, 0) from rfl] at hc; cases hc
    have := sq_ge (L := L) (k := 4) (by omega); omega
  · rw [show closeClass 8 = some (8, 0) from rfl] at hc; cases hc
    have := sq_ge (L := L) (k := 24) (by omega); omega
  · rw [show closeClass 16 = some (32, 0) from rfl] at hc; cases hc
    have := sq_ge (L := L) (k := 32) (by omega); omega
  · rw [show closeClass 24 = some (64, 32) from rfl] at hc; cases hc
    have := sq_ge (L := L) (k := 32) (by omega); omega
  · rw [show closeClass 32 = some (64, 0) from rfl] at hc; cases hc
    have := sq_ge (L := L) (k := 192) (by omega); omega
  · rw [show closeClass 48 = some (128, 0) from rfl] at hc; cases hc
    have := sq_ge (L := L) (k := 256) (by omega); omega
  · rw [show closeClass 64 = some (128, 0) from rfl] at hc; cases hc
    have := sq_ge (L := L) (k := 256) (by omega); omega
  · rw [show closeClass 176 = some (128, 0) from rfl] at hc; cases hc
    have := sq_ge (L := L) (k := 256) (by omega); omega

/-- A full pass divides R³ and L₁² by the same factor, 16³ = 64² = 4096. -/
theorem sigma_pass (R : Nat) (L : Int) (h : SigmaOK R L) : SigmaOK (16 * R) (64 * L) := by
  unfold SigmaOK at *
  have e1 : ((16 * R : Nat) : Int) ^ 3 = 4096 * (R : Int) ^ 3 := by rw [Int.natCast_mul, Int.mul_pow]; rfl
  have e2 : (64 * L) ^ 2 = 4096 * L ^ 2 := by rw [Int.mul_pow]; rfl
  rw [e1, e2]
  omega

theorem sigma_passes (p R : Nat) (L : Int) (h : SigmaOK R L) : SigmaOK (16 ^ p * R) (64 ^ p * L) := by
  induction p with
  | zero => simpa using h
  | succ p ih =>
    have := sigma_pass _ _ ih
    rwa [Nat.pow_succ, Int.pow_succ, Nat.mul_comm (16 ^ p) 16, Nat.mul_assoc, Int.mul_comm ((64 : Int) ^ p) 64,
      Int.mul_assoc]

/-- **The σ bound through the loop.**  If the loop's run from a pass start (right end R, left countdown L) makes p
full passes to a pass start in a closing class (`loop_stretch`), then R³/L² ≤ 176³/256²: log₂W ≤ σ + 6.38 at the
first pass start. -/
theorem sigma_through_passes {ms₁ : List Mark} {W₁ R₁ : Nat} (h : InCloseClass ms₁ W₁ R₁) (p R : Nat) (L : Int)
    (hR : R = 16 ^ p * R₁) (hL : L = 64 ^ p * passL1 ms₁ W₁) : SigmaOK R L := by
  rw [hR, hL]
  exact sigma_passes p _ _ (sigma_close h)
