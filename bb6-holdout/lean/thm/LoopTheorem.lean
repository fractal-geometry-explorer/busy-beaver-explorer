import EndgameTheorem
open BB6 BB6.Sym

/-! # The loop's chain from a pass start

`endgame_stretch` covers every pass start with gaps ≥ 448 (one tree for R ≥ 178, one per R below): a close needs R
in the closing set and L₁ in R's class; otherwise the run is close-free up to an end event (`loop_step`).  The end
event is a round start that is not three walls, after the run left phase 0 or the halving chain, or a landing of the
loop's chain: a full pass, a half pass or a break of the chain at round 7, each with an exact map on the width E, the
right end R and the left countdown L₁ (`StepMap`).  When the landing's gaps are again all ≥ 448, the run is followed on
from there.  `LoopChain` is the chain of these steps.  A round-7 break can raise R, so the chain is followed by
induction on the halting time (`loop_chain_halt` in `LoopHalt.lean`).

A half pass starts from a width E ≡ 2 (mod 4) and every landing has width ≡ 0 (mod 4), so a half pass can only be the
first step of a chain (`LoopChain.half_first`).  The width grows by 24 at a full pass or a round-7 break and by 6 at a
half pass (`LoopChain.width`).

**σ.**  A full pass divides R³ and L₁² by the same factor 4096, so R³/L₁² is the same at every pass start of a run of
full passes, and at a close it is at most 176³/256² (`sigma_close`: |L₁| ≥ 256 in the class of R = 176, and the
smaller R of the closing set allow less).  So a chain that ends in a closing class has R³/L₁² ≤ 176³/256² (`SigmaOK`)
at the start of its last run of full passes (`LoopChain.sigma`).  With s = log₂(W/R) and λ = log₂(|L₁|/W) there (W the
width) and σ = 3s + 2λ, this is the notes' bound log₂W ≤ σ + 6.38 (3 log₂ 176 − 2 log₂ 256 = 6.378).  At a round-7
landing 32R′ ≥ 3E + 5R and 0 < 96L₁′ ≤ 385(3E + 5R), so `SigmaOK` there needs E < 2²⁴ (`break7_sigma`).  From a
pass start of width at least 2²⁴, a chain that ends in a closing class therefore makes no round-7 break: it is p full
passes, after at most one half pass at the start (`LoopChain.close_wide`). -/

/-- At the pass start, R is in the closing set and the left countdown L₁ is in R's class (`closeClass`). -/
def InCloseClass (ms : List Mark) (W R : Nat) : Prop :=
  ∃ a b m c, ms = [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, W - R - 1⟩] ∧ closeClass R = some (m, c) ∧ loopL1 b (W - R - 1) W % m = c

/-- The loop's chain from the pass start `ms W` with right end R to the pass start `ms' W'` with right end R′, through
steps of the kinds `ks`.  Every pass start of the chain has every gap at least 448 (`PassStart448`); each step runs n
rounds (kk machine steps) from one to the next, close-free (every end meeting at distance at least 3), to a width
W₁ ≡ 0 (mod 4), with the map of its kind (`StepMap`) from the width, right end and left countdown (`passL1`) of its
start to those of its landing. -/
inductive LoopChain : List Mark → Nat → Nat → List StepKind → List Mark → Nat → Nat → Prop
  | nil {ms : List Mark} {W R : Nat} : PassStart448 ms W R → LoopChain ms W R [] ms W R
  | cons {ms : List Mark} {W R : Nat} {ks : List StepKind} {ms₁ : List Mark} {W₁ R₁ : Nat} {ms' : List Mark}
      {W' R' : Nat} (k : StepKind) (n kk : Nat) : PassStart448 ms W R →
      steps kk (roundStart ms W) = some (roundStart ms₁ W₁) → roundsZ 1000 n ms W = .newRound ms₁ W₁ →
      (∀ d ∈ meetsRounds 1000 n ms W, 3 ≤ d) → W₁ % 4 = 0 →
      StepMap k n W R (passL1 ms W) W₁ R₁ (passL1 ms₁ W₁) → LoopChain ms₁ W₁ R₁ ks ms' W' R' →
      LoopChain ms W R (k :: ks) ms' W' R'

/-- **One step of the loop's chain.**  From every phase-0 pass start with right end R and every gap at least 448,
either R is in the closing set and the left countdown is in R's class, or the machine runs n rounds without halting,
reaching the round start that `roundsZ` computes, every end meeting on the way is at distance at least 3 (no close),
and the run ends at an end event (`EndEvent`) with the start's width W, right end R and left countdown L₁ =
`passL1 ms W`: a round start that is not three walls after the run left phase 0 or the halving chain, or a landing of
the loop's chain (`Landing`). -/
theorem loop_step (R : Nat) (ms : List Mark) (W : Nat) (hP : PassStart448 ms W R) :
    InCloseClass ms W R ∨
    ∃ n kk ms' W', steps kk (roundStart ms W) = some (roundStart ms' W') ∧
      roundsZ 1000 n ms W = .newRound ms' W' ∧ (∀ d ∈ meetsRounds 1000 n ms W, 3 ≤ d) ∧
      EndEvent W R (passL1 ms W) n (meetsRounds 1000 n ms W) ms' W' := by
  obtain ⟨a, b, rfl, ha, hb, hW, hR, hR2, h1, h2, h3⟩ := hP
  rcases endgame_stretch R hR hR2 a b W ha hb hW h1 h2 h3 with ⟨m, c, hc, hl⟩ | h
  · exact Or.inl ⟨a, b, m, c, rfl, hc, hl⟩
  · exact Or.inr h

/-- A pass start is three walls. -/
theorem BB6.PassStart448.www {ms : List Mark} {W R : Nat} (h : PassStart448 ms W R) : ¬ NotWWW ms := by
  obtain ⟨a, b, rfl, -⟩ := h
  exact fun hn => hn a b _ rfl

/-- A landing that is a pass start with every gap at least 448: its width is ≡ 0 (mod 4), and the step's map ends at
the pass start's right end and left countdown. -/
theorem landing_passStart {n E R : Nat} {L : Int} {ms : List Mark} {W R' : Nat} (hl : Landing n E R L ms W)
    (hP : PassStart448 ms W R') : W % 4 = 0 ∧ ∃ k, StepMap k n E R L W R' (passL1 ms W) := by
  obtain ⟨k, a, b, c, R₁, rfl, -, -, hW, hc, -, -, hm, -⟩ := hl
  obtain ⟨a₂, b₂, hms, -, -, -, -, -, -, -, h3⟩ := hP
  simp only [List.cons.injEq, Mark.mk.injEq, true_and, and_true] at hms
  obtain ⟨-, -, hc₂⟩ := hms
  have e : R₁ = R' := by omega
  subst e
  exact ⟨hW, k, hm⟩

/-- **Wide landings keep their gaps.**  From a pass start of width E ≥ 2¹³ with every gap at least 448, a landing of
the loop's chain is again a pass start with every gap at least 448, unless it is a half pass from a start whose middle
wall b is within 896 of the end: a half pass lands with last gap (E − b)/2.  With c = E − R − 1, the landing's first two
walls are 64a′ = b + 4c + 12E + 678 and 64b′ = b + 8c + 40E + 1258 after a full pass, 2a′ = b + 10 and 2b′ = b + c + 11
after a half pass, 16a′ = b + c + E + 135 and 32b′ = 3b + 6c + 10E + 452 after a round-7 break (a′ from `StepWall`, b′
from `StepMap` through the left countdown); a full pass needs E ≥ 2,334 for a′ ≥ 448, a round-7 break E ≥ 6,138. -/
theorem landing_wide {a b E R : Nat} (hP : PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E R)
    (hE : 2 ^ 13 ≤ E) (hh : E % 4 = 2 → b + 896 ≤ E) {n : Nat} {ms' : List Mark} {W' : Nat}
    (hl : Landing n E R (passL1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E) ms' W') : ∃ R', PassStart448 ms' W' R' := by
  obtain ⟨a₀, b₀, hms, -, -, -, -, -, h1, h2, h3⟩ := hP
  simp only [List.cons.injEq, Mark.mk.injEq, true_and, and_true] at hms
  obtain ⟨rfl, rfl⟩ := hms
  obtain ⟨k, a', b', c', R', rfl, ha', hb', hW4, hc', hR2, hR', hm, hw⟩ := hl
  have hL : passL1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E = 147 * (b : Int) - 112 * E + 392 * R - 186 := by
    show loopL1 b (E - R - 1) E = _
    unfold loopL1
    omega
  rw [hL] at hm hw
  have hE' : 8192 ≤ E := hE
  have key : 448 ≤ a' ∧ a' + 448 ≤ b' ∧ b' + 448 + R' + 1 ≤ W' := by
    clear ha' hb' hW4 hR2 hE hL
    cases k with
    | full =>
      obtain ⟨-, e1, e2, e3⟩ := hm
      simp only [StepWall] at hw
      unfold loopL1 at e2
      clear hh
      omega
    | half =>
      obtain ⟨-, e1, e2, e3, e4⟩ := hm
      simp only [StepWall] at hw
      unfold loopL1 at e2
      have h4 := hh e4
      clear hh e4
      have hw' : 2 * (a' : Int) = b + 10 := by omega
      have e2' : 2 * (b' : Int) = b + E - R + 10 := by omega
      clear hw e2
      omega
    | break7 =>
      obtain ⟨-, e1, e2, e3⟩ := hm
      simp only [StepWall] at hw
      unfold loopL1 at e2
      clear hh
      omega
  refine ⟨R', a', b', ?_, ha', hb', by omega, hR2, hR', key.1, key.2.1, key.2.2⟩
  rw [show W' - R' - 1 = c' by omega]

/-- **From a wide pass start the chain's end leaves three walls.**  At a pass start of width E ≥ 2¹³ with every gap at
least 448 (and, if E ≡ 2 mod 4, the middle wall at least 896 from the end), an end of the loop's chain (`LoopEnd`) is
not a landing: the run left phase 0 or the halving chain, at a round start that is not three walls. -/
theorem loopEnd_wide {a b E R : Nat} (hP : PassStart448 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E R)
    (hE : 2 ^ 13 ≤ E) (hh : E % 4 = 2 → b + 896 ≤ E) {n : Nat} {ds : List Nat} {ms' : List Mark} {W' : Nat}
    (he : LoopEnd E R (passL1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E) n ds ms' W') :
    (LeftPhase0 n ms' ∨ ChainBreak ds) ∧ NotWWW ms' := by
  obtain ⟨he | hl, hn⟩ := he
  · exact he
  · exact absurd (landing_wide hP hE hh hl) hn

/-- Every list of steps is a list that does not end with a full pass, followed by a run of full passes. -/
theorem split_fulls : ∀ ks : List StepKind, ∃ ks₁ p, ks = ks₁ ++ List.replicate p .full ∧
    (ks₁ = [] ∨ ∃ ks₀ k, ks₁ = ks₀ ++ [k] ∧ k ≠ .full)
  | [] => ⟨[], 0, rfl, Or.inl rfl⟩
  | k :: ks => by
    obtain ⟨ks₁, p, rfl, hl⟩ := split_fulls ks
    rcases hl with rfl | ⟨ks₀, k', rfl, hk'⟩
    · by_cases hk : k = .full
      · exact ⟨[], p + 1, by rw [hk]; rfl, Or.inl rfl⟩
      · exact ⟨[k], p, rfl, Or.inr ⟨[], k, rfl, hk⟩⟩
    · exact ⟨k :: (ks₀ ++ [k']), p, by simp, Or.inr ⟨k :: ks₀, k', by simp, hk'⟩⟩

namespace LoopChain

variable {ms : List Mark} {W R : Nat} {ks : List StepKind} {ms' : List Mark} {W' R' : Nat}

/-- The chain's last pass start. -/
theorem stop (h : LoopChain ms W R ks ms' W' R') : PassStart448 ms' W' R' := by
  induction h with
  | nil hP => exact hP
  | cons _ _ _ _ _ _ _ _ _ _ ih => exact ih

/-- The chain's last pass start is its first, or a landing: of width ≡ 0 (mod 4). -/
theorem stop_mod (h : LoopChain ms W R ks ms' W' R') : (ms' = ms ∧ W' = W ∧ R' = R) ∨ W' % 4 = 0 := by
  induction h with
  | nil _ => exact Or.inl ⟨rfl, rfl, rfl⟩
  | cons _ _ _ _ _ _ _ hW4 _ _ ih =>
    rcases ih with ⟨rfl, rfl, rfl⟩ | h
    · exact Or.inr hW4
    · exact Or.inr h

/-- The chain's first pass start. -/
theorem start (h : LoopChain ms W R ks ms' W' R') : PassStart448 ms W R := by
  cases h with
  | nil hP => exact hP
  | cons _ _ _ hP => exact hP

/-- The chain's last pass start. -/
theorem last (h : LoopChain ms W R ks ms' W' R') : PassStart448 ms' W' R' := by
  induction h with
  | nil hP => exact hP
  | cons _ _ _ _ _ _ _ _ _ _ ih => exact ih

/-- **The width.**  It grows by 24 at a full pass or a round-7 break and by 6 at a half pass. -/
theorem width (h : LoopChain ms W R ks ms' W' R') :
    W' = W + 24 * (ks.count .full + ks.count .break7) + 6 * ks.count .half := by
  induction h with
  | nil => simp
  | cons k _ _ _ _ _ _ _ hm _ ih =>
    cases k <;> simp only [StepMap] at hm <;> simp only [List.count_cons, beq_iff_eq, reduceCtorEq, ↓reduceIte] <;>
      omega

/-- From a width ≡ 0 (mod 4) the chain makes no half pass: a half pass starts from a width ≡ 2 (mod 4). -/
theorem no_half (h : LoopChain ms W R ks ms' W' R') : W % 4 = 0 → StepKind.half ∉ ks := by
  induction h with
  | nil => intro _; simp
  | cons k _ _ _ _ _ _ hW₁ hm _ ih =>
    intro hW hk
    rcases List.mem_cons.mp hk with rfl | hk
    · simp only [StepMap] at hm; omega
    · exact ih hW₁ hk

/-- **A half pass only as the first step**: every landing has width ≡ 0 (mod 4). -/
theorem half_first {k : StepKind} (h : LoopChain ms W R (k :: ks) ms' W' R') : StepKind.half ∉ ks := by
  cases h with
  | cons _ _ _ _ _ _ _ hW₁ _ tl => exact tl.no_half hW₁

theorem append {ks₂ : List StepKind} {ms₂ : List Mark} {W₂ R₂ : Nat} (h₁ : LoopChain ms W R ks ms' W' R')
    (h₂ : LoopChain ms' W' R' ks₂ ms₂ W₂ R₂) : LoopChain ms W R (ks ++ ks₂) ms₂ W₂ R₂ := by
  induction h₁ with
  | nil => exact h₂
  | cons k n kk hP hk hr hm hW hmap _ ih => exact .cons k n kk hP hk hr hm hW hmap (ih h₂)

theorem split : ∀ (ks₁ : List StepKind) {ks₂ : List StepKind} {ms : List Mark} {W R : Nat} {ms' : List Mark}
    {W' R' : Nat}, LoopChain ms W R (ks₁ ++ ks₂) ms' W' R' →
    ∃ ms₁ W₁ R₁, LoopChain ms W R ks₁ ms₁ W₁ R₁ ∧ LoopChain ms₁ W₁ R₁ ks₂ ms' W' R'
  | [], _, _, _, _, _, _, _, h => ⟨_, _, _, .nil h.start, h⟩
  | k :: ks₁, _, _, _, _, _, _, _, h => by
    cases h with
    | cons _ n kk hP hk hr hm hW hmap tl =>
      obtain ⟨ms₁, W₁, R₁, h₁, h₂⟩ := split ks₁ tl
      exact ⟨ms₁, W₁, R₁, .cons k n kk hP hk hr hm hW hmap h₁, h₂⟩

/-- An empty chain stays at its pass start. -/
theorem nil_eq (h : LoopChain ms W R [] ms' W' R') : ms' = ms ∧ W' = W ∧ R' = R := by
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- **Through a run of full passes**: R = 16^p R′ and L₁ = 64^p L₁′. -/
theorem fulls : ∀ (p : Nat) {ms : List Mark} {W R : Nat} {ms' : List Mark} {W' R' : Nat},
    LoopChain ms W R (List.replicate p .full) ms' W' R' → R = 16 ^ p * R' ∧ passL1 ms W = 64 ^ p * passL1 ms' W'
  | 0, _, _, _, _, _, _, h => by
    obtain ⟨rfl, rfl, rfl⟩ := nil_eq h
    simp
  | p + 1, _, _, _, _, _, _, h => by
    cases h with
    | cons _ _ _ _ _ _ _ _ hmap tl =>
      obtain ⟨hR, hL⟩ := fulls p tl
      obtain ⟨-, h16, h64, -⟩ := hmap
      refine ⟨?_, ?_⟩
      · rw [← h16, hR, Nat.pow_succ, Nat.mul_comm (16 ^ p) 16, Nat.mul_assoc]
      · rw [← h64, hL, Int.pow_succ, Int.mul_comm ((64 : Int) ^ p) 64, Int.mul_assoc]

end LoopChain

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

/-- **σ at a round-7 landing.**  A round-7 break from a pass start of width E with right end R and every gap at least
448 lands with 32 R′ = 4E + 4R − b + 110 ≥ 3E + 5R + 559 and 96 L₁′ = 147 b + 1008 E + 2058 R + 50142 ≤
1155 E + 1911 R − 15861 (b the middle wall, at most E − R − 449).  With S = 3E + 5R that is 32 R′ ≥ S and
0 < 96 L₁′ ≤ 385 S, so R′³/L₁′² ≤ 176³/256² there needs 18432 S ≤ 176³ · 385², that is S ≤ 43,841,661: E < 2²⁴
(E ≤ 14,613,887). -/
theorem break7_sigma {ms : List Mark} {E R : Nat} (hP : PassStart448 ms E R) {n W R' : Nat} {L' : Int}
    (hm : StepMap .break7 n E R (passL1 ms E) W R' L') (hσ : SigmaOK R' L') : E < 2 ^ 24 := by
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
  have c3 : 65536 * R' ^ 3 ≤ 5451776 * l ^ 2 := by
    unfold SigmaOK at hσ
    have e : ((65536 * R' ^ 3 : Nat) : Int) ≤ ((5451776 * l ^ 2 : Nat) : Int) := by
      rw [Int.natCast_mul, Int.natCast_mul, Int.natCast_pow, Int.natCast_pow]
      exact hσ
    exact Int.ofNat_le.mp e
  apply Nat.lt_of_not_le
  intro hE
  have hE' : 16777216 ≤ E := hE
  have hS' : 50331648 ≤ S := by omega
  have m : S ^ 2 * 50331648 ≤ S ^ 3 := by
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
theorem sigma_fulls (p : Nat) (h : LoopChain ms W R (List.replicate p .full) ms' W' R')
    (hσ : SigmaOK R' (passL1 ms' W')) : SigmaOK R (passL1 ms W) := by
  obtain ⟨hR, hL⟩ := fulls p h
  rw [hR, hL]
  exact sigma_passes p _ _ hσ

/-- **σ through the chain.**  A chain that ends in a closing class is a chain `ks₁` that does not end with a full pass,
to a pass start with R³/L₁² ≤ 176³/256² (`SigmaOK`: log₂W ≤ σ + 6.38 there), followed by p full passes. -/
theorem sigma (h : LoopChain ms W R ks ms' W' R') (hc : InCloseClass ms' W' R') :
    ∃ ks₁ p ms₁ W₁ R₁, ks = ks₁ ++ List.replicate p .full ∧ (ks₁ = [] ∨ ∃ ks₀ k, ks₁ = ks₀ ++ [k] ∧ k ≠ .full) ∧
      LoopChain ms W R ks₁ ms₁ W₁ R₁ ∧ LoopChain ms₁ W₁ R₁ (List.replicate p .full) ms' W' R' ∧
      SigmaOK R₁ (passL1 ms₁ W₁) := by
  obtain ⟨ks₁, p, rfl, hl⟩ := split_fulls ks
  obtain ⟨ms₁, W₁, R₁, h₁, h₂⟩ := split ks₁ h
  exact ⟨ks₁, p, ms₁, W₁, R₁, rfl, hl, h₁, h₂, sigma_fulls p h₂ (sigma_close hc)⟩

/-- A chain of full passes only that ends in a closing class has R³/L₁² ≤ 176³/256² at its start. -/
theorem sigma_all_full (h : LoopChain ms W R ks ms' W' R') (hc : InCloseClass ms' W' R')
    (hf : ∀ k ∈ ks, k = .full) : SigmaOK R (passL1 ms W) := by
  have e : ks = List.replicate ks.length .full := List.eq_replicate_iff.mpr ⟨rfl, hf⟩
  rw [e] at h
  exact sigma_fulls _ h (sigma_close hc)

/-- **From a wide pass start, a close makes no round-7 break.**  A chain from a pass start of width W ≥ 2²⁴ that ends
in a closing class at `ms' W'` with right end R′ is p full passes, with R = 16^p R′ and L₁ = 64^p L₁′; or a half pass
(from W ≡ 2 mod 4) and then p full passes, with R = 2 · 16^p R′ and 2 · 64^p L₁′ = L₁ + 35 W − 147 R − 60 (L₁ and
L₁′ the left countdowns at the two ends).  Every round-7 break starts from a width at least W, and `SigmaOK` at its
landing would need a width below 2²⁴ (`break7_sigma`). -/
theorem close_wide (h : LoopChain ms W R ks ms' W' R') (hc : InCloseClass ms' W' R') (hW : 2 ^ 24 ≤ W) :
    ∃ p, (ks = List.replicate p .full ∧ R = 16 ^ p * R' ∧ passL1 ms W = 64 ^ p * passL1 ms' W') ∨
      (ks = .half :: List.replicate p .full ∧ W % 4 = 2 ∧ R = 2 * 16 ^ p * R' ∧
        2 * 64 ^ p * passL1 ms' W' = passL1 ms W + 35 * (W : Int) - 147 * (R : Int) - 60) := by
  obtain ⟨ks₁, p, rfl, hl, ms₁, W₁, R₁, h₁, h₂, hσ⟩ :
      ∃ ks₁ p, ks = ks₁ ++ List.replicate p .full ∧ (ks₁ = [] ∨ ∃ ks₀ k, ks₁ = ks₀ ++ [k] ∧ k ≠ .full) ∧
        ∃ ms₁ W₁ R₁, LoopChain ms W R ks₁ ms₁ W₁ R₁ ∧ LoopChain ms₁ W₁ R₁ (List.replicate p .full) ms' W' R' ∧
          SigmaOK R₁ (passL1 ms₁ W₁) := by
    obtain ⟨ks₁, p, ms₁, W₁, R₁, e, hl, h₁, h₂, hσ⟩ := h.sigma hc
    exact ⟨ks₁, p, e, hl, ms₁, W₁, R₁, h₁, h₂, hσ⟩
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
      | break7 => exact absurd (break7_sigma hP₀ hmap hσ) (by omega)
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
