import Pass

/-!
# A second exact quantity: the alternating sum ψ

For a block list `y₁ … y_k` (first block first), `ψ = y_k − 2 y_(k−1) + 4 y_(k−2) − …`: with the list nearest first,
as `next` reads it, `ψ (y :: ys) = y − 2 ψ ys`.  A pass changes it by an exact rule (`psi_next`):

    2 ψ' = −ψ + 3 (−2)^n − 7

where n is the number of blocks the sweep crosses before it stops (n = 0 when the last block is even, and the sweep
always crosses an odd last block, so n ≥ 1 otherwise).  Together with `next_sum` (the ones go up by 4) this is a
second linear quantity the pass map moves by a rule that depends only on n.  On a two-block state `[a, 2a+d]`,
ψ = d.  It is the parity information that a bound on block sizes alone lacks (`notes/LAB_NOTES.md`, 1 November):
the halving loop of the small starts needs |ψ| large, while ψ stays small along the orbit (computed).

Found by the thread "Find the provable first-block bound" (checked there by sympy for k ≤ 12 and on all lists of up
to 6 blocks); proved here for every block list, kernel only.
-/

namespace BB6d

/-- `ψ`, nearest block first: `ψ (y :: ys) = y − 2 ψ ys`. -/
def psi : List Nat → Int
  | [] => 0
  | y :: ys => (y : Int) - 2 * psi ys

/-- The correction a zigzag through the recorded `gs` makes to `ψ`. -/
def zagC : List Nat → Int
  | [] => 0
  | g :: gs => zagC gs + (-2) ^ gs.length * (-(g : Int) - 4)

theorem lc2 (P a : Int) : P * (2 * a) = 2 * (P * a) := Int.mul_left_comm _ _ _
theorem lc4 (P a : Int) : P * (4 * a) = 4 * (P * a) := Int.mul_left_comm _ _ _
theorem rc2 (P : Int) : P * 2 = 2 * P := Int.mul_comm _ _
theorem rc4 (P : Int) : P * 4 = 4 * P := Int.mul_comm _ _

/-- Bring a product with `P` to the form `c * (P * x)` so that `omega` sees `P * x` as one atom. -/
macro "pnorm" P:term : tactic => `(tactic| simp only [Int.mul_add, Int.mul_sub, Int.mul_neg, Int.neg_mul, Int.mul_one,
  lc2 $P, lc4 $P, rc2 $P, rc4 $P, Int.mul_assoc] at *)

theorem psi_bump (k : Nat) (ys : List Nat) : psi ((bump k ys).1 :: (bump k ys).2) = psi ys - k := by
  match ys with
  | [] => simp only [bump, psi]; omega
  | [b] => simp only [bump, psi]; push_cast; omega
  | b :: a :: ms => simp only [bump, psi]; push_cast; omega

theorem psi_zag (gs : List Nat) : ∀ (q : Nat) (ms : List Nat),
    psi (zag q ms gs) = zagC gs + (-2) ^ gs.length * psi (q :: ms) := by
  induction gs with
  | nil => intro q ms; simp [zag, zagC]
  | cons g gs ih =>
    intro q ms
    simp only [zag, ih, zagC, List.length_cons, psi]
    rw [Int.pow_succ]
    generalize (-2 : Int) ^ gs.length = P
    push_cast
    pnorm P
    omega

/-- The sweep moves `ψ` by the rule, with `Z` what the blocks already crossed contribute. -/
theorem psi_sweep (ys : List Nat) : ∀ (gs : List Nat) (out : List Nat) (Z : Int),
    sweep gs ys = .ok out → Z + 2 * zagC gs = 2 * (-2) ^ gs.length - 7 →
    ∃ n : Nat, n ≤ gs.length + ys.length ∧ 2 * psi out + Z + (-2) ^ gs.length * psi ys = 3 * (-2) ^ n - 7 := by
  induction ys with
  | nil => intro gs out Z h; simp [sweep] at h
  | cons y ys ih =>
    intro gs out Z h hZ
    unfold sweep at h
    by_cases hy : y % 2 = 0
    · rw [if_pos hy] at h
      by_cases h0 : y = 0
      · rw [if_pos h0] at h; cases h
      rw [if_neg h0] at h
      have hZ' : (Z + (-2) ^ gs.length * y) + 2 * zagC ((y / 2 - 1) :: gs)
          = 2 * (-2) ^ ((y / 2 - 1) :: gs).length - 7 := by
        simp only [zagC, List.length_cons]
        rw [Int.pow_succ]
        generalize (-2 : Int) ^ gs.length = P at hZ ⊢
        have ey : ((y : Int)) = 2 * ((y / 2 - 1 : Nat) : Int) + 2 := by omega
        rw [ey]
        generalize ((y / 2 - 1 : Nat) : Int) = g
        pnorm P
        omega
      obtain ⟨n, hle, hn⟩ := ih _ out _ h hZ'
      refine ⟨n, by simp only [List.length_cons] at hle ⊢; omega, ?_⟩
      simp only [List.length_cons] at hn
      rw [Int.pow_succ] at hn
      simp only [psi]
      generalize (-2 : Int) ^ gs.length = P at hn ⊢
      generalize (-2 : Int) ^ n = R at hn ⊢
      pnorm P
      omega
    · rw [if_neg hy] at h
      by_cases h1 : y = 1
      · rw [if_pos h1] at h; cases h
      rw [if_neg h1] at h
      cases h
      refine ⟨gs.length, by simp, ?_⟩
      rw [psi_zag, psi_bump]
      simp only [psi]
      generalize (-2 : Int) ^ gs.length = P at hZ ⊢
      have ey : ((y : Int)) = 2 * (((y - 1) / 2 : Nat) : Int) + 1 := by omega
      rw [ey]
      generalize (((y - 1) / 2 : Nat) : Int) = c
      pnorm P
      omega

/-- **The rule for `ψ`**: a pass that gives a block list moves `ψ` by `2 ψ' = −ψ + 3 (−2)^n − 7`, for some `n` at
most the number of blocks (the number of blocks the sweep crosses). -/
theorem psi_next (zs out : List Nat) (h : next zs = .ok out) :
    ∃ n : Nat, n ≤ zs.length ∧ 2 * psi out = -psi zs + 3 * (-2) ^ n - 7 := by
  match zs with
  | [] => simp [next] at h; subst h; exact ⟨0, by decide, by decide⟩
  | y :: ys =>
    rw [next] at h
    by_cases hy : y % 2 = 0
    · rw [if_pos hy] at h
      cases h
      refine ⟨0, by simp, ?_⟩
      rw [psi_bump]
      simp only [psi]
      omega
    · rw [if_neg hy] at h
      obtain ⟨n, hle, hn⟩ := psi_sweep ys [(y + 3) / 2] out y h
        (by simp only [zagC, List.length_nil, List.length_cons]; omega)
      refine ⟨n, by simp only [List.length_cons, List.length_nil] at hle ⊢; omega, ?_⟩
      simp only [List.length_cons, List.length_nil, psi] at hn ⊢
      omega

end BB6d
