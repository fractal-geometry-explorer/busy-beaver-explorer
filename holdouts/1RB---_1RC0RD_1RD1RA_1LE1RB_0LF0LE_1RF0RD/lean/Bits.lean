import Count

/-!
# Numbers as bit lists, and counts in numbers

`bitsOf w v` is the `w` lowest bits of `v`, lowest first.  With it the left string and the counters of
`Count.lean` become numbers: `count_nat` is one count (the left string `bitsOf (w+1) v` gains 2), `count_many` is
`n` counts of a counter `bitsOf l c` with any tape `T` after it.
-/

namespace H140108

open TM

/-- The `w` lowest bits of `v`, lowest first. -/
def bitsOf : Nat → Nat → List Bool
  | 0, _ => []
  | w + 1, v => (v % 2 == 1) :: bitsOf w (v / 2)

theorem bitsOf_succ (w v : Nat) : bitsOf (w + 1) v = (v % 2 == 1) :: bitsOf w (v / 2) := rfl

theorem length_bitsOf : ∀ (w v : Nat), (bitsOf w v).length = w
  | 0, _ => rfl
  | w + 1, v => by simp [bitsOf, length_bitsOf w (v / 2)]

theorem pow_succ' (w : Nat) : 2 ^ (w + 1) = 2 * 2 ^ w := by
  rw [Nat.pow_succ]; omega

theorem pow_pos' (w : Nat) : 0 < 2 ^ w := Nat.pow_pos (by omega)

theorem bitsOf_inc : ∀ (w v : Nat), v + 1 < 2 ^ w → inc (bitsOf w v) = bitsOf w (v + 1)
  | 0, v, h => by simp at h
  | w + 1, v, h => by
    rw [pow_succ'] at h
    rcases Nat.mod_two_eq_zero_or_one v with h0 | h1
    · have e1 : (v + 1) % 2 = 1 := by omega
      have e2 : (v + 1) / 2 = v / 2 := by omega
      rw [bitsOf_succ, bitsOf_succ, h0, e1, e2]; rfl
    · have e1 : (v + 1) % 2 = 0 := by omega
      have e2 : (v + 1) / 2 = v / 2 + 1 := by omega
      rw [bitsOf_succ, bitsOf_succ, h1, e1, e2]
      show false :: inc (bitsOf w (v / 2)) = _
      rw [bitsOf_inc w (v / 2) (by omega)]; rfl

theorem false_mem_bitsOf : ∀ (w v : Nat), v + 1 < 2 ^ w → false ∈ bitsOf w v
  | 0, v, h => by simp at h
  | w + 1, v, h => by
    rw [pow_succ'] at h
    rw [bitsOf_succ]
    rcases Nat.mod_two_eq_zero_or_one v with h0 | h1
    · rw [h0]; simp
    · rw [h1]; exact List.mem_cons_of_mem _ (false_mem_bitsOf w (v / 2) (by omega))

theorem bitsOf_full : ∀ (w : Nat), bitsOf w (2 ^ w - 1) = List.replicate w true
  | 0 => rfl
  | w + 1 => by
    have h := pow_pos' w
    rw [bitsOf_succ, pow_succ']
    have e1 : (2 * 2 ^ w - 1) % 2 = 1 := by omega
    have e2 : (2 * 2 ^ w - 1) / 2 = 2 ^ w - 1 := by omega
    rw [e1, e2, bitsOf_full w]; rfl

theorem bitsOf_zero : ∀ (w : Nat), bitsOf w 0 = List.replicate w false
  | 0 => rfl
  | w + 1 => by rw [bitsOf_succ, bitsOf_zero w]; rfl

theorem bitsOf_pow : ∀ (l : Nat), bitsOf (l + 1) (2 ^ l) = List.replicate l false ++ [true]
  | 0 => rfl
  | l + 1 => by
    rw [bitsOf_succ, pow_succ']
    have e1 : (2 * 2 ^ l) % 2 = 0 := by omega
    have e2 : (2 * 2 ^ l) / 2 = 2 ^ l := by omega
    rw [e1, e2, bitsOf_pow l]; rfl

/-- The `m+1` bits of `2^(m+1) - 2 + b`: the bit `b`, then `m` ones. -/
theorem bitsOf_top (m : Nat) (b : Bool) :
    bitsOf (m + 1) (2 ^ (m + 1) - 2 + (if b then 1 else 0)) = b :: List.replicate m true := by
  have h := pow_pos' m
  rw [bitsOf_succ, pow_succ']
  cases b with
  | false =>
    have e1 : (2 * 2 ^ m - 2 + 0) % 2 = 0 := by omega
    have e2 : (2 * 2 ^ m - 2 + 0) / 2 = 2 ^ m - 1 := by omega
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [e1, e2, bitsOf_full]; rfl
  | true =>
    have e1 : (2 * 2 ^ m - 2 + 1) % 2 = 1 := by omega
    have e2 : (2 * 2 ^ m - 2 + 1) / 2 = 2 ^ m - 1 := by omega
    simp only [↓reduceIte]
    rw [e1, e2, bitsOf_full]; rfl

/-- `bitsOf a x ++ bitsOf b y` is `bitsOf (a + b) (x + 2^a y)` when `x < 2^a`. -/
theorem bitsOf_append : ∀ (a b x y : Nat), x < 2 ^ a → bitsOf (a + b) (x + 2 ^ a * y) = bitsOf a x ++ bitsOf b y
  | 0, b, x, y, h => by simp at h; subst h; simp [bitsOf]
  | a + 1, b, x, y, h => by
    rw [pow_succ'] at h
    rw [show a + 1 + b = (a + b) + 1 by omega, bitsOf_succ, bitsOf_succ, pow_succ']
    have e1 : (x + 2 * 2 ^ a * y) % 2 = x % 2 := by
      rw [Nat.mul_assoc, Nat.add_mul_mod_self_left]
    have e2 : (x + 2 * 2 ^ a * y) / 2 = x / 2 + 2 ^ a * y := by
      rw [Nat.mul_assoc, Nat.add_mul_div_left _ _ (by omega)]
    rw [e1, e2, bitsOf_append a b (x / 2) y (by omega)]
    rfl

theorem bitsOf_cons (w v : Nat) (b : Bool) :
    bitsOf (w + 1) ((if b then 1 else 0) + 2 * v) = b :: bitsOf w v := by
  rw [bitsOf_succ]
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    rw [Nat.mul_mod_right, Nat.mul_div_cancel_left _ (by omega)]; rfl
  | true =>
    simp only [↓reduceIte]
    have e1 : (1 + 2 * v) % 2 = 1 := by omega
    have e2 : (1 + 2 * v) / 2 = v := by omega
    rw [e1, e2]; rfl

/-- **One count, in numbers.**  The left string `bitsOf (w+1) v` gains 2 (its lowest bit is left alone). -/
theorem count_nat (w v : Nat) (hv : v + 2 < 2 ^ (w + 1)) (ds : List Bool) (hd : false ∈ ds) (L T : Tape) :
    Reach ⟨enc (false :: bitsOf (w + 1) v) L, ctr ds T, .B⟩
      ⟨enc (false :: bitsOf (w + 1) (v + 2)) L, ctr (inc ds) T, .B⟩ := by
  rw [pow_succ'] at hv
  have e1 : (v + 2) % 2 = v % 2 := by omega
  have e2 : (v + 2) / 2 = v / 2 + 1 := by omega
  rw [bitsOf_succ, bitsOf_succ, e1, e2, ← bitsOf_inc w (v / 2) (by omega)]
  exact count _ _ ds (false_mem_bitsOf w (v / 2) (by omega)) hd L T

/-- **`n` counts.**  A counter `bitsOf l c` (any tape `T` after it) gains `n` and the left string `2n`. -/
theorem count_many (w v l c : Nat) (L T : Tape) : ∀ n : Nat, v + 2 * n < 2 ^ (w + 1) → c + n < 2 ^ l →
    Reach ⟨enc (false :: bitsOf (w + 1) v) L, ctr (bitsOf l c) T, .B⟩
      ⟨enc (false :: bitsOf (w + 1) (v + 2 * n)) L, ctr (bitsOf l (c + n)) T, .B⟩
  | 0, _, _ => Reach.refl' _
  | n + 1, hv, hc => by
    refine Reach.trans' (count_many w v l c L T n (by omega) (by omega)) ?_
    have h := count_nat w (v + 2 * n) (by omega) (bitsOf l (c + n)) (false_mem_bitsOf l (c + n) (by omega)) L T
    rw [bitsOf_inc l (c + n) (by omega)] at h
    rw [show v + 2 * (n + 1) = v + 2 * n + 2 by omega, show c + (n + 1) = c + n + 1 by omega]
    exact h

end H140108
