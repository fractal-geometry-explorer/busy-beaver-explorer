import Rules

/-!
# 1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC: many visits at once

Away from the resets, `op` (in `Rules.lean`) is one of two affine maps, chosen by one "digit":

    grow (digit true):   (a, b) ↦ (2a + 4, b - a - 1)  if a is even,  (2a + 3, b - a)  if a is odd
    swap (digit false):  (a, b) ↦ (a - b + 1, 2b + 3)

In `d = b - a`, `s = a + b` these are `d ↦ 2d - s + c`, `d ↦ 2d + s + 2`: a doubling map on `d / s`, the grow/swap
digits being the binary expansion of `(1 + d / s) / 2` up to small carries.  `c/abfast.c` guesses K digits at once
from that expansion (K up to 48), applies them with tables, and keeps the result only if both coordinates end at
least `16 * 2^K`.  `block_ok` is why that is safe for *any* guessed digits: `drun` applies the two maps formally
on integers (no side conditions), and if the formal run ends with both coordinates at least `16 * 2^K`, it is the
orbit of `op` (`opIter`) for those K visits.  `block_far` adds that none of those visits has `1 ≤ b - a ≤ 27`, so
none is near the halting diagonal `b - a = 4` (or a reset), and the run's log of near visits misses nothing.

The proof: one formal step at most doubles `min a b` plus 4 (`dstep_min`), so a large final minimum forces
`min a b ≥ 28` after every formal step (`drun_back`); and a formal step that ends with both coordinates at least 28
starts from a visit where `op` is that same step (`dstep_op`).
-/

namespace H8084

/-- One formal step on integers: `true` is grow, `false` is swap. -/
def dstep : Bool → Int × Int → Int × Int
  | true, (a, b) => if a % 2 = 0 then (2 * a + 4, b - a - 1) else (2 * a + 3, b - a)
  | false, (a, b) => (a - b + 1, 2 * b + 3)

/-- The formal run of a list of digits. -/
def drun : List Bool → Int × Int → Int × Int
  | [], x => x
  | g :: L, x => drun L (dstep g x)

theorem dstep_sum (g : Bool) (a b : Int) : (dstep g (a, b)).1 + (dstep g (a, b)).2 ≥ a + b + 3 := by
  cases g
  · simp only [dstep]; omega
  · by_cases hp : a % 2 = 0 <;> simp only [dstep, hp, ite_true, ite_false] <;> omega

/-- A formal step at most doubles the smaller coordinate plus 4 (when `a + b ≥ 0`). -/
theorem dstep_min (g : Bool) (a b T : Int) (hs : 0 ≤ a + b)
    (h1 : T ≤ (dstep g (a, b)).1) (h2 : T ≤ (dstep g (a, b)).2) : T ≤ 2 * a + 4 ∧ T ≤ 2 * b + 4 := by
  cases g
  · simp only [dstep] at h1 h2; omega
  · by_cases hp : a % 2 = 0 <;> simp only [dstep, hp, ite_true, ite_false] at h1 h2 <;> omega

/-- Backwards along a formal run: a final minimum of at least `2^n (X + 4) - 4` needs a minimum of at least X
    at the start. -/
theorem drun_back : ∀ (L : List Bool) (a b X : Int), 0 ≤ a + b →
    2 ^ L.length * (X + 4) ≤ (drun L (a, b)).1 + 4 → 2 ^ L.length * (X + 4) ≤ (drun L (a, b)).2 + 4 →
    X ≤ a ∧ X ≤ b
  | [], a, b, X, _, h1, h2 => by simp [drun] at h1 h2; omega
  | g :: L, a, b, X, hs, h1, h2 => by
    simp only [drun, List.length_cons] at h1 h2
    rcases hf : dstep g (a, b) with ⟨a1, b1⟩
    have hs1 := dstep_sum g a b
    rw [hf] at h1 h2 hs1
    have hp : (2 : Int) ^ (L.length + 1) * (X + 4) = 2 ^ L.length * ((2 * X + 4) + 4) := by
      rw [Int.pow_succ, Int.mul_assoc, show (2 * X + 4) + 4 = 2 * (X + 4) by omega]
    rw [hp] at h1 h2
    obtain ⟨k1, k2⟩ := drun_back L a1 b1 (2 * X + 4) (by simp at hs1; omega) h1 h2
    have := dstep_min g a b (2 * X + 4) hs (by rw [hf]; exact k1) (by rw [hf]; exact k2)
    omega

/-- A formal step that ends with both coordinates at least 28 is the step of `op`. -/
theorem dstep_op (g : Bool) (a b : Nat) (h1 : 28 ≤ (dstep g ((a : Int), (b : Int))).1)
    (h2 : 28 ≤ (dstep g ((a : Int), (b : Int))).2) :
    op (a, b) = some ((dstep g (a, b)).1.toNat, (dstep g (a, b)).2.toNat) ∧ (b ≤ a ∨ a + 28 ≤ b) := by
  cases g
  · simp only [dstep] at h1 h2 ⊢
    refine ⟨?_, by omega⟩
    simp only [op]
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    congr 2 <;> omega
  · simp only [dstep] at h1 h2 ⊢
    by_cases hp : (a : Int) % 2 = 0
    · simp only [hp, ite_true] at h1 h2 ⊢
      refine ⟨?_, by omega⟩
      simp only [op]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega)]
      congr 2 <;> omega
    · simp only [hp, ite_false] at h1 h2 ⊢
      refine ⟨?_, by omega⟩
      simp only [op]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega)]
      congr 2 <;> omega

/-- The block check of `c/abfast.c`: whatever digits were guessed, if their formal run from a visit `(a, b)` ends
    with both coordinates at least `16 * 2^K`, then the next K visits are that formal run. -/
theorem block_ok : ∀ (L : List Bool) (a b : Nat),
    16 * 2 ^ L.length ≤ (drun L (a, b)).1 → 16 * 2 ^ L.length ≤ (drun L (a, b)).2 →
    opIter L.length (a, b) = some ((drun L (a, b)).1.toNat, (drun L (a, b)).2.toNat)
  | [], a, b, _, _ => by simp [drun, opIter]
  | g :: L, a, b, h1, h2 => by
    simp only [drun, List.length_cons] at h1 h2 ⊢
    rcases hf : dstep g ((a : Int), (b : Int)) with ⟨a1, b1⟩
    have hs1 := dstep_sum g a b
    rw [hf] at h1 h2 hs1
    rw [Int.pow_succ] at h1 h2
    have hpos : (0 : Int) < 2 ^ L.length := Int.pow_pos (by decide)
    obtain ⟨k1, k2⟩ := drun_back L a1 b1 28 (by simp at hs1; omega) (by simp only [show (28 : Int) + 4 = 32 from rfl]; omega)
      (by simp only [show (28 : Int) + 4 = 32 from rfl]; omega)
    have ho := (dstep_op g a b (by rw [hf]; exact k1) (by rw [hf]; exact k2)).1
    rw [hf] at ho
    have e1 : ((a1.toNat : Nat) : Int) = a1 := Int.toNat_of_nonneg (by omega)
    have e2 : ((b1.toNat : Nat) : Int) = b1 := Int.toNat_of_nonneg (by omega)
    have ih := block_ok L a1.toNat b1.toNat (by rw [e1, e2]; omega) (by rw [e1, e2]; omega)
    rw [e1, e2] at ih
    simp only [opIter, ho, Option.bind_some]
    exact ih

/-- No visit inside an accepted block is near the diagonal: each has `b ≤ a` or `b ≥ a + 28`.  (Visit j of the
    block, j < K, is `opIter j (a, b)`; it is the start of the formal run of the remaining digits.) -/
theorem block_far : ∀ (L : List Bool) (a b : Nat),
    16 * 2 ^ L.length ≤ (drun L (a, b)).1 → 16 * 2 ^ L.length ≤ (drun L (a, b)).2 →
    ∀ j, j < L.length → ∀ a' b', opIter j (a, b) = some (a', b') → b' ≤ a' ∨ a' + 28 ≤ b'
  | [], _, _, _, _, j, hj, _, _, _ => by simp at hj
  | g :: L, a, b, h1, h2, j, hj, a', b', hy => by
    simp only [drun, List.length_cons] at h1 h2 hj
    rcases hf : dstep g ((a : Int), (b : Int)) with ⟨a1, b1⟩
    have hs1 := dstep_sum g a b
    rw [hf] at h1 h2 hs1
    rw [Int.pow_succ] at h1 h2
    have hpos : (0 : Int) < 2 ^ L.length := Int.pow_pos (by decide)
    obtain ⟨k1, k2⟩ := drun_back L a1 b1 28 (by simp at hs1; omega) (by simp only [show (28 : Int) + 4 = 32 from rfl]; omega)
      (by simp only [show (28 : Int) + 4 = 32 from rfl]; omega)
    have hop := dstep_op g a b (by rw [hf]; exact k1) (by rw [hf]; exact k2)
    rw [hf] at hop
    cases j with
    | zero => simp only [opIter, Option.some.injEq, Prod.mk.injEq] at hy; obtain ⟨rfl, rfl⟩ := hy; exact hop.2
    | succ j =>
      have e1 : ((a1.toNat : Nat) : Int) = a1 := Int.toNat_of_nonneg (by omega)
      have e2 : ((b1.toNat : Nat) : Int) = b1 := Int.toNat_of_nonneg (by omega)
      simp only [opIter, hop.1, Option.bind_some] at hy
      exact block_far L a1.toNat b1.toNat (by rw [e1, e2]; omega) (by rw [e1, e2]; omega) j (by omega) a' b' hy

end H8084
