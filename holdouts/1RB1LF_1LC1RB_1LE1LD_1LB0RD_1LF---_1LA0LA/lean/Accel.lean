/-!
# The arithmetic of the level-stripping accelerator

The accelerator (`py/lsa`) treats a ladder of levels as a mixed-radix counter and an eater phase as a run of
K identical blocks.  Its two counting laws are proved here for all values.

* `first_pass`: a level whose cycle has length `p` and passes one hit per cycle, at position `t` (1 ≤ t ≤ p),
  makes its `m`-th pass at its hit number `p * (m - 1) + t`.  So a chain of such levels needs an affine number
  of hits at the top, and a block of four base-4 levels multiplies by 256.
* `blocks_closed`: the hits needed above a run of K blocks.  Block i (counted from the bottom, i = 0 for the
  newest) passes on what block i - 1 needs plus the P hits of one super-cycle; with the block's map
  x ↦ (c + 1) x + b this is the recursion `blocks`, and its closed form is a geometric sum.
-/

namespace Accel

/-- hits that must enter the run from above: `blocks c b P Z k` for the block k places above the newest one,
when the region below the run must receive `Z` more hits; the block map is `x ↦ (c + 1) * x + b`. -/
def blocks (c b P Z : Nat) : Nat → Nat
  | 0 => (c + 1) * Z + b
  | k + 1 => (c + 1) * (P + blocks c b P Z k) + b

theorem blocks_closed (c b P Z : Nat) : ∀ k : Nat,
    c * blocks c b P Z k + ((c + 1) * P + b) = (c + 1) ^ k * (c * ((c + 1) * Z + b) + ((c + 1) * P + b))
  | 0 => by simp [blocks]
  | k + 1 => by
    have ih := blocks_closed c b P Z k
    have e : c * blocks c b P Z (k + 1) + ((c + 1) * P + b)
        = (c + 1) * (c * blocks c b P Z k + ((c + 1) * P + b)) := by
      simp only [blocks, Nat.mul_add, Nat.add_mul, Nat.one_mul]
      simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [e, ih, Nat.pow_succ, Nat.mul_comm ((c + 1) ^ k) (c + 1), Nat.mul_assoc]

/-- with b = 0 (all eaters seen so far) and c = 255 (a block of four base-4 levels):
255 * blocks + 256 P = 256^k * (255 * 256 * Z + 256 P). -/
theorem blocks_256 (P Z k : Nat) :
    255 * blocks 255 0 P Z k + 256 * P = 256 ^ k * (255 * (256 * Z) + 256 * P) := by
  have h := blocks_closed 255 0 P Z k
  simpa using h

/-- The m-th pass (m ≥ 1) of a level with cycle length p that passes once per cycle at position t. -/
def first_pass (p t m : Nat) : Nat := p * (m - 1) + t

/-- hits passed by the first q hits of such a level, from the start of its cycle -/
def passes (p t q : Nat) : Nat := if q < t then 0 else (q - t) / p + 1

theorem first_pass_correct (p t m : Nat) (hp : 0 < p) (ht : 1 ≤ t) (_htp : t ≤ p) (hm : 1 ≤ m) :
    passes p t (first_pass p t m) = m ∧ passes p t (first_pass p t m - 1) = m - 1 := by
  unfold passes first_pass
  constructor
  · have h1 : ¬ (p * (m - 1) + t < t) := by omega
    simp only [h1, ↓reduceIte]
    have : p * (m - 1) + t - t = p * (m - 1) := by omega
    rw [this, Nat.mul_div_cancel_left _ hp]; omega
  · by_cases h : p * (m - 1) + t - 1 < t
    · simp only [h, ↓reduceIte]
      have : p * (m - 1) < 1 := by omega
      have : m - 1 = 0 := by
        cases Nat.eq_zero_or_pos (m - 1) with
        | inl h0 => exact h0
        | inr hpos => exact absurd (Nat.mul_le_mul_left p hpos) (by omega)
      omega
    · simp only [h, ↓reduceIte]
      have hm1 : 1 ≤ m - 1 := by
        cases Nat.eq_zero_or_pos (m - 1) with
        | inl h0 => rw [h0] at h; omega
        | inr hpos => exact hpos
      have e : p * (m - 1) + t - 1 - t = p * (m - 2) + (p - 1) := by
        have : p * (m - 1) = p * (m - 2) + p := by
          have : m - 1 = (m - 2) + 1 := by omega
          rw [this, Nat.mul_succ]
        omega
      rw [e]
      have : (p * (m - 2) + (p - 1)) / p = m - 2 := by
        rw [Nat.add_comm, Nat.add_mul_div_left _ _ hp]
        have : (p - 1) / p = 0 := Nat.div_eq_of_lt (by omega)
        omega
      omega

end Accel
