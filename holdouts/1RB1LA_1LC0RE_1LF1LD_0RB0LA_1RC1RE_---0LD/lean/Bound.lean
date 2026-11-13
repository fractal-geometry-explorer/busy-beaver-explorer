import Collatz

/-!
# Space Needle: Doucette's sequence checked for a while

`checkF n D` checks that none of `D, F D, ..., F^(n-1) D` is a power of two.  The kernel runs it for the first
20,000 terms (numbers up to about 19,000 bits); compiled code (`native_decide`) for the first 300,000 (up to
about 282,000 bits).  These are floors, not a proof: the sequence grows like 1.92^k and a power of two would have to be hit exactly.
-/

namespace H101957

def checkF : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, D => (odd D != 1) && checkF n (F D)

theorem checkF_spec (n : Nat) : ∀ k, checkF n (Fit k) = true → ∀ i < n, odd (Fit (k + i)) ≠ 1 := by
  induction n with
  | zero => intro k _ i hi; omega
  | succ n ih =>
    intro k h i hi
    simp only [checkF, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    cases i with
    | zero => exact h.1
    | succ i =>
      have := ih (k + 1) h.2 i (by omega)
      rw [show k + (i + 1) = k + 1 + i by omega]
      exact this

theorem Fit_kernel : ∀ i < 20000, odd (Fit i) ≠ 1 := by
  have := checkF_spec 20000 0 (by decide +kernel)
  simpa using this

theorem Fit_native : ∀ i < 300000, odd (Fit i) ≠ 1 := by
  have := checkF_spec 300000 0 (by native_decide)
  simpa using this

end H101957
