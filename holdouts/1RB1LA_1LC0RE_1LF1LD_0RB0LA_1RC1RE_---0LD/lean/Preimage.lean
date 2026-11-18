import Collatz

/-!
# Space Needle: the last step before a halt

The machine halts iff some term of Doucette's sequence `Fit` is a power of two (`halts_iff_pow2`).  Which `D` step
onto `2^n`?  With `D = 2^v (2a + 1)`, `F D = D + v + 3a` gives

    (2a + 1) (2^(v+1) + 3) + 2v = 2^(n+1) + 3,

so `2^(n+1) ≡ 2v − 3 (mod 2^(v+1) + 3)` (`last_step_congr`).  Unlike the other four machines of the family
(modulus `2^(v+1) + 1`, where the powers of two are just `±2^i`), here the residue of `2^(n+1)` is spread over the
whole cyclic group, so the condition does not bound `v`; it only puts `n` in one class modulo the order of 2.  For
the first valuations (`last_step_small`):

| v | modulus | condition |
|---|---|---|
| 0 | 5 | n ≡ 0 (mod 4) |
| 1 | 7 | impossible |
| 2 | 11 | n ≡ 9 (mod 10) |
| 3 | 19 | n ≡ 12 (mod 18) |
| 4 | 35 | impossible |
| 5 | 67 | n ≡ 22 (mod 66) |
| 6 | 131 | n ≡ 13 (mod 130) |
| 7 | 259 | impossible |
| 8 | 515 | n ≡ 98 (mod 204) |

(computed further in `tools/doucette`: v = 9, 10, 12, 13, 18, 19, ... are impossible as well).
-/

namespace H101957

/-- Powers of 2 modulo `q` repeat with period `p` once `2^p ≡ 1`. -/
theorem pow_mod_period (q p m : Nat) (hp : 2 ^ p % q = 1) : 2 ^ m % q = 2 ^ (m % p) % q := by
  conv => lhs; rw [← Nat.div_add_mod m p, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, hp]
  simp

/-- **The congruence of the last step.**  If `F D = 2^n` then
`(2^(n+1) + 3) ≡ 2 v (mod 2^(v+1) + 3)`, `v = v2 D`. -/
theorem last_step_congr (D n : Nat) (hD : 6 ≤ D) (h : F D = 2 ^ n) :
    (2 ^ (n + 1) + 3) % (2 ^ (v2 D + 1) + 3) = (2 * v2 D) % (2 ^ (v2 D + 1) + 3) := by
  obtain ⟨hs, ho⟩ := odd_spec D (by omega)
  unfold F at h
  generalize hv : v2 D = v at hs h ⊢
  generalize hE : odd D = E at hs ho h
  obtain ⟨a, rfl⟩ : ∃ a, E = 2 * a + 1 := ⟨E / 2, by omega⟩
  have hP : 2 ^ (v + 1) = 2 * 2 ^ v := by rw [Nat.pow_succ]; omega
  have hq : 2 ^ (v + 1) * (2 * a + 1) = 2 * D := by rw [hP, Nat.mul_assoc, hs]
  have eq : (2 * a + 1) * (2 ^ (v + 1) + 3) + 2 * v = 2 ^ (n + 1) + 3 := by
    rw [Nat.mul_add, Nat.mul_comm, hq, Nat.pow_succ]
    have : (2 * a + 1) / 2 = a := by omega
    rw [this] at h; omega
  rw [← eq, Nat.mul_comm, Nat.mul_add_mod]

/-- The class of `n` for one valuation `c`, from a finite check of `2^t mod q` over a period. -/
theorem class_of (q p c e n : Nat) (hp : 2 ^ p % q = 1) (hp0 : 0 < p)
    (hchk : ∀ t < p, (2 ^ t % q + 3) % q = (2 * c) % q → t = e)
    (h : (2 ^ (n + 1) + 3) % q = (2 * c) % q) : (n + 1) % p = e := by
  apply hchk _ (Nat.mod_lt _ hp0)
  rw [← pow_mod_period q p (n + 1) hp, ← h, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

theorem none_of (q p c n : Nat) (hp : 2 ^ p % q = 1) (hp0 : 0 < p)
    (hchk : ∀ t < p, (2 ^ t % q + 3) % q ≠ (2 * c) % q)
    (h : (2 ^ (n + 1) + 3) % q = (2 * c) % q) : False := by
  apply hchk _ (Nat.mod_lt (n + 1) hp0)
  rw [← pow_mod_period q p (n + 1) hp, ← h, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

/-- **The last step, for v ≤ 8.** -/
theorem last_step_small (D n : Nat) (hD : 6 ≤ D) (h : F D = 2 ^ n) :
    (v2 D = 0 → n % 4 = 0) ∧ v2 D ≠ 1 ∧ (v2 D = 2 → n % 10 = 9) ∧ (v2 D = 3 → n % 18 = 12) ∧ v2 D ≠ 4 ∧
    (v2 D = 5 → n % 66 = 22) ∧ (v2 D = 6 → n % 130 = 13) ∧ v2 D ≠ 7 ∧ (v2 D = 8 → n % 204 = 98) := by
  have k := last_step_congr D n hD h
  generalize v2 D = v at k ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro hv <;> subst hv
  · have := class_of 5 4 0 1 n (by decide) (by decide) (by decide +kernel) k; omega
  · exact none_of 7 3 1 n (by decide) (by decide) (by decide +kernel) k
  · have := class_of 11 10 2 0 n (by decide) (by decide) (by decide +kernel) k; omega
  · have := class_of 19 18 3 13 n (by decide) (by decide) (by decide +kernel) k; omega
  · exact none_of 35 12 4 n (by decide) (by decide) (by decide +kernel) k
  · have := class_of 67 66 5 23 n (by decide) (by decide) (by decide +kernel) k; omega
  · have := class_of 131 130 6 14 n (by decide) (by decide) (by decide +kernel) k; omega
  · exact none_of 259 36 7 n (by decide) (by decide) (by decide +kernel) k
  · have := class_of 515 204 8 99 n (by decide) (by decide) (by decide +kernel) k; omega

end H101957
