import Doucette
import PowMod

/-!
# 1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB: the last step before a halt (base 3)

The machine halts iff the sequence `Dorb` reaches `(3^n, r)` with `n + r ≡ 1 (mod 3)` (`halts_iff_doucette`).
Which states `(D, r)` step onto a power of three?  With `D = 3^v (3a + ρ)`, `ρ ∈ {1, 2}`, the rule
`D' = D + a + v + r + ρ + 1` gives `(3a + ρ)(3^(v+1) + 1) + 3v + 3r + 2ρ + 3 = 3^(n+1)`, and modulo
`q = 3^(v+1) + 1` the powers of three are `±3^i` (`PowMod.pow_mod`); the left side is `2ρ ≢ 0 (mod 3)` off a multiple
of `q`.  So (`last_step`), for `r ∈ {1, 2}`, the next `r` is 1 and

* `r = 1`: `v = 1`, and `n ≡ 3 (mod 4)` if `ρ = 1`, `n ≡ 0 (mod 4)` if `ρ = 2`;
* `r = 2`: `v = 0` (`n` even if `ρ = 1`, odd if `ρ = 2`), or `v = 2`, `ρ = 2` and `n ≡ 4 (mod 6)`;

and a pure power of three (the exception) never steps onto another.  With `r = 1` the halt at `(3^n, 1)` needs
`3 ∣ n`, so (`halt_from_r1`) **the term before a halt has exactly one factor 3 and `n ≡ 0` or `3 (mod 12)`**.
-/

namespace H86694

open PowMod

theorem pow3_inj (n m : Nat) (h : 3 ^ n = 3 ^ m) : n = m := by
  rcases Nat.lt_trichotomy n m with hl | he | hg
  · have := Nat.pow_lt_pow_right (show 1 < 3 by omega) hl; omega
  · exact he
  · have := Nat.pow_lt_pow_right (show 1 < 3 by omega) hg; omega

theorem no_pow3_between (k n : Nat) (h1 : 3 ^ k < 3 ^ n) (h2 : 3 ^ n < 3 ^ (k + 1)) : False := by
  have a := (Nat.pow_lt_pow_iff_right (by omega : 1 < 3)).1 h1
  have b := (Nat.pow_lt_pow_iff_right (by omega : 1 < 3)).1 h2
  omega

theorem pow3_ge' (v : Nat) (h : 3 ≤ v) : 3 * v + 14 ≤ 2 * 3 ^ v := by
  induction v with
  | zero => omega
  | succ v ih =>
    by_cases h2 : v = 2
    · subst h2; decide
    · have := ih (by omega); rw [Nat.pow_succ]; omega

set_option maxHeartbeats 8000000 in
/-- **The last step before a halt.** -/
theorem last_step (D r n r' : Nat) (hD : 2 ≤ D) (hr : r = 1 ∨ r = 2) (h : G (D, r) = some (3 ^ n, r')) :
    r' = 1 ∧
    ((r = 1 ∧ val 3 D = 1 ∧ ((part 3 D % 3 = 1 ∧ n % 4 = 3) ∨ (part 3 D % 3 = 2 ∧ n % 4 = 0))) ∨
     (r = 2 ∧ ((val 3 D = 0 ∧ ((part 3 D % 3 = 1 ∧ n % 2 = 0) ∨ (part 3 D % 3 = 2 ∧ n % 2 = 1))) ∨
               (val 3 D = 2 ∧ part 3 D % 3 = 2 ∧ n % 6 = 4)))) := by
  obtain ⟨hs, ho⟩ := part_spec 3 D (by omega) (by omega)
  generalize hv : val 3 D = v at hs h ⊢
  generalize hE : part 3 D = E at hs ho h ⊢
  unfold G at h
  simp only at h
  rw [hv, hE] at h
  have hP : 3 ^ (v + 1) = 3 * 3 ^ v := by rw [Nat.pow_succ]; omega
  have hp1 : 1 ≤ 3 ^ v := Nat.pow_pos (by omega)
  split at h
  · -- D is a power of three: the next value lies strictly between 3^v and 3^(v+1)
    exfalso
    rename_i h1
    subst h1
    have hv1 : 1 ≤ v := by
      cases v with
      | zero => simp at hs; omega
      | succ v => omega
    have hl : v < 3 ^ v := Nat.lt_pow_self (show 1 < 3 by omega)
    have h3v : 3 ≤ 3 ^ v := by
      have := Nat.pow_le_pow_right (show 1 ≤ 3 by omega) hv1; simpa using this
    rw [Nat.mul_one] at hs
    split at h
    · cases h
    split at h
    all_goals
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h, -⟩ := h
      exact no_pow3_between v n (by omega) (by omega)
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨h, rfl⟩ := h
  refine ⟨rfl, ?_⟩
  obtain ⟨a, ρ, rfl, hρ⟩ : ∃ a ρ, E = 3 * a + ρ ∧ (ρ = 1 ∨ ρ = 2) := ⟨E / 3, E % 3, by omega, by omega⟩
  have hρ' : (3 * a + ρ) % 3 = ρ := by omega
  have hρ3 : (3 * a + ρ) / 3 = a := by omega
  rw [hρ', hρ3] at h
  rw [hρ']
  have hq : 3 ^ (v + 1) * (3 * a + ρ) = 3 * D := by rw [hP, Nat.mul_assoc, hs]
  have eq : (3 * a + ρ) * (3 ^ (v + 1) + 1) + (3 * v + 3 * r + 2 * ρ + 3) = 3 ^ (n + 1) + 0 := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm, hq, Nat.pow_succ]; omega
  have k := key 3 v (n + 1) _ _ 0 (by omega) eq
  simp only [Nat.add_zero] at k
  obtain ⟨hsplit, hi⟩ := split v (n + 1)
  generalize hi' : (n + 1) % (v + 1) = i at k hsplit hi
  generalize hj' : (n + 1) / (v + 1) = j at k hsplit
  have t1 : 1 ≤ 3 ^ i := Nat.pow_pos (by omega)
  have t2 : 3 ^ i ≤ 3 ^ v := Nat.pow_le_pow_right (by omega) hi
  rcases (show v ≤ 2 ∨ 3 ≤ v by omega) with hs2 | hs3
  · clear h hs hq eq hE ho hP hρ' hρ3 hp1
    rcases (show v = 0 ∨ v = 1 ∨ v = 2 by omega) with rfl | rfl | rfl <;>
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl <;>
    by_cases hj : j % 2 = 0 <;>
    simp only [hj, ↓reduceIte, Nat.reducePow, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod,
      Nat.reduceLeDiff, Nat.zero_add, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.one_mul, true_and]
      at k t2 hsplit ⊢ <;> omega
  · exfalso
    have := pow3_ge v (by omega)
    have h3 : 3 ^ v ≥ 27 := by
      have := Nat.pow_le_pow_right (show 1 ≤ 3 by omega) hs3; simpa using this
    have hw : 3 * v + 3 * r + 2 * ρ + 3 < 3 ^ (v + 1) + 1 := by omega
    rw [Nat.mod_eq_of_lt hw] at k
    split at k
    · rw [Nat.mod_eq_of_lt (by omega)] at k
      by_cases i0 : i = 0
      · subst i0; simp at k <;> omega
      · have := three_pow_mod i (by omega); omega
    · have h31 := three_pow_mod (v + 1) (by omega)
      by_cases i0 : i = 0
      · subst i0
        simp at k
        first
          | omega
          | (rw [Nat.mod_eq_of_lt (by omega)] at k; omega)
      · have h3i := three_pow_mod i (by omega)
        have hst : 3 * v + 14 ≤ 2 * 3 ^ v := pow3_ge' v hs3
        rw [Nat.mod_eq_of_lt (by omega)] at k
        omega

/-- **The step before a halt, from `r = 1`.**  If `(D, 1)` steps onto `(3^n, r')` and `(3^n, r')` halts, then `D`
has exactly one factor 3 and `n ≡ 0` or `3 (mod 12)`. -/
theorem halt_from_r1 (D n r' : Nat) (hD : 2 ≤ D) (h : G (D, 1) = some (3 ^ n, r'))
    (hh : G (3 ^ n, r') = none) : val 3 D = 1 ∧ (n % 12 = 0 ∨ n % 12 = 3) := by
  obtain ⟨rfl, hc⟩ := last_step D 1 n r' hD (Or.inl rfl) h
  have hpow := (val_part 3 (by omega) n 1 (by omega))
  rw [Nat.mul_one] at hpow
  have h31 : (n + 1) % 3 = 1 := by
    unfold G at hh; simp only [hpow.1, hpow.2, ↓reduceIte] at hh
    by_cases c1 : (n + 1) % 3 = 1
    · exact c1
    · simp only [c1, ↓reduceIte] at hh; split at hh <;> cases hh
  rcases hc with ⟨_, hv, hc⟩ | ⟨h2, _⟩
  · exact ⟨hv, by omega⟩
  · omega

end H86694
