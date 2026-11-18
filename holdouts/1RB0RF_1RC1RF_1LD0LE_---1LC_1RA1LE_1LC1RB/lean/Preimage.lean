import Doucette
import PowMod

/-!
# 1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB: the last step before a halt

The machine halts iff Doucette's sequence `Dorb` (6, 10, 15, 24, ...) reaches a power of two
(`halts_iff_doucette`).  With `D = 2^v (2a + 1)` the rule `D' = D + a + v + 2` gives
`(2a + 1)(2^(v+1) + 1) + 2v + 4 = 2^(n+1) + 1`, and modulo `q = 2^(v+1) + 1` the powers of two are `±2^i`
(`PowMod.pow_mod`).  So (`last_step`) a term steps onto `2^n` only if

* `v = 2` and `n ≡ 3 (mod 6)`, or
* `v = 3` and `n ≡ 6 (mod 8)`;

the exception `D = 3 · 2^v` (v even, positive) never steps onto a power of two.  This is the "j ∈ {2, 3}" argument of
the README, now in Lean.  Hence **the sequence never reaches `2^n` unless `n ≡ 3 (mod 6)` or `n ≡ 6 (mod 8)`**
(`halting_exponent`): 17 of every 24 exponents are ruled out.
-/

namespace H144815

open PowMod

set_option maxHeartbeats 4000000 in
/-- **The last step before a halt.** -/
theorem last_step (D n : Nat) (hD : 3 ≤ D) (h : G D = some (2 ^ n)) :
    (val 2 D = 2 ∧ n % 6 = 3) ∨ (val 2 D = 3 ∧ n % 8 = 6) := by
  obtain ⟨hs, ho⟩ := part_spec 2 D (by omega) (by omega)
  generalize hv : val 2 D = v at hs h ⊢
  generalize hE : part 2 D = E at hs ho h
  unfold G at h
  rw [hv, hE] at h
  split at h
  · cases h
  have hP : 2 ^ (v + 1) = 2 * 2 ^ v := by rw [Nat.pow_succ]; omega
  split at h
  · -- the exception: (3D + 3v + 10)/2 lies strictly between 2^(v+2) and 2^(v+3)
    rename_i hx
    obtain ⟨h3, hv2, hv0⟩ := hx
    simp only [Option.some.injEq] at h
    subst h3
    have hP2 : 2 ^ (v + 1 + 1) = 4 * 2 ^ v := by rw [Nat.pow_succ, hP]; omega
    have hP3 : 2 ^ (v + 1 + 1 + 1) = 8 * 2 ^ v := by rw [Nat.pow_succ, hP2]; omega
    have hge : 2 ≤ v := by omega
    have : 3 * v + 10 < 7 * 2 ^ v := by
      have := Nat.lt_two_pow_self (n := v)
      have h4 : 4 ≤ 2 ^ v := by
        have := Nat.pow_le_pow_right (show 1 ≤ 2 by omega) hge; simpa using this
      omega
    exact (no_pow_between (v + 1 + 1) n (by omega) (by omega)).elim
  simp only [Option.some.injEq] at h
  obtain ⟨a, rfl⟩ : ∃ a, E = 2 * a + 1 := ⟨E / 2, by omega⟩
  have hq : 2 ^ (v + 1) * (2 * a + 1) = 2 * D := by rw [hP, Nat.mul_assoc, hs]
  have eq : (2 * a + 1) * (2 ^ (v + 1) + 1) + (2 * v + 4) = 2 ^ (n + 1) + 1 := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm, hq, Nat.pow_succ]
    have : (2 * a + 1) / 2 = a := by omega
    rw [this] at h; omega
  have k := key 2 v (n + 1) _ _ 1 (by omega) eq
  obtain ⟨hsplit, hi⟩ := split v (n + 1)
  generalize hi' : (n + 1) % (v + 1) = i at k hsplit hi
  generalize hj' : (n + 1) / (v + 1) = j at k hsplit
  have t1 : 1 ≤ 2 ^ i := Nat.pow_pos (by omega)
  have t2 : 2 ^ i ≤ 2 ^ v := Nat.pow_le_pow_right (by omega) hi
  rcases (show v ≤ 3 ∨ 4 ≤ v by omega) with hs3 | hs4
  · clear h hs hq eq hE ho hP
    rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega) with rfl | rfl | rfl | rfl <;>
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
    by_cases hj : j % 2 = 0 <;>
    simp only [hj, ↓reduceIte, Nat.reducePow, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod,
      Nat.reduceLeDiff, Nat.zero_add, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.one_mul, true_and]
      at k t2 hsplit ⊢ <;> omega
  · have := pow_ge v hs4
    have hw : 2 * v + 4 < 2 ^ (v + 1) + 1 := by omega
    rw [Nat.mod_eq_of_lt hw] at k
    split at k
    · rw [Nat.mod_eq_of_lt (by omega)] at k
      have i0 : i = 0 := two_pow_odd i (by omega)
      subst i0; simp at k <;> omega
    · by_cases i0 : i = 0
      · subst i0; simp at k <;> omega
      · have t3 : 2 ≤ 2 ^ i := by
          have := Nat.pow_le_pow_right (show 1 ≤ 2 by omega) (show 1 ≤ i by omega); simpa using this
        rw [Nat.mod_eq_of_lt (by omega)] at k
        omega

theorem Dorb_ge : ∀ k D, Dorb k = some D → 6 ≤ D := by
  intro k
  induction k with
  | zero => intro D h; cases h; omega
  | succ k ih =>
    intro D h
    unfold Dorb at h ih
    rw [oit_succ'] at h
    cases hk : oit G k (some 6) with
    | none => rw [hk] at h; cases h
    | some D0 => rw [hk] at h; exact Nat.le_trans (ih D0 hk) (G_ge D0 D h)

/-- **Halting exponents.**  The sequence reaches `2^n` only if `n ≡ 3 (mod 6)` or `n ≡ 6 (mod 8)`. -/
theorem halting_exponent (k n : Nat) (h : Dorb k = some (2 ^ n)) : n % 6 = 3 ∨ n % 8 = 6 := by
  cases k with
  | zero =>
    exfalso
    have h6 : 2 ^ n = 6 := by simp [Dorb, oit] at h; omega
    exact no_pow_between 2 n (by omega) (by omega)
  | succ k =>
    unfold Dorb at h
    rw [oit_succ'] at h
    cases hk : oit G k (some 6) with
    | none => rw [hk] at h; cases h
    | some D =>
      rw [hk] at h
      have hD := Dorb_ge k D hk
      rcases last_step D n (by omega) h with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega

end H144815
