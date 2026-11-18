import Doucette
import PowMod

/-!
# 1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE: the last step before a halt

The machine halts iff Doucette's sequence `Dorb` reaches a power of two (`halts_iff_doucette`).  Which values can step
onto `2^n`?  Writing `D = 2^v (2a + 1)`, the rule `D' = D + a + v` gives `(2a + 1)(2^(v+1) + 1) + 2v = 2^(n+1) + 1`,
and modulo `q = 2^(v+1) + 1` the powers of two are `±2^i` (`PowMod.pow_mod`).  That leaves only two ways in
(`last_step`):

* `v = 0` and `n` even (`D = (2^(n+1) + 1)/3`), or
* `v = 1` and `n ≡ 3 (mod 4)` (`D = 2(2^(n+1) − 1)/5`);

the exception `D = 3 · 2^v` never steps onto a power of two.  So **the sequence never reaches `2^n` with
`n ≡ 1 (mod 4)`** (`no_pow2_one_mod_four`), and a halt needs a term `≡ 1 (mod 2)` or `≡ 2 (mod 4)` of one of the two
forms just before it.  This is the "dangerous families" lemma of the wiki (Aristotle), with both families exact.
-/

namespace H31371

open PowMod

theorem three_two_pow_not_pow2 (v n : Nat) (hv : 1 ≤ v) (h : 2 ^ v * 3 + v + 3 = 2 ^ n) : False := by
  have hP : 2 ^ (v + 1) = 2 * 2 ^ v := by rw [Nat.pow_succ]; omega
  have hP2 : 2 ^ (v + 1 + 1) = 4 * 2 ^ v := by rw [Nat.pow_succ, hP]; omega
  by_cases h4 : 4 ≤ v
  · have := pow_ge v h4
    exact no_pow_between (v + 1) n (by omega) (by omega)
  · have : v = 1 ∨ v = 2 ∨ v = 3 := by omega
    rcases this with rfl | rfl | rfl
    · exact no_pow_between 3 n (by simp at h; omega) (by simp at h; omega)
    · exact no_pow_between 4 n (by simp at h; omega) (by simp at h; omega)
    · exact no_pow_between 4 n (by simp at h; omega) (by simp at h; omega)

/-- **The last step before a halt.**  If `G D = 2^n` then `v2 D = 0` and `n` is even, or `v2 D = 1` and
`n ≡ 3 (mod 4)`. -/
theorem last_step (D n : Nat) (hD : 5 ≤ D) (h : G D = some (2 ^ n)) :
    (val 2 D = 0 ∧ n % 2 = 0) ∨ (val 2 D = 1 ∧ n % 4 = 3) := by
  obtain ⟨hs, ho⟩ := part_spec 2 D (by omega) (by omega)
  generalize hv : val 2 D = v at hs h ⊢
  generalize hE : part 2 D = E at hs ho h
  unfold G at h
  rw [hv, hE] at h
  split at h
  · cases h
  split at h
  · simp only [Option.some.injEq] at h
    subst_vars
    have hv1 : 1 ≤ v := by
      cases v with
      | zero => simp at hD
      | succ v => omega
    exact (three_two_pow_not_pow2 v n hv1 (by omega)).elim
  simp only [Option.some.injEq] at h
  obtain ⟨a, rfl⟩ : ∃ a, E = 2 * a + 1 := ⟨E / 2, by omega⟩
  have hP : 2 ^ (v + 1) = 2 * 2 ^ v := by rw [Nat.pow_succ]; omega
  have hq : 2 ^ (v + 1) * (2 * a + 1) = 2 * D := by rw [hP, Nat.mul_assoc, hs]
  have eq : (2 * a + 1) * (2 ^ (v + 1) + 1) + 2 * v = 2 ^ (n + 1) + 1 := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm, hq, Nat.pow_succ]
    have : (2 * a + 1) / 2 = a := by omega
    rw [this] at h; omega
  have k := key 2 v (n + 1) _ _ 1 (by omega) eq
  have hvq : 2 * v < 2 ^ (v + 1) + 1 := by have := Nat.lt_two_pow_self (n := v); omega
  rw [Nat.mod_eq_of_lt hvq] at k
  obtain ⟨hsplit, hi⟩ := split v (n + 1)
  generalize hi' : (n + 1) % (v + 1) = i at k hsplit hi
  generalize hj' : (n + 1) / (v + 1) = j at k hsplit
  have t1 : 1 ≤ 2 ^ i := Nat.pow_pos (by omega)
  have t2 : 2 ^ i ≤ 2 ^ v := Nat.pow_le_pow_right (by omega) hi
  have lv := Nat.lt_two_pow_self (n := v)
  split at k
  · -- j even: 2v = 2^i + 1, so 2^i is odd, i = 0 and v = 1
    rw [Nat.mod_eq_of_lt (by omega)] at k
    have i0 : i = 0 := two_pow_odd i (by omega)
    subst i0
    have v1 : v = 1 := by simp at k; omega
    subst v1
    right; refine ⟨rfl, ?_⟩
    omega
  · -- j odd
    by_cases i0 : i = 0
    · subst i0
      simp at k
      have : v = 0 := by omega
      subst this
      left; refine ⟨rfl, ?_⟩
      simp at hsplit; omega
    · have t3 : 2 ≤ 2 ^ i := by
        have := Nat.pow_le_pow_right (show 1 ≤ 2 by omega) (show 1 ≤ i by omega); simpa using this
      rw [Nat.mod_eq_of_lt (by omega)] at k
      rcases (show v ≤ 3 ∨ 4 ≤ v by omega) with hs3 | hs4
      · rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega) with rfl | rfl | rfl | rfl <;> simp at * <;> omega
      · have := pow_ge v hs4; omega

/-- **Halting exponents.**  After the start, the sequence never equals `2^n` with `n ≡ 1 (mod 4)`. -/
theorem no_pow2_one_mod_four (k n : Nat) (hn : n % 4 = 1) : Dorb (k + 1) ≠ some (2 ^ n) := by
  intro h
  unfold Dorb at h
  rw [oit_succ'] at h
  cases hk : oit G k (some 5) with
  | none => rw [hk] at h; cases h
  | some D =>
    rw [hk] at h
    have hD : 5 ≤ D := by
      have : ∀ k D, oit G k (some 5) = some D → 5 ≤ D := by
        intro k
        induction k with
        | zero => intro D h; cases h; omega
        | succ k ih =>
          intro D h
          rw [oit_succ'] at h
          cases hk' : oit G k (some 5) with
          | none => rw [hk'] at h; cases h
          | some D0 => rw [hk'] at h; exact Nat.le_trans (ih D0 hk') (G_ge D0 D h)
      exact this k D hk
    rcases last_step D n hD h with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega

end H31371
