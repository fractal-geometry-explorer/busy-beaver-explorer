import Doucette
import PowMod

/-!
# 1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC: the last step before a halt

The machine halts iff Doucette's sequence `Dorb` reaches a power of two (`halts_iff_doucette`).  Which states
`(D, r)` step onto `(2^n, ·)`?  With `D = 2^v (2a + 1)` the rule `D' = D + a + v + r` gives
`(2a + 1)(2^(v+1) + 1) + 2v + 2r = 2^(n+1) + 1`, and modulo `q = 2^(v+1) + 1` the powers of two are `±2^i`
(`PowMod.pow_mod`).  So (`last_step`), for `r ∈ {1, 2}`:

* `r = 1`: `v = 0` and `n` odd, or `v = 1` and `n ≡ 2 (mod 4)`, or `v = 2` and `n ≡ 4 (mod 6)`;
* `r = 2`: `v = 2` and `n ≡ 3 (mod 6)`, or `v = 3` and `n ≡ 6 (mod 8)`;
* the exception `D = 3 · 2^v` steps onto a power of two only from `(12, 1)` (to 16).

`r` is always 1 or 2 along the sequence (`Dorb_r`).  Hence **the sequence never reaches `2^n` with `n ≡ 0` or
`8 (mod 12)`** (`no_pow2_mod_twelve`, for `n > 4`).
-/

namespace H53489

open PowMod

theorem pow2_inj (n m : Nat) (h : 2 ^ n = 2 ^ m) : n = m := by
  rcases Nat.lt_trichotomy n m with hl | he | hg
  · have := Nat.pow_lt_pow_right (show 1 < 2 by omega) hl; omega
  · exact he
  · have := Nat.pow_lt_pow_right (show 1 < 2 by omega) hg; omega

theorem ite21 (c : Prop) [Decidable c] : (if c then 2 else 1) = 1 ∨ (if c then 2 else 1) = 2 := by
  by_cases h : c <;> simp [h]

theorem three_two_pow_cases (v r n : Nat) (hv : 1 ≤ v) (hr : r = 1 ∨ r = 2)
    (h : 2 ^ v * 3 + v + r + 1 = 2 ^ n) : v = 2 ∧ r = 1 ∧ n = 4 := by
  have hP : 2 ^ (v + 1) = 2 * 2 ^ v := by rw [Nat.pow_succ]; omega
  have hP2 : 2 ^ (v + 1 + 1) = 4 * 2 ^ v := by rw [Nat.pow_succ, hP]; omega
  by_cases h4 : 4 ≤ v
  · have := pow_ge v h4
    exact (no_pow_between (v + 1) n (by omega) (by omega)).elim
  · have : v = 1 ∨ v = 2 ∨ v = 3 := by omega
    rcases this with rfl | rfl | rfl
    · exact (no_pow_between 3 n (by simp at h; omega) (by simp at h; omega)).elim
    · rcases hr with rfl | rfl
      · simp at h
        exact ⟨rfl, rfl, pow2_inj n 4 (by simpa using h.symm)⟩
      · exact (no_pow_between 4 n (by simp at h; omega) (by simp at h; omega)).elim
    · exact (no_pow_between 4 n (by simp at h; omega) (by simp at h; omega)).elim

set_option maxHeartbeats 4000000 in
/-- **The last step before a halt.** -/
theorem last_step (D r n r' : Nat) (hD : 4 ≤ D) (hr : r = 1 ∨ r = 2) (h : G (D, r) = some (2 ^ n, r')) :
    (D = 12 ∧ r = 1 ∧ n = 4) ∨
    (r = 1 ∧ ((val 2 D = 0 ∧ n % 2 = 1) ∨ (val 2 D = 1 ∧ n % 4 = 2) ∨ (val 2 D = 2 ∧ n % 6 = 4))) ∨
    (r = 2 ∧ ((val 2 D = 2 ∧ n % 6 = 3) ∨ (val 2 D = 3 ∧ n % 8 = 6))) := by
  obtain ⟨hs, ho⟩ := part_spec 2 D (by omega) (by omega)
  generalize hv : val 2 D = v at hs h ⊢
  generalize hE : part 2 D = E at hs ho h
  unfold G at h
  simp only at h
  rw [hv, hE] at h
  split at h
  · cases h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    subst_vars
    have hv1 : 1 ≤ v := by
      cases v with
      | zero => simp at hD
      | succ v => omega
    obtain ⟨rfl, rfl, rfl⟩ := three_two_pow_cases v r n hv1 hr (by omega)
    left; simp
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨h, -⟩ := h
  right
  obtain ⟨a, rfl⟩ : ∃ a, E = 2 * a + 1 := ⟨E / 2, by omega⟩
  have hP : 2 ^ (v + 1) = 2 * 2 ^ v := by rw [Nat.pow_succ]; omega
  have hq : 2 ^ (v + 1) * (2 * a + 1) = 2 * D := by rw [hP, Nat.mul_assoc, hs]
  have eq : (2 * a + 1) * (2 ^ (v + 1) + 1) + (2 * v + 2 * r) = 2 ^ (n + 1) + 1 := by
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
  · -- small v: finitely many cases
    clear h hs hq eq hE ho hP
    rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega) with rfl | rfl | rfl | rfl <;>
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
    by_cases hj : j % 2 = 0 <;>
    simp only [hj, ↓reduceIte, Nat.reducePow, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod,
      Nat.reduceLeDiff, Nat.zero_add, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.one_mul, true_and] at k t2 hsplit ⊢ <;> omega
  · have := pow_ge v hs4
    have hw : 2 * v + 2 * r < 2 ^ (v + 1) + 1 := by omega
    rw [Nat.mod_eq_of_lt hw] at k
    split at k
    · rw [Nat.mod_eq_of_lt (by omega)] at k
      have i0 : i = 0 := two_pow_odd i (by omega)
      subst i0; simp at k; omega
    · by_cases i0 : i = 0
      · subst i0; simp at k; omega
      · have t3 : 2 ≤ 2 ^ i := by
          have := Nat.pow_le_pow_right (show 1 ≤ 2 by omega) (show 1 ≤ i by omega); simpa using this
        rw [Nat.mod_eq_of_lt (by omega)] at k
        omega

/-- Along the sequence `D ≥ 4` and `r ∈ {1, 2}`. -/
theorem Dorb_r : ∀ k D r, Dorb k = some (D, r) → 4 ≤ D ∧ (r = 1 ∨ r = 2) := by
  intro k
  induction k with
  | zero => intro D r h; cases h; omega
  | succ k ih =>
    intro D r h
    unfold Dorb at h ih
    rw [oit_succ'] at h
    cases hk : oit G k (some (5, 2)) with
    | none => rw [hk] at h; cases h
    | some x =>
      rw [hk] at h
      obtain ⟨D0, r0⟩ := x
      change G (D0, r0) = some (D, r) at h
      obtain ⟨h1, _⟩ := ih D0 r0 hk
      have := G_inv (D0, r0) (D, r) ⟨h1, by omega⟩ h
      refine ⟨this.1, ?_⟩
      unfold G at h; try simp only at h
      split at h
      · cases h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h; exact ite21 _
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨_, rfl⟩ := h; simp

/-- **Halting exponents.**  The sequence never reaches `2^n` with `n > 4` and `n ≡ 0` or `8 (mod 12)`. -/
theorem no_pow2_mod_twelve (k n r : Nat) (hn4 : 4 < n) (hn : n % 12 = 0 ∨ n % 12 = 8) :
    Dorb (k + 1) ≠ some (2 ^ n, r) := by
  intro h
  unfold Dorb at h
  rw [oit_succ'] at h
  cases hk : oit G k (some (5, 2)) with
  | none => rw [hk] at h; cases h
  | some x =>
    rw [hk] at h
    obtain ⟨D, r0⟩ := x
    change G (D, r0) = some (2 ^ n, r) at h
    obtain ⟨hD, hr⟩ := Dorb_r k D r0 hk
    rcases last_step D r0 n r hD hr h with ⟨_, _, h3⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega

end H53489
