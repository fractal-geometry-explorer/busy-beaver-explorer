/-!
# Powers of `b` modulo `b^(v+1) + 1`

`b^(v+1) ≡ −1`, so the powers of `b` modulo `q = b^(v+1) + 1` are exactly `b^i` and `q − b^i` for `i ≤ v`
(`pow_mod`).  This is the whole arithmetic behind the "last step before halting" lemmas.
-/

namespace PowMod

theorem if_pos_eq {c : Prop} [Decidable c] {α : Type} {x y : α} (h : c) : (if c then x else y) = x := by simp [h]
theorem if_neg_eq {c : Prop} [Decidable c] {α : Type} {x y : α} (h : ¬ c) : (if c then x else y) = y := by simp [h]

theorem pow_le_pow (b : Nat) (hb : 1 ≤ b) {i v : Nat} (h : i ≤ v) : b ^ i ≤ b ^ v :=
  Nat.pow_le_pow_right hb h

theorem pow_pos' (b i : Nat) (hb : 1 ≤ b) : 1 ≤ b ^ i := Nat.pow_pos hb

/-- One more factor `b^(v+1)`: `t ↦ q − t` modulo `q`. -/
theorem mul_mod_q (P t B : Nat) (hB : B % (P + 1) = t) (ht1 : 1 ≤ t) (ht : t ≤ P) :
    (P * B) % (P + 1) = P + 1 - t := by
  rw [Nat.mul_mod, hB, Nat.mod_eq_of_lt (show P < P + 1 by omega)]
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have e : P * (s + 1) = s * (P + 1) + (P + 1 - (s + 1)) := by
    rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_comm P s]; omega
  rw [e, Nat.mul_comm s, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- **Powers of `b` modulo `b^(v+1) + 1`.** -/
theorem pow_mod (b v : Nat) (hb : 2 ≤ b) (i : Nat) (hi : i ≤ v) : ∀ j,
    b ^ ((v + 1) * j + i) % (b ^ (v + 1) + 1) = if j % 2 = 0 then b ^ i else b ^ (v + 1) + 1 - b ^ i := by
  have h1 : 1 ≤ b ^ i := Nat.pow_pos (by omega)
  have h2 : b ^ i ≤ b ^ v := Nat.pow_le_pow_right (by omega) hi
  have h3 : b ^ v < b ^ (v + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  intro j
  induction j with
  | zero =>
    rw [Nat.mul_zero, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]; rfl
  | succ j ih =>
    have e : b ^ ((v + 1) * (j + 1) + i) = b ^ (v + 1) * b ^ ((v + 1) * j + i) := by
      rw [← Nat.pow_add]; congr 1; rw [Nat.mul_succ]; omega
    rw [e]
    by_cases hj : j % 2 = 0
    · simp only [hj, ↓reduceIte] at ih
      rw [mul_mod_q _ _ _ ih h1 (by omega), if_neg_eq (show ¬ (j + 1) % 2 = 0 by omega)]
    · simp only [hj, ↓reduceIte] at ih
      rw [mul_mod_q _ _ _ ih (by omega) (by omega), if_pos_eq (show (j + 1) % 2 = 0 by omega)]
      omega

/-- Every exponent splits as `(v+1) j + i` with `i ≤ v`. -/
theorem split (v n : Nat) : n = (v + 1) * (n / (v + 1)) + n % (v + 1) ∧ n % (v + 1) ≤ v :=
  ⟨(Nat.div_add_mod n (v + 1)).symm, by have := Nat.mod_lt n (show 0 < v + 1 by omega); omega⟩

/-- `b^n mod (b^(v+1)+1)` in closed form, with `i = n mod (v+1)` and `j = n / (v+1)`. -/
theorem pow_mod' (b v n : Nat) (hb : 2 ≤ b) :
    b ^ n % (b ^ (v + 1) + 1) =
      if (n / (v + 1)) % 2 = 0 then b ^ (n % (v + 1)) else b ^ (v + 1) + 1 - b ^ (n % (v + 1)) := by
  obtain ⟨e, hi⟩ := split v n
  conv => lhs; rw [e]
  exact pow_mod b v hb _ hi _

/-- `2^i` is odd only for `i = 0`. -/
theorem two_pow_odd (i : Nat) (h : 2 ^ i % 2 = 1) : i = 0 := by
  cases i with
  | zero => rfl
  | succ i => rw [Nat.pow_succ, Nat.mul_mod_left] at h; cases h

/-- `3^i ≡ 0 (mod 3)` for `i ≥ 1`. -/
theorem three_pow_mod (i : Nat) (h : 1 ≤ i) : 3 ^ i % 3 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [Nat.pow_succ, Nat.mul_mod_left]

theorem lin_lt_pow (v : Nat) : v < 2 ^ v := Nat.lt_two_pow_self

/-- `2^v ≥ 2v + 3` from `v = 4` on. -/
theorem pow_ge (v : Nat) (h : 4 ≤ v) : 2 * v + 3 ≤ 2 ^ v := by
  induction v with
  | zero => omega
  | succ v ih =>
    by_cases h4 : v = 3
    · subst h4; decide
    · have := ih (by omega); rw [Nat.pow_succ]; omega

/-- `2·3^v ≥ 3v + 13` from `v = 2` on... (used in base 3). -/
theorem pow3_ge (v : Nat) (h : 2 ≤ v) : 3 * v + 13 ≤ 2 * 3 ^ v + 1 := by
  induction v with
  | zero => omega
  | succ v ih =>
    by_cases h2 : v = 1
    · subst h2; decide
    · have := ih (by omega); rw [Nat.pow_succ]; omega

/-- No power of two lies strictly between `2^k` and `2^(k+1)`. -/
theorem no_pow_between (k n : Nat) (h1 : 2 ^ k < 2 ^ n) (h2 : 2 ^ n < 2 ^ (k + 1)) : False := by
  have a := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).1 h1
  have b := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).1 h2
  omega

end PowMod

namespace PowMod

theorem mod_two (x q : Nat) (h : x < 2 * q) : x % q = if x < q then x else x - q := by
  by_cases hx : x < q
  · rw [if_pos_eq hx, Nat.mod_eq_of_lt hx]
  · rw [if_neg_eq hx, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- **The key congruence.**  If `u · q + w = b^n + c` with `q = b^(v+1) + 1`, then `w ≡ ±b^i + c (mod q)`, where
`n = (v+1) j + i`, the sign being `+` for even `j`. -/
theorem key (b v n u w c : Nat) (hb : 2 ≤ b) (h : u * (b ^ (v + 1) + 1) + w = b ^ n + c) :
    w % (b ^ (v + 1) + 1) =
      ((if (n / (v + 1)) % 2 = 0 then b ^ (n % (v + 1)) else b ^ (v + 1) + 1 - b ^ (n % (v + 1))) + c)
        % (b ^ (v + 1) + 1) := by
  have h1 : (u * (b ^ (v + 1) + 1) + w) % (b ^ (v + 1) + 1) = (b ^ n + c) % (b ^ (v + 1) + 1) := by rw [h]
  rw [Nat.mul_comm u, Nat.mul_add_mod, Nat.add_mod (b ^ n), pow_mod' b v n hb] at h1
  rw [h1, Nat.add_mod_mod]

end PowMod
