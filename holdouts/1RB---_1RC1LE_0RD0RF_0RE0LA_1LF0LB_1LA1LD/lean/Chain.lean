import MapThm

/-!
# The chain criterion: halting as a number-theory condition on the orbit

A C step with s = 0 maps `(x, m, 0)` (m odd, x >= (m+5)/2) to `(x-(m+5)/2, 2m+7, 0)`, so m+7 doubles and a chain
of C steps with s = 0 runs through `m_i = (m+7) 2^i - 7`, using up `(m_i+5)/2 = (m+7) 2^(i-1) - 1` pairs per step.

* `chain`: from `(x, m, 0)`, m odd, the map makes `j` C steps with s = 0 to `(y, M, 0)` with `M + 7 = (m+7) 2^j`,
  `y + (m+7) 2^j / 2 = x + j + (m+7)/2`, `y < (M+5)/2` (the chain stops there), and `y = 0` iff `x = 0` or
  `x + k + 1 = (m+7)(2^(k+1)-1)/2` for some k.
* `exit_step`: where the chain stops, the next step is H if y = 0, A' to `(2y+3, 1, 0)` if `y = (M+3)/2`, and
  otherwise A to `(2y+1, M+4-2y, 1)`.
* `chain_hit`: if `x + k + 1 = (m+7)(2^(k+1)-1)/2`, then k+1 C steps and H (`iter (k+2) (x, m, 0) = none`).
* `halts_iff_chain`: the machine halts from blank tape iff some orbit point is `(x, m, 0)`, m odd, with
  `x + k + 1 = (m+7)(2^(k+1)-1)/2` for some k; `halts_iff_chain_start`: the same with the point a chain start
  (t = 0 or the previous point does not make a C step with s = 0).
* `crit_m1`, `crit_m3`: for m = 1 the condition is `x = 2^(k+3) - k - 5`, for m = 3 it is `x = 5 2^(k+1) - k - 6`.

Internally `m = 2n+1` and `A_j = (n+4) 2^j`; the chain lemmas are inductions on j.  Written by hand.
-/

namespace H26350

/-- `n` steps of the map from a point; `none` once H is reached. -/
def iter : Nat → Nat × Nat × Bool → Option (Nat × Nat × Bool)
  | 0, p => some p
  | n + 1, (x, m, s) =>
    match mstep x m s with
    | none => none
    | some q => iter n q

theorem two_pow_ge (j : Nat) : j + 1 ≤ 2 ^ j := by
  induction j with
  | zero => decide
  | succ j ih => rw [Nat.pow_succ]; omega

theorem bigA (n j : Nat) : n + 4 + 4 * j ≤ (n + 4) * 2 ^ j := by
  have h1 : (n + 4) * (j + 1) ≤ (n + 4) * 2 ^ j := Nat.mul_le_mul_left _ (two_pow_ge j)
  have h2 : 4 * j ≤ (n + 4) * j := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.mul_succ] at h1
  omega

theorem dblA (n j : Nat) : (n + 4) * 2 ^ (j + 1) = 2 * ((n + 4) * 2 ^ j) := by
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_left_comm]

theorem dblA' (n j : Nat) : (2 * n + 4 + 4) * 2 ^ j = 2 * ((n + 4) * 2 ^ j) := by
  rw [show 2 * n + 4 + 4 = 2 * (n + 4) by omega, Nat.mul_assoc]

theorem cstep0 (x n : Nat) (h : n + 3 ≤ x) :
    mstep x (2 * n + 1) false = some (x - (n + 3), 2 * (2 * n + 4) + 1, false) := by
  unfold mstep
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega), show (2 * n + 1 + 5) / 2 = n + 3 by omega,
    show 2 * (2 * n + 1) + 7 - (if false = true then 1 else 0) = 2 * (2 * n + 4) + 1 by simp; omega]

theorem hstep (n : Nat) (s : Bool) : mstep 0 (2 * n + 1) s = none := by
  unfold mstep
  rw [ite_eq_right (by omega), ite_eq_left rfl]

theorem iter_succ' (j : Nat) : ∀ p, iter (j + 1) p = (iter j p).bind (fun q => mstep q.1 q.2.1 q.2.2) := by
  induction j with
  | zero =>
    intro ⟨x, m, s⟩
    show (match mstep x m s with | none => none | some q => some q) = mstep x m s
    cases mstep x m s <;> rfl
  | succ j ih =>
    intro ⟨x, m, s⟩
    show (match mstep x m s with | none => none | some q => iter (j + 1) q) =
      (match mstep x m s with | none => none | some q => iter j q).bind _
    cases mstep x m s with
    | none => rfl
    | some q => exact ih q

theorem orbit_none_add (t : Nat) (h : orbit t = none) : ∀ n, orbit (t + n) = none := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih => show (match orbit (t + n) with | none => none | some (x, m, s) => mstep x m s) = none; rw [ih]

theorem orbit_add (n : Nat) : ∀ t p, orbit t = some p → orbit (t + n) = iter n p := by
  induction n with
  | zero => intro t p h; exact h
  | succ n ih =>
    intro t ⟨x, m, s⟩ h
    have h1 : orbit (t + 1) = mstep x m s := by show (match orbit t with | none => none | some (x, m, s) => mstep x m s) = _; rw [h]
    rw [show t + (n + 1) = t + 1 + n by omega]
    show _ = (match mstep x m s with | none => none | some q => iter n q)
    cases e : mstep x m s with
    | none => rw [e] at h1; exact orbit_none_add _ h1 n
    | some q => rw [e] at h1; exact ih _ q h1

/-! ## The chain, with `m = 2n+1` and `A_j = (n+4) 2^j` -/

/-- `j` C steps with s = 0, while they apply. -/
theorem chain_steps_n (j : Nat) : ∀ x n, (n + 4) * 2 ^ j ≤ x + j + (n + 4) →
    iter j (x, 2 * n + 1, false) = some (x + j + (n + 4) - (n + 4) * 2 ^ j, 2 * ((n + 4) * 2 ^ j - 4) + 1, false) := by
  induction j with
  | zero => intro x n _; simp only [Nat.pow_zero, Nat.mul_one, iter, Option.some.injEq, Prod.mk.injEq, and_true]; omega
  | succ j ih =>
    intro x n h
    have hA := bigA n j
    rw [dblA] at h ⊢
    have hx : n + 3 ≤ x := by omega
    show (match mstep x (2 * n + 1) false with | none => none | some q => iter j q) = _
    rw [cstep0 x n hx]
    show iter j (x - (n + 3), 2 * (2 * n + 4) + 1, false) = _
    rw [ih (x - (n + 3)) (2 * n + 4) (by rw [dblA']; omega), dblA']
    simp only [Option.some.injEq, Prod.mk.injEq, and_true]
    omega

/-- The chain hits H: `x + j + n + 4 = A_j` gives j C steps, then H. -/
theorem chain_hit_n (j : Nat) : ∀ x n, x + j + (n + 4) = (n + 4) * 2 ^ j → iter (j + 1) (x, 2 * n + 1, false) = none := by
  intro x n h
  rw [iter_succ', chain_steps_n j x n (by omega)]
  show mstep _ _ _ = none
  rw [show x + j + (n + 4) - (n + 4) * 2 ^ j = 0 by omega]
  exact hstep _ _

/-- Every chain stops: a `j` with `A_j <= x + j + n + 4 < A_(j+1) - 1`. -/
theorem exit_exists_n (b : Nat) : ∀ x, x ≤ b → ∀ n, ∃ j, (n + 4) * 2 ^ j ≤ x + j + (n + 4) ∧
    x + j + 1 + (n + 4) < (n + 4) * 2 ^ (j + 1) := by
  induction b with
  | zero =>
    intro x hx n
    refine ⟨0, ?_, ?_⟩ <;> simp only [Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.pow_one] <;> omega
  | succ b ih =>
    intro x hx n
    by_cases hc : x < n + 3
    · refine ⟨0, ?_, ?_⟩ <;> simp only [Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.pow_one] <;> omega
    · obtain ⟨j, h1, h2⟩ := ih (x - (n + 3)) (by omega) (2 * n + 4)
      refine ⟨j + 1, ?_, ?_⟩
      · rw [dblA' n j] at h1; rw [dblA n j]; omega
      · rw [dblA' n (j + 1)] at h2; rw [dblA n (j + 1)]; omega

theorem mono_lt (n i d : Nat) : (n + 4) * 2 ^ i + (i + d + 1) < (n + 4) * 2 ^ (i + d + 1) + i := by
  induction d with
  | zero => have := bigA n i; rw [dblA]; omega
  | succ d ih =>
    have := bigA n (i + d + 1)
    rw [show i + (d + 1) + 1 = i + d + 1 + 1 by omega, dblA]; omega

theorem mono_le (n i i' : Nat) (h : i ≤ i') : (n + 4) * 2 ^ i + i' ≤ (n + 4) * 2 ^ i' + i := by
  rcases Nat.eq_or_lt_of_le h with rfl | hl
  · omega
  · obtain ⟨d, rfl⟩ : ∃ d, i' = i + d + 1 := ⟨i' - i - 1, by omega⟩
    have := mono_lt n i d; omega

theorem crit_eq (n k : Nat) : (2 * n + 1 + 7) * (2 ^ (k + 1) - 1) / 2 + (n + 4) = (n + 4) * 2 ^ (k + 1) := by
  rw [show 2 * n + 1 + 7 = 2 * (n + 4) by omega, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < 2),
    Nat.mul_sub_one]
  have := bigA n (k + 1)
  omega

/-! ## The chain criterion, for odd m -/

/-- Where a chain of C steps with s = 0 stops (m odd, x < (m+5)/2), `mstep` does H if x = 0, A' if
x = (m+3)/2, and A (to s = 1) otherwise. -/
theorem exit_step (y M : Nat) (hM : M % 2 = 1) (hy : y < (M + 5) / 2) :
    mstep y M false = if y = 0 then none else if y + 1 = (M + 5) / 2 then some (2 * y + 3, 1, false)
      else some (2 * y + 1, M + 4 - 2 * y, true) := by
  unfold mstep
  rw [ite_eq_right (by omega)]
  by_cases h0 : y = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
  · rw [ite_eq_right h0, ite_eq_right h0, ite_eq_right (by omega)]
    by_cases h1 : y + 1 = (M + 5) / 2
    · rw [ite_eq_left ⟨h1, rfl⟩, ite_eq_left h1]
    · rw [ite_eq_right (fun h => h1 h.1), ite_eq_right h1]; rfl

/-- The chain from `(x, m, 0)`, m odd: `j` C steps with s = 0 (every point before step `j` is a C step with
s = 0), to `(y, M, 0)` with `M + 7 = (m+7) 2^j` and `y + (m+7) 2^j / 2 = x + j + (m+7)/2`, where the chain stops
(`y < (M+5)/2`; the next step is `exit_step`), and it stops at H (`y = 0`) iff `x = 0` or
`x + k + 1 = (m+7)(2^(k+1)-1)/2` for some k. -/
theorem chain (x m : Nat) (hm : m % 2 = 1) : ∃ j y M,
    (∀ i, i < j → ∃ xi mi, iter i (x, m, false) = some (xi, mi, false) ∧ mi % 2 = 1 ∧ (mi + 5) / 2 ≤ xi) ∧
    iter j (x, m, false) = some (y, M, false) ∧ M % 2 = 1 ∧ y < (M + 5) / 2 ∧
    M + 7 = (m + 7) * 2 ^ j ∧ y + (m + 7) * 2 ^ j / 2 = x + j + (m + 7) / 2 ∧
    iter (j + 1) (x, m, false) = mstep y M false ∧
    (y = 0 ↔ (x = 0 ∨ ∃ k, x + k + 1 = (m + 7) * (2 ^ (k + 1) - 1) / 2)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = 2 * n + 1 := ⟨m / 2, by omega⟩
  obtain ⟨j, h1, h2⟩ := exit_exists_n x x (Nat.le_refl x) n
  have hA := bigA n j
  have hA1 := dblA n j
  have e7 : (2 * n + 1 + 7) * 2 ^ j = 2 * ((n + 4) * 2 ^ j) := by
    rw [show 2 * n + 1 + 7 = 2 * (n + 4) by omega, Nat.mul_assoc]
  refine ⟨j, x + j + (n + 4) - (n + 4) * 2 ^ j, 2 * ((n + 4) * 2 ^ j - 4) + 1, ?_, chain_steps_n j x n h1,
    by omega, by omega, by rw [e7]; omega, by rw [e7]; omega, ?_, ?_⟩
  · intro i hi
    have hl := mono_le n (i + 1) j (by omega)
    have hi1 := dblA n i
    have hAi := bigA n i
    exact ⟨_, _, chain_steps_n i x n (by omega), by omega, by omega⟩
  · rw [iter_succ', chain_steps_n j x n h1]; rfl
  · constructor
    · intro hy
      rcases j with _ | k
      · left; simp only [Nat.pow_zero, Nat.mul_one] at hy; omega
      · right; exact ⟨k, by have := crit_eq n k; omega⟩
    · rintro (rfl | ⟨k, hk⟩)
      · omega
      · have hc := crit_eq n k
        rcases Nat.lt_or_ge j (k + 1) with hj | hj
        · have := mono_le n (j + 1) (k + 1) (by omega)
          omega
        · rcases Nat.eq_or_lt_of_le hj with rfl | hj
          · omega
          · obtain ⟨d, rfl⟩ : ∃ d, j = k + 1 + d + 1 := ⟨j - k - 2, by omega⟩
            have := mono_lt n (k + 1) d
            omega

/-- If `x + k + 1 = (m+7)(2^(k+1)-1)/2` (m odd), the chain from `(x, m, 0)` makes k+1 C steps and then H. -/
theorem chain_hit (x m k : Nat) (hm : m % 2 = 1) (h : x + k + 1 = (m + 7) * (2 ^ (k + 1) - 1) / 2) :
    iter (k + 2) (x, m, false) = none := by
  obtain ⟨n, rfl⟩ : ∃ n, m = 2 * n + 1 := ⟨m / 2, by omega⟩
  have := crit_eq n k
  exact chain_hit_n (k + 1) x n (by omega)

/-- After an R step with s = 0 (m = 1) the criterion reads `x = 2^(k+3) - k - 5`. -/
theorem crit_m1 (x k : Nat) : x + k + 1 = (1 + 7) * (2 ^ (k + 1) - 1) / 2 ↔ x = 2 ^ (k + 3) - k - 5 := by
  have h := crit_eq 0 k
  have hp := two_pow_ge (k + 1)
  rw [show (1 : Nat) + 7 = 2 * 0 + 1 + 7 from rfl, show 2 ^ (k + 3) = 4 * 2 ^ (k + 1) by
    rw [Nat.pow_succ, Nat.pow_succ]; omega]
  omega

/-- After an R step with s = 1 (m = 3) the criterion reads `x = 5 * 2^(k+1) - k - 6`. -/
theorem crit_m3 (x k : Nat) : x + k + 1 = (3 + 7) * (2 ^ (k + 1) - 1) / 2 ↔ x = 5 * 2 ^ (k + 1) - k - 6 := by
  have h := crit_eq 1 k
  have hp := two_pow_ge (k + 1)
  rw [show (3 : Nat) + 7 = 2 * 1 + 1 + 7 from rfl]
  omega

/-! ## Halting from blank tape as the criterion on the orbit -/

theorem mstep_none {x m : Nat} {s : Bool} (h : mstep x m s = none) : x = 0 ∧ m % 2 = 1 := by
  unfold mstep at h
  by_cases he : m % 2 = 0
  · rw [ite_eq_left he] at h; split at h <;> simp at h
  · rw [ite_eq_right he] at h
    by_cases hx : x = 0
    · exact ⟨hx, by omega⟩
    · rw [ite_eq_right hx] at h; split at h <;> (try split at h) <;> simp at h

/-- The only step into a point `(0, m', s')` with m' odd is a C step with s = 0 from `x = (m+5)/2`. -/
theorem pred_zero {x m : Nat} {s : Bool} {m' : Nat} {s' : Bool} (h : mstep x m s = some (0, m', s'))
    (hm : m' % 2 = 1) : s = false ∧ m % 2 = 1 ∧ x = (m + 5) / 2 := by
  unfold mstep at h
  by_cases he : m % 2 = 0
  · rw [ite_eq_left he] at h
    split at h <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;> omega
  · rw [ite_eq_right he] at h
    by_cases hx : x = 0
    · rw [ite_eq_left hx] at h; simp at h
    · rw [ite_eq_right hx] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        cases s
        · exact ⟨rfl, by omega, by omega⟩
        · simp at h; omega
      · split at h <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;> omega

theorem last_some (T : Nat) (hT : orbit T = none) : ∃ t p, orbit t = some p ∧ orbit (t + 1) = none := by
  induction T with
  | zero => simp [orbit] at hT
  | succ T ih =>
    cases e : orbit T with
    | none => exact ih e
    | some p => exact ⟨T, p, e, hT⟩

theorem orbit_succ {t : Nat} {x m : Nat} {s : Bool} (h : orbit t = some (x, m, s)) :
    orbit (t + 1) = mstep x m s := by
  show (match orbit t with | none => none | some (x, m, s) => mstep x m s) = _
  rw [h]

theorem orbit_succ' {t : Nat} (h : orbit t = none) : orbit (t + 1) = none := orbit_none_add t h 1

/-- **The machine halts from blank tape iff some point of the orbit of (7, 1, 0) is `(x, m, 0)` with m odd and
`x + k + 1 = (m+7)(2^(k+1)-1)/2` for some k >= 0** (from it, k+1 C steps with s = 0 lead to H). -/
theorem halts_iff_chain : HaltsFromBlank ↔ ∃ t x m k, orbit t = some (x, m, false) ∧ m % 2 = 1 ∧
    x + k + 1 = (m + 7) * (2 ^ (k + 1) - 1) / 2 := by
  rw [halts_iff]
  constructor
  · rintro ⟨T, hT⟩
    obtain ⟨t, ⟨x, m, s⟩, ht, ht1⟩ := last_some T hT
    have hs : mstep x m s = none := by rw [← orbit_succ ht]; exact ht1
    obtain ⟨rfl, hm⟩ := mstep_none hs
    rcases t with _ | r
    · simp [orbit] at ht
    · cases e : orbit r with
      | none => rw [orbit_succ' e] at ht; simp at ht
      | some q =>
        obtain ⟨x', m', s'⟩ := q
        have hq : mstep x' m' s' = some (0, m, s) := by rw [← orbit_succ e]; exact ht
        obtain ⟨rfl, hm', hx'⟩ := pred_zero hq hm
        exact ⟨r, x', m', 0, e, hm', by simp only [Nat.zero_add, Nat.pow_one]; omega⟩
  · rintro ⟨t, x, m, k, ht, hm, hk⟩
    exact ⟨t + (k + 2), by rw [orbit_add _ t _ ht]; exact chain_hit x m k hm hk⟩

/-- The point `p` makes a C step with s = 0. -/
def IsC0 (p : Nat × Nat × Bool) : Prop := p.2.2 = false ∧ p.2.1 % 2 = 1 ∧ (p.2.1 + 5) / 2 ≤ p.1

theorem back (r : Nat) : ∀ x m k, orbit r = some (x, m, false) → m % 2 = 1 →
    x + k + 1 = (m + 7) * (2 ^ (k + 1) - 1) / 2 →
    ∃ t x m k, orbit t = some (x, m, false) ∧ m % 2 = 1 ∧ x + k + 1 = (m + 7) * (2 ^ (k + 1) - 1) / 2 ∧
      ∀ t' q, t = t' + 1 → orbit t' = some q → ¬ IsC0 q := by
  induction r with
  | zero =>
    intro x m k h hm hk
    exact ⟨0, x, m, k, h, hm, hk, fun t' q e => absurd e (by omega)⟩
  | succ r ih =>
    intro x m k h hm hk
    cases e : orbit r with
    | none => rw [orbit_succ' e] at h; simp at h
    | some q =>
      by_cases hc : IsC0 q
      · obtain ⟨x', m', s'⟩ := q
        obtain ⟨hs', hm', hx'⟩ := hc
        simp only at hs' hm' hx'
        subst hs'
        obtain ⟨n, rfl⟩ : ∃ n, m' = 2 * n + 1 := ⟨m' / 2, by omega⟩
        have hq := orbit_succ e
        rw [h, cstep0 x' n (by omega)] at hq
        simp only [Option.some.injEq, Prod.mk.injEq, and_true] at hq
        obtain ⟨rfl, rfl⟩ := hq
        refine ih x' (2 * n + 1) (k + 1) e hm' ?_
        have c1 := crit_eq n (k + 1)
        have c2 := crit_eq (2 * n + 4) k
        have d1 := dblA n (k + 1)
        have d2 := dblA' n (k + 1)
        omega
      · exact ⟨r + 1, x, m, k, h, hm, hk, fun t' q' et eq' => by
          rw [show t' = r by omega, e] at eq'
          cases eq'
          exact hc⟩

/-- The same with the point a chain start: `t = 0`, or the point before it does not make a C step with s = 0. -/
theorem halts_iff_chain_start : HaltsFromBlank ↔ ∃ t x m k, orbit t = some (x, m, false) ∧ m % 2 = 1 ∧
    x + k + 1 = (m + 7) * (2 ^ (k + 1) - 1) / 2 ∧ ∀ t' q, t = t' + 1 → orbit t' = some q → ¬ IsC0 q := by
  constructor
  · intro hh
    obtain ⟨t, x, m, k, ht, hm, hk⟩ := halts_iff_chain.mp hh
    exact back t x m k ht hm hk
  · rintro ⟨t, x, m, k, ht, hm, hk, -⟩
    exact halts_iff_chain.mpr ⟨t, x, m, k, ht, hm, hk⟩

end H26350
