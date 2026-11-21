import Phase1

/-!
# 1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE: the closed form of the map

With `h k = 5·2^k - k - 6` (so the thresholds `c_i` of the README are `h (i+1)`: 3, 12, 31, 70, …), for
`h k < n < h (k+1)` the map `next` of `Phase1.lean` is `n ↦ 3n + 3k + 14 - 10·2^k` (`next_closed`), and it halts
exactly at the thresholds: `next (h k) = none` for `k ≥ 1` (`next_halt`).  (`h 0` is `0` in `Nat`; the range
`h 0 < n < h 1` is `n = 1, 2`.)

Proof: `j` complete bounce rounds take `ph (R + d j) 0 0` to `ph R 0 (10·2^j - 5)` with `d j = 10·2^j - j - 6`
(`ph_rounds`); from there either the right block runs out first (`ph_lt`) or the left one does, leaving one of
the four endings `ph r (10·2^j - 5) 0`, `r ≤ 3` (`ph_bounces`).
-/

namespace H87254

/-- The level thresholds. -/
def h (k : Nat) : Nat := 5 * 2 ^ k - k - 6

theorem pow_facts (k : Nat) : k < 2 ^ k ∧ 2 ^ (k + 1) = 2 * 2 ^ k :=
  ⟨Nat.lt_two_pow_self, by rw [Nat.pow_succ]; omega⟩

/-- `m` bounces. -/
theorem ph_bounces (m : Nat) : ∀ K i, ph (K + m) i m = ph K (i + m) 0 := by
  induction m with
  | zero => intro K i; rfl
  | succ m ih =>
    intro K i
    rw [show K + (m + 1) = (K + m) + 1 by omega, show i + (m + 1) = (i + 1) + m by omega, ← ih K (i + 1)]
    simp only [ph]

/-- The right block runs out first. -/
theorem ph_lt (K : Nat) : ∀ i m, K < m → ph K i m = some (4 * i + 3 * K + m + 7) := by
  induction K with
  | zero =>
    intro i m hm
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [ph]; congr 1
  | succ K ih =>
    intro i m hm
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [ph]
    rw [ih (i + 1) m (by omega)]; congr 1; omega

/-- `j` complete rounds. -/
theorem ph_rounds (j : Nat) : ∀ R, ph (R + (10 * 2 ^ j - j - 6)) 0 0 = ph R 0 (10 * 2 ^ j - 5) := by
  induction j with
  | zero => intro R; simp only [ph, Nat.pow_zero]
  | succ j ih =>
    intro R
    obtain ⟨p1, p2⟩ := pow_facts j
    have e1 : R + (10 * 2 ^ (j + 1) - (j + 1) - 6) = (R + 4 + (10 * 2 ^ j - 5)) + (10 * 2 ^ j - j - 6) := by omega
    rw [e1, ih, ph_bounces, Nat.zero_add]
    simp only [ph]
    congr 1; omega

/-- The value of `next` when the run ends in the round after `j` complete rounds (`n ≥ h (j+1) + 2`). -/
theorem next_round (j R : Nat) : next (R + (10 * 2 ^ j - j - 6) + 1) = ph R 0 (10 * 2 ^ j - 5) := by
  simp only [next, Nat.add_sub_cancel]; exact ph_rounds j R

/-- **The closed form**: for `h k < n < h (k+1)`, `next n = 3n + 3k + 14 - 10·2^k`. -/
theorem next_closed (k n : Nat) (h1 : h k < n) (h2 : n < h (k + 1)) : next n = some (3 * n + 3 * k + 14 - 10 * 2 ^ k) := by
  unfold h at h1 h2
  obtain ⟨p1, p2⟩ := pow_facts k
  cases k with
  | zero =>
    simp only [Nat.pow_zero] at h1 h2 ⊢
    have : n = 1 ∨ n = 2 := by omega
    rcases this with rfl | rfl <;> rfl
  | succ j =>
    obtain ⟨q1, q2⟩ := pow_facts j
    rw [p2] at h2
    rw [q2] at h1 h2 ⊢
    by_cases hlo : n = 10 * 2 ^ j - j - 6
    · -- the ending `r = 3` of the previous round (or `n = 4`)
      cases j with
      | zero => subst hlo; rfl
      | succ i =>
        obtain ⟨s1, s2⟩ := pow_facts i
        rw [s2] at hlo h1 h2 ⊢
        have e : n = 3 + (10 * 2 ^ i - 5) + (10 * 2 ^ i - i - 6) + 1 := by omega
        rw [e, next_round, ph_bounces]; simp only [ph]; congr 1; omega
    · by_cases hmid : n + 3 ≤ 20 * 2 ^ j - j - 8
      · have e : n = (n - (10 * 2 ^ j - j - 6) - 1) + (10 * 2 ^ j - j - 6) + 1 := by omega
        rw [e, next_round, ph_lt _ _ _ (by omega)]; congr 1; omega
      · -- the endings `r = 0, 1`
        have : n + 2 = 20 * 2 ^ j - j - 8 ∨ n + 1 = 20 * 2 ^ j - j - 8 := by omega
        rcases this with e0 | e0
        · rw [show n = 0 + (10 * 2 ^ j - 5) + (10 * 2 ^ j - j - 6) + 1 by omega, next_round, ph_bounces]
          simp only [ph]; congr 1; omega
        · rw [show n = 1 + (10 * 2 ^ j - 5) + (10 * 2 ^ j - j - 6) + 1 by omega, next_round, ph_bounces]
          simp only [ph]; congr 1; omega

/-- **The halts**: `next (h k) = none` for `k ≥ 1`. -/
theorem next_halt (k : Nat) (hk : 1 ≤ k) : next (h k) = none := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  cases j with
  | zero => rfl
  | succ i =>
    obtain ⟨s1, s2⟩ := pow_facts i
    obtain ⟨q1, q2⟩ := pow_facts (i + 1)
    unfold h
    rw [q2, s2, show 5 * (2 * (2 * 2 ^ i)) - (i + 1 + 1) - 6 = 2 + (10 * 2 ^ i - 5) + (10 * 2 ^ i - i - 6) + 1 by omega,
      next_round, ph_bounces]
    simp only [ph]

/-! Spot checks of the statements. -/
example : (List.range 7).map h = [0, 3, 12, 31, 70, 149, 308] := by decide
example : next 30 = some (3 * 30 + 3 * 2 + 14 - 10 * 2 ^ 2) := by decide

end H87254
