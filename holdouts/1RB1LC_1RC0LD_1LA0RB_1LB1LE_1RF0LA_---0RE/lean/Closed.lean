import Orbit

/-!
# 1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE: the closed form of the round map

With `h k = 5·2^k - k - 6` (3, 12, 31, 70, … for `k ≥ 1`; `h 0` is `0` in `Nat`) and the coordinate `N = 2n + 2`:
for `h k < n < h (k+1)` the round map `next` of `Orbit.lean` takes `2n + 2` to `2n' + 2` with
`n' = 3n + 3k + 14 - 10·2^k` (`next_closed`), and `next (2 h k + 2) = none` for `k ≥ 1` (`next_halt`).  In terms of
`N` this is the README's `N ↦ 3N + 24 + 6k - 20·2^k`, halting when the remainder `N + 10 - 10·2^k + 2k` is 0.

Proof: `j` doublings take `phase 1 (m + 10·2^j - 2j - 10)` to `phase (5·2^j - 4) m` (`phase_rounds`); with `j = k`
the remainder is `m = 2n + 2 - (10·2^k - 2k - 10)`, which is `0` at `n = h k` and `0 < m < 2K + 6` inside the level.
-/

namespace H167198

/-- The level thresholds. -/
def h (k : Nat) : Nat := 5 * 2 ^ k - k - 6

theorem pow_facts (k : Nat) : k < 2 ^ k ∧ 2 ^ (k + 1) = 2 * 2 ^ k :=
  ⟨Nat.lt_two_pow_self, by rw [Nat.pow_succ]; omega⟩

theorem phase_zero (K : Nat) : phase K 0 = none := by
  rw [phase]; simp

theorem phase_double (K m : Nat) : phase K (m + (2 * K + 6)) = phase (2 * K + 4) m := by
  rw [phase]
  have h0 : ¬(m + (2 * K + 6) = 0) := by omega
  simp only [h0, Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel]

theorem phase_end (K m : Nat) (h0 : 0 < m) (h1 : m < 2 * K + 6) : phase K m = some (2 * K + 3 * m + 2) := by
  rw [phase]
  have h0' : ¬(m = 0) := by omega
  have h1' : ¬(2 * K + 6 ≤ m) := by omega
  simp only [h0', h1', ↓reduceIte]

/-- `j` doublings from `phase 1`. -/
theorem phase_rounds (j : Nat) : ∀ m, phase 1 (m + (10 * 2 ^ j - 2 * j - 10)) = phase (5 * 2 ^ j - 4) m := by
  induction j with
  | zero => intro m; rfl
  | succ j ih =>
    intro m
    obtain ⟨p1, p2⟩ := pow_facts j
    rw [show m + (10 * 2 ^ (j + 1) - 2 * (j + 1) - 10) = m + (2 * (5 * 2 ^ j - 4) + 6) + (10 * 2 ^ j - 2 * j - 10) by omega,
      ih, phase_double, show 2 * (5 * 2 ^ j - 4) + 4 = 5 * 2 ^ (j + 1) - 4 by omega]

/-- **The closed form**: for `h k < n < h (k+1)`, `next (2n + 2) = 2(3n + 3k + 14 - 10·2^k) + 2`. -/
theorem next_closed (k n : Nat) (h1 : h k < n) (h2 : n < h (k + 1)) :
    next (2 * n + 2) = some (2 * (3 * n + 3 * k + 14 - 10 * 2 ^ k) + 2) := by
  unfold h at h1 h2
  obtain ⟨p1, p2⟩ := pow_facts k
  rw [p2] at h2
  unfold next
  rw [show 2 * n + 2 = (2 * n + 2 - (10 * 2 ^ k - 2 * k - 10)) + (10 * 2 ^ k - 2 * k - 10) by omega, phase_rounds,
    phase_end _ _ (by omega) (by omega)]
  congr 1; omega

/-- **The halts**: `next (2 h k + 2) = none` for `k ≥ 1`. -/
theorem next_halt (k : Nat) (hk : 1 ≤ k) : next (2 * h k + 2) = none := by
  obtain ⟨p1, p2⟩ := pow_facts k
  unfold next h
  rw [show 2 * (5 * 2 ^ k - k - 6) + 2 = 0 + (10 * 2 ^ k - 2 * k - 10) by omega, phase_rounds, phase_zero]

end H167198
