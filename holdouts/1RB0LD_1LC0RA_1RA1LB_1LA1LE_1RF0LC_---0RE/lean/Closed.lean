import Iff

/-!
# 1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE: the closed form of the macro step

With `h k = 5·2^k - k - 6` (3, 12, 31, 70, … for `k ≥ 1`; `h 0` is `0` in `Nat`, the range `h 0 < n < h 1` is
`n = 1, 2`): for `h k < n < h (k+1)` the macro step `pstep n` of `Macro.lean` goes to `P (3n + 3k + 14 - 10·2^k)`
(`pstep_closed`), and `pstep (h k)` halts for `k ≥ 1` (`pstep_halt`).  Only the position is stated; the step count
is left as it is.

Proof: `k` doubling rounds take `T 1 (m + 10·2^k - 2k - 10)` to `T (5·2^k - 4) m` (`tphase_rounds`), and with
`2n + 2 = 2(n - h k) + 10·2^k - 2k - 10` the end of the phase is `tend c (2r)`, `1 ≤ r ≤ c + 2`, which goes to
`P (c + 3r)` (`tend_even`), or `tend c 0`, a halt.
-/

namespace H50372

/-- The level thresholds. -/
def h (k : Nat) : Nat := 5 * 2 ^ k - k - 6

theorem pow_facts (k : Nat) : k < 2 ^ k ∧ 2 ^ (k + 1) = 2 * 2 ^ k :=
  ⟨Nat.lt_two_pow_self, by rw [Nat.pow_succ]; omega⟩

theorem Out.addT_addT (a b : Nat) (o : Out) : (o.addT b).addT a = o.addT (a + b) := by
  cases o <;> simp [Out.addT, Nat.add_assoc]

theorem Out.addT_zero (o : Out) : o.addT 0 = o := by
  cases o <;> simp [Out.addT]

theorem tphase_round (f c m : Nat) :
    tphase (f + 1) c (m + (2 * c + 6)) = (tphase f (2 * c + 4) m).addT ((2 * c + 3) + (zsteps 0 c + (16 * c + 23))) := by
  simp only [tphase, Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel]

theorem tphase_end (f c m : Nat) (hm : m < 2 * c + 6) : tphase f c m = tend c m := by
  have h : ¬(2 * c + 6 ≤ m) := by omega
  cases f <;> simp only [tphase, h, ↓reduceIte]

/-- `j` doubling rounds from `T 1`. -/
theorem tphase_rounds (j : Nat) : ∀ f m, ∃ a,
    tphase (f + j) 1 (m + (10 * 2 ^ j - 2 * j - 10)) = (tphase f (5 * 2 ^ j - 4) m).addT a := by
  induction j with
  | zero => intro f m; exact ⟨0, by simp [Out.addT_zero]⟩
  | succ j ih =>
    intro f m
    obtain ⟨p1, p2⟩ := pow_facts j
    obtain ⟨a, ha⟩ := ih (f + 1) (m + (2 * (5 * 2 ^ j - 4) + 6))
    rw [show f + (j + 1) = f + 1 + j by omega,
      show m + (10 * 2 ^ (j + 1) - 2 * (j + 1) - 10) = m + (2 * (5 * 2 ^ j - 4) + 6) + (10 * 2 ^ j - 2 * j - 10) by omega,
      ha, tphase_round, Out.addT_addT, show 2 * (5 * 2 ^ j - 4) + 4 = 5 * 2 ^ (j + 1) - 4 by omega]
    exact ⟨_, rfl⟩

theorem go_ex {a b t : Nat} (h : a = b) : ∃ t', Out.go a t = Out.go b t' := ⟨t, h ▸ rfl⟩

/-- The end of the phase with an even number `2r ≥ 2` of ones left. -/
theorem tend_even (c r : Nat) (h1 : 1 ≤ r) (h2 : r ≤ c + 2) : ∃ t, tend c (2 * r) = .go (c + 3 * r) t := by
  simp only [tend]
  repeat' split
  all_goals first | (exfalso; omega) | exact go_ex (by omega)

theorem tend_zero (c : Nat) : tend c 0 = .halt (2 * c) := by simp [tend]

/-- The macro step from `P n` with `2n + 2 = m + 10·2^k - 2k - 10`. -/
theorem pstep_eq (k n m : Nat) (hn : 2 * n + 2 = m + (10 * 2 ^ k - 2 * k - 10)) (hm : m < 2 * (5 * 2 ^ k - 4) + 6)
    (hk : k ≤ 2 * n + 2) : ∃ a, pstep n = (tend (5 * 2 ^ k - 4) m).addT a := by
  obtain ⟨a, ha⟩ := tphase_rounds k (2 * n + 2 - k) m
  rw [show 2 * n + 2 - k + k = 2 * n + 2 by omega, ← hn, tphase_end _ _ _ hm] at ha
  exact ⟨_, by rw [pstep, ha, Out.addT_addT]⟩

/-- **The closed form**: for `h k < n < h (k+1)`, `P n` goes to `P (3n + 3k + 14 - 10·2^k)`. -/
theorem pstep_closed (k n : Nat) (h1 : h k < n) (h2 : n < h (k + 1)) :
    ∃ t, pstep n = .go (3 * n + 3 * k + 14 - 10 * 2 ^ k) t := by
  unfold h at h1 h2
  obtain ⟨p1, p2⟩ := pow_facts k
  rw [p2] at h2
  cases k with
  | zero =>
    simp only [Nat.pow_zero] at h1 h2 ⊢
    have : n = 1 ∨ n = 2 := by omega
    rcases this with rfl | rfl <;> exact ⟨_, rfl⟩
  | succ j =>
    obtain ⟨a, ha⟩ := pstep_eq (j + 1) n (2 * (n - (5 * 2 ^ (j + 1) - (j + 1) - 6))) (by omega) (by omega) (by omega)
    obtain ⟨t, ht⟩ := tend_even (5 * 2 ^ (j + 1) - 4) (n - (5 * 2 ^ (j + 1) - (j + 1) - 6)) (by omega) (by omega)
    rw [ha, ht]
    exact go_ex (by omega)

/-- **The halts**: `P (h k)` halts for `k ≥ 1`. -/
theorem pstep_halt (k : Nat) (hk : 1 ≤ k) : ∃ t, pstep (h k) = .halt t := by
  obtain ⟨p1, p2⟩ := pow_facts k
  unfold h
  obtain ⟨a, ha⟩ := pstep_eq k (5 * 2 ^ k - k - 6) 0 (by omega) (by omega) (by omega)
  rw [ha, tend_zero]
  exact ⟨_, rfl⟩

end H50372
