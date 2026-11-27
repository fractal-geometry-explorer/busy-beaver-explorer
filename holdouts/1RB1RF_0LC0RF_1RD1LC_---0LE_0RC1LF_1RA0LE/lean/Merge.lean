import Tent
/-!
# 1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE: which tapes lead to a given tape

For the rule map `op` of `Tent.lean` (a plain function on numbers, see there):

* `op_even`: every rule lands on `B(x', y')` with `x'` even, or on `B(2x + 1, 0)`;
* `three_pre`: a tape `B(2a + 2, 2c)` (`a ≥ 1`) is the next tape of three different tapes, so orbits merge;
* `odd_pre`: a tape with `y'` odd has exactly one tape before it;
* `halt_pre`, `halt_pre_iff`: the tape before the halting tape `B(x', 2x' + 1)` is `B(x, 6x + 8)` with `x' = 2x + 2`,
  and nothing else.

`c/fates.c` and `c/back.c` count with these: all tapes below a level end on a handful of orbits.
-/

namespace H151878.Merge
open H151878.Tent

/-- Every rule lands on an even `x'`, except the rule into `B(2x + 1, 0)`. -/
theorem op_even (x y x' y' : Nat) (h : op x y = some (x', y')) : x' % 2 = 0 ∨ (x' = 2 * x + 1 ∧ y' = 0) := by
  unfold op at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; omega)
    | simp at h

/-- Three tapes with the same next tape `B(2a + 2, 2c)`: a fold from `y` even, a fold from `y` odd, a doubling. -/
theorem three_pre (a c : Nat) (ha : 1 ≤ a) :
    op (a + c) (2 * a) = some (2 * a + 2, 2 * c) ∧
    op (a + c + 1) (2 * a - 1) = some (2 * a + 2, 2 * c) ∧
    op a (2 * a + 2 * c + 3) = some (2 * a + 2, 2 * c) := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 : (2 * a) % 2 = 0 := by omega
    have h2 : (2 * a) / 2 = a := by omega
    have h3 : a + c ≥ a := by omega
    have h4 : 2 * (a + c) - 2 * a = 2 * c := by omega
    simp [op, h1, h2, h3, h4]
  · have h1 : (2 * a - 1) % 2 = 1 := by omega
    have h2 : (2 * a - 1) / 2 = a - 1 := by omega
    have h3 : a + c + 1 > a - 1 + 1 := by omega
    have h4 : 2 * (a - 1) + 4 = 2 * a + 2 := by omega
    have h5 : 2 * (a + c + 1) - 2 * (a - 1) - 4 = 2 * c := by omega
    simp [op, h1, h2, h3, h4, h5]
  · have h1 : (2 * a + 2 * c + 3) % 2 = 1 := by omega
    have h2 : (2 * a + 2 * c + 3) / 2 = a + c + 1 := by omega
    have h3 : ¬ a > a + c + 1 + 1 := by omega
    have h4 : ¬ a = a + c + 1 + 1 := by omega
    have h5 : a < a + c + 1 := by omega
    have h6 : 2 * (a + c + 1) - 2 * a - 2 = 2 * c := by omega
    simp [op, h1, h2, h3, h4, h5, h6]

/-- A tape with `y'` odd has one tape before it: `B(x, y' + 2x + 3)` with `x' = 2x + 2`. -/
theorem odd_pre (x y x' y' : Nat) (h : op x y = some (x', y')) (hy : y' % 2 = 1) :
    x' = 2 * x + 2 ∧ y = y' + 2 * x + 3 := by
  unfold op at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; omega)
    | simp at h

/-- The only tape before the halting tape `B(x', 2x' + 1)` is `B(x, 6x + 8)`, `x' = 2x + 2`. -/
theorem halt_pre (x y x' : Nat) (h : op x y = some (x', 2 * x' + 1)) : x' = 2 * x + 2 ∧ y = 6 * x + 8 := by
  have := odd_pre x y x' (2 * x' + 1) h (by omega)
  omega

theorem halt_pre_iff (x y x' : Nat) :
    op x y = some (x', 2 * x' + 1) ↔ x' = 2 * x + 2 ∧ y = 6 * x + 8 := by
  constructor
  · exact halt_pre x y x'
  · rintro ⟨rfl, rfl⟩
    have h1 : (6 * x + 8) % 2 = 0 := by omega
    have h2 : (6 * x + 8) / 2 = 3 * x + 4 := by omega
    have h3 : ¬ x ≥ 3 * x + 4 := by omega
    have h4 : x + 1 < 3 * x + 4 := by omega
    have h5 : 2 * (3 * x + 4) - 2 * x - 3 = 2 * (2 * x + 2) + 1 := by omega
    simp [op, h1, h2, h3, h4, h5]

end H151878.Merge
