/-!
# 1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE: the rules are a tent map with drift

`op` is the bbchallenge wiki's rule map `B(x, y) → B(x', y')` of this machine, `B(x, y) := 0^∞ 1^(2x) F> 1^y 0^∞`,
transcribed from `py/rules.py` (`op`), where it is checked against the machine and the Lean frame map of
`Phases.lean`; here it is a plain function on numbers and is not tied to the machine.

In the coordinates `n = 2x + y` (the tape's length) and `d = 2x − y` the rules are exactly

    d ≥ 0:            n' = n + 4,  d' = n − 2d + 4      (fold, y even)
    d ≥ 3, d odd:     n' = n + 3,  d' = n − 2d + 9      (fold, y odd)
    d ≤ −3:           n' = n + 1,  d' = n + 2d + 7      (double)

plus `d = −2 → B(2x + 1, 0)`, `d = 1 → B(2, 4x − 2)`, and the halt at `d = −1` and nowhere else (`tent`,
`op_none_iff`).  So `u = d/n` follows the tent map `u ↦ 1 − 2|u|` up to `O(1/n)`, and every rule doubles that
`O(1/n)` error: `py/tent.py` shows that the tent orbit of `u`, i.e. its binary expansion read with flips, agrees with
the real fold/double word for only about `log₂ n` rules.  The halt is the exact middle `u = −1/n`.
-/

namespace H151878.Tent

/-- The wiki's rule map (`op` of `py/rules.py`); `none` is the halt. -/
def op (x y : Nat) : Option (Nat × Nat) :=
  if y % 2 = 0 then
    if x ≥ y / 2 then some (2 * (y / 2) + 2, 2 * x - 2 * (y / 2))
    else if x + 1 < y / 2 then some (2 * x + 2, 2 * (y / 2) - 2 * x - 3)
    else some (2 * x + 1, 0)
  else
    if x > y / 2 + 1 then some (2 * (y / 2) + 4, 2 * x - 2 * (y / 2) - 4)
    else if x = y / 2 + 1 then some (2, 4 * x - 2)
    else if x < y / 2 then some (2 * x + 2, 2 * (y / 2) - 2 * x - 2)
    else none

/-- The halt is the exact middle `y = 2x + 1`, i.e. `d = −1`. -/
theorem op_none_iff (x y : Nat) : op x y = none ↔ y = 2 * x + 1 := by
  unfold op
  constructor
  · intro h
    split at h <;> (try split at h) <;> (try split at h) <;> (try split at h) <;> simp_all <;> omega
  · intro h; subst h
    have h1 : (2 * x + 1) % 2 = 1 := by omega
    have h2 : (2 * x + 1) / 2 = x := by omega
    simp [h1, h2]

/-- The rules in the coordinates `n = 2x + y`, `d = 2x − y`: a tent map with drift. -/
theorem tent (x y x' y' : Nat) (h : op x y = some (x', y')) :
    (0 ≤ (2 * x - y : Int) ∧ y % 2 = 0 ∧ (2 * x' + y' : Int) = 2 * x + y + 4 ∧
      (2 * x' - y' : Int) = (2 * x + y) - 2 * (2 * x - y) + 4) ∨
    (3 ≤ (2 * x - y : Int) ∧ y % 2 = 1 ∧ (2 * x' + y' : Int) = 2 * x + y + 3 ∧
      (2 * x' - y' : Int) = (2 * x + y) - 2 * (2 * x - y) + 9) ∨
    ((2 * x - y : Int) ≤ -3 ∧ (2 * x' + y' : Int) = 2 * x + y + 1 ∧
      (2 * x' - y' : Int) = (2 * x + y) + 2 * (2 * x - y) + 7) ∨
    ((2 * x - y : Int) = -2 ∧ x' = 2 * x + 1 ∧ y' = 0) ∨
    ((2 * x - y : Int) = 1 ∧ x' = 2 ∧ y' = 4 * x - 2) := by
  unfold op at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; omega)
    | simp at h

end H151878.Tent
