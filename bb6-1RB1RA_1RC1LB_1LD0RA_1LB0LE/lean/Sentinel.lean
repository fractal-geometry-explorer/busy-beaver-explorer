import Pass

/-!
# A sentinel block of 3: the pass map contains a copy of itself

For a block list `y₁ … y_k` (first block first) let `φ(y) = y₁ … y_(k−1) (y_k + 5) 3`: the last block gains 5 and a
block of 3 is put after it.  Then a pass commutes with `φ` exactly, for every block list (`next_phi`):

    next (φ y) = φ (next y)

and a halt or a stop at a block of 1 of `y` is one of `φ y` as well.  Why: an odd 3 is always crossed and stays 3
((3 + 3)/2 = 3 is what the zigzag leaves for it); crossing it records `g = 3`, which adds 5 = 3 + 2 to the block
before it; and `y_k + 5` has the other parity from `y_k`, so the sweep of `φ y` crosses it exactly when the sweep
of `y` stops at once, and the zigzag's `g` for it is the `g` of `y_k` plus nothing (`(y_k + 5)/2 − 1 = (y_k + 3)/2`).

So the orbit of `φ y` is `φ` of the orbit of `y`, pass for pass (`iter_phi`).  Two consequences, kernel only:

* `sentinel_orbit`: from the tape `1^5 0 1^3` (`φ` of blank tape, read as one empty block) the pass map runs
  `φ` of the blank-tape orbit for ever.  This is the "sentinel orbit from [1, 3]" of `py/induction.py` (that orbit
  is at `[0, 5, 3]` after one pass): it meets a stop block of 1 exactly when the blank orbit does
  (`sentinel_one_iff`), so every result on the blank orbit holds for it.
* `inner_counter`: the three-block state `[x, 2x+6, 3]` runs exactly the excursion of `[x, 2x+1]`; its return map
  is the return map G of `Return.lean`, with the same k and the same 9k passes.

`notes/LAB_NOTES.md` (4 November) uses this to read the excursions of the return map: while the last block of a
state is 3 modulo a high power of 2, the pass map runs (modulo that power, losing one bit per pass) the orbit of the
list with that block removed, and for a = 1 + 2^m u the first m − 1 passes of the excursion from `[a, 2a+1]` run
the blank orbit itself (computed).
-/

namespace BB6d

/-- `φ`, nearest block first: `3` goes in front and the old nearest block gains 5.  Blank tape is read as one empty
block, so `φ [] = [3, 5]`. -/
def phi : List Nat → List Nat
  | [] => [3, 5]
  | y :: ys => 3 :: (y + 5) :: ys

/-- `φ` on the outcome of a pass: a halt and a stop at a block of 1 stay what they are. -/
def phiN : Next → Next
  | .ok zs => .ok (phi zs)
  | e => e

/-- `t` passes of the closed form from `zs`. -/
def iter : Nat → List Nat → Next
  | 0, zs => .ok zs
  | n + 1, zs =>
    match iter n zs with
    | .ok ws => next ws
    | e => e

theorem zag_three (gs : List Nat) : ∀ (q : Nat) (ms : List Nat), zag q ms (gs ++ [3]) = phi (zag q ms gs) := by
  induction gs with
  | nil => intro q ms; simp only [List.nil_append, zag, phi]
  | cons g gs ih => intro q ms; simp only [List.cons_append, zag, ih]

theorem sweep_three (ys : List Nat) : ∀ gs : List Nat, sweep (gs ++ [3]) ys = phiN (sweep gs ys) := by
  induction ys with
  | nil => intro gs; rfl
  | cons y ys ih =>
    intro gs
    simp only [sweep]
    by_cases h0 : y % 2 = 0
    · by_cases hz : y = 0
      · simp [hz, phiN]
      · simp only [h0, hz, ite_true, ite_false]
        rw [← List.cons_append]; exact ih _
    · by_cases h1 : y = 1
      · simp [h1, phiN]
      · simp only [h0, h1, ite_false, phiN, zag_three]

/-- **A pass commutes with the sentinel**, for every block list. -/
theorem next_phi (zs : List Nat) : next (phi zs) = phiN (next zs) := by
  match zs with
  | [] => rfl
  | y :: ys =>
    show sweep [3] ((y + 5) :: ys) = phiN (next (y :: ys))
    simp only [next, sweep]
    by_cases h : y % 2 = 0
    · have h1 : (y + 5) % 2 ≠ 0 := by omega
      have h2 : y + 5 ≠ 1 := by omega
      have h3 : (y + 5 - 1) / 2 = y / 2 + 2 := by omega
      simp only [h, h1, h2, h3, ite_true, ite_false, phiN]
      rw [show [3] = ([] : List Nat) ++ [3] from rfl, zag_three]; rfl
    · have h1 : (y + 5) % 2 = 0 := by omega
      have h2 : y + 5 ≠ 0 := by omega
      have h3 : (y + 5) / 2 - 1 = (y + 3) / 2 := by omega
      simp only [h, h1, h2, h3, ite_true, ite_false]
      rw [show [(y + 3) / 2, 3] = [(y + 3) / 2] ++ [3] from rfl, sweep_three]

/-- The orbit of `φ zs` is `φ` of the orbit of `zs`. -/
theorem iter_phi (zs : List Nat) : ∀ n, iter n (phi zs) = phiN (iter n zs) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [iter, ih]
    cases iter n zs with
    | ok ws => exact next_phi ws
    | halt => rfl
    | one => rfl

theorem orbit_iter (n : Nat) : orbit n = iter n [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [orbit, iter, ih]; cases iter n [] <;> rfl

/-- From `1^5 0 1^3` (nearest first `[3, 5]`, which is `φ` of blank tape) the pass map runs `φ` of the blank-tape
orbit, for every pass. -/
theorem sentinel_orbit (n : Nat) : iter n [3, 5] = phiN (orbit n) := by
  rw [orbit_iter]; exact iter_phi [] n

/-- The sentinel orbit meets a stop block of 1 exactly when the blank-tape orbit does. -/
theorem sentinel_one_iff (n : Nat) : iter n [3, 5] = .one ↔ orbit n = .one := by
  rw [sentinel_orbit]
  cases orbit n with
  | ok zs => simp [phiN]
  | halt => simp [phiN]
  | one => simp [phiN]

/-- **The inner counter**: `[x, 2x+6, 3]` (nearest first `[3, 2x+6, x]`) runs exactly `φ` of the excursion of
`[x, 2x+1]`, so it returns to `[x', 2x'+6, 3]` exactly when `[x, 2x+1]` returns to `[x', 2x'+1]`, after the same
number of passes. -/
theorem inner_counter (x n : Nat) : iter n [3, 2 * x + 6, x] = phiN (iter n [2 * x + 1, x]) :=
  iter_phi [2 * x + 1, x] n

theorem inner_return (x x' n : Nat) (h : iter n [2 * x + 1, x] = .ok [2 * x' + 1, x']) :
    iter n [3, 2 * x + 6, x] = .ok [3, 2 * x' + 6, x'] := by
  rw [inner_counter, h]; rfl

/-! Two checks by evaluation: the sentinel orbit at pass 5 is `[5, 16, 3]` (`φ [5, 11]`, the blank orbit's pass 4,
`phi` of it), and the inner counter from x = 5 returns at x = 17 after 9 passes, as `[5, 11]` does. -/
example : iter 4 [3, 5] = .ok [3, 16, 5] := by decide
example : iter 9 [3, 16, 5] = .ok [3, 40, 17] := by decide

end BB6d
