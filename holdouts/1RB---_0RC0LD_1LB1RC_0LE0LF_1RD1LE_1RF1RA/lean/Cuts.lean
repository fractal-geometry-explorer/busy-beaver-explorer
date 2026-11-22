import Series

/-!
# 1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA: why a descent at the left end never starts a sweep on a block of 3

At the left end of the tape the machine cuts the first block to two thirds again and again (README, "What it
does"); after the first cut every value is even.  `Sweep.lean` says that a sweep that starts at `B L (3 :: r :: R)`
with `r ≥ 1` halts.  This file computes the end of a descent whose last two cuts are an even block divisible by 3
and then a block `≡ 1 (mod 3)`: the even block is `6s` with `s ≡ 1 (mod 3)`, so `18u + 6`, and

* `cut_even`: `E [] (18u+6 :: 0 :: j :: R)` reaches `B [8u+7] (4u+1 :: j+6u+1 :: R)` in `30u + 7` frames.

So the sweep that follows starts on a block of `4u + 1` cells: 1, 5, 9, 13, …, never 3.  The block of 3 that
`critical_15` (`Series.lean`) reaches comes from an odd block of 15, which a descent can only start with.  This
is the arithmetic behind the observation that the first block at a sweep start is so often `≡ 1 (mod 4)`
(`c/sweeps.c`).
-/

namespace H15414

open TM

theorem cut_even_a (u j : Nat) (R : List Nat) :
    iterF next (18 * u + 5) (.E [] ((18 * u + 6) :: 0 :: j :: R))
      = some (.E [] ((12 * u + 4) :: 0 :: 1 :: (j + 6 * u + 1) :: R)) := by
  have e1 : 18 * u + 5 = 3 + (3 * (6 * u) + 2) := by omega
  have e2 : 18 * u + 6 = (18 * u + 1) + 5 := by omega
  rw [e1, e2, iterF_add, zig1_end, Option.bind_some, iterF_add]
  have e3 : 18 * u + 1 + 2 = 1 + 2 + 3 * (6 * u) := by omega
  rw [e3, zig (6 * u) 2 [] 1 (j + 1) R, Option.bind_some]
  have e4 : j + 1 + 6 * u = j + 6 * u + 1 := by omega
  have e5 : 2 + 2 * (6 * u) + 2 = 12 * u + 4 := by omega
  rw [e4]
  show some (Ph.E [] ((2 + 2 * (6 * u) + 2) :: 0 :: (0 + 1) :: (j + 6 * u + 1) :: R)) = _
  rw [e5]

theorem cut_even_b (u J : Nat) (R : List Nat) :
    iterF next (12 * u + 2) (.E [] ((12 * u + 4) :: 0 :: 1 :: J :: R))
      = some (.B [8 * u + 7] ((4 * u + 1) :: J :: R)) := by
  cases u with
  | zero => rfl
  | succ v =>
    have e1 : 12 * (v + 1) + 2 = 3 + (3 * (4 * v + 3) + 2) := by omega
    have e2 : 12 * (v + 1) + 4 = (12 * v + 11) + 5 := by omega
    rw [e1, e2, iterF_add, zig1_end, Option.bind_some, iterF_add]
    have e3 : 12 * v + 11 + 2 = 2 + 2 + 3 * (4 * v + 3) := by omega
    rw [e3, zig (4 * v + 3) 2 [] 2 (1 + 1) (J :: R), Option.bind_some]
    show some (Ph.B [2 + 2 * (4 * v + 3) + 2 + 5] ((1 + 1 + (4 * v + 3)) :: J :: R)) = _
    have e4 : 2 + 2 * (4 * v + 3) + 2 + 5 = 8 * (v + 1) + 7 := by omega
    have e5 : 1 + 1 + (4 * v + 3) = 4 * (v + 1) + 1 := by omega
    rw [e4, e5]

/-- **A descent at the left end that ends with an even block divisible by 3 starts its sweep on a block of
`4u + 1` cells**, never 3. -/
theorem cut_even (u j : Nat) (R : List Nat) :
    iterF next (30 * u + 7) (.E [] ((18 * u + 6) :: 0 :: j :: R))
      = some (.B [8 * u + 7] ((4 * u + 1) :: (j + 6 * u + 1) :: R)) := by
  have e : 30 * u + 7 = (18 * u + 5) + (12 * u + 2) := by omega
  rw [e, iterF_add, cut_even_a, Option.bind_some, cut_even_b]

end H15414
