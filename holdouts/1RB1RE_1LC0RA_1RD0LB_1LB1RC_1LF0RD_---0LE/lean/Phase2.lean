import Rules

/-!
# 1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE: the second phase of a round, for all values

* `S n`   = `0^inf C> 0 (10)^n 1 0^inf`               (the samples: the head at the left end)
* `T x z` = `0^inf C> 0 (10)^x 111 0 (10)^z 1 0^inf`  (the end of the first phase)
* `U k m` = `0^inf 1^k 0 A> 0 (10)^m 1 0^inf`

`phase2`: `T x z` reaches `S (2x + z + 4)`.  The left block of `T` is first turned into `2x + 1` ones; each
bounce then turns two of them into a pair `10` of the right block (`t2`), and the last one adds a cell on the left.
The first phase, `S n` to `T x z`, is checked by simulation (see the README), not proved here.
-/

namespace H87254

open TM

def S (n : Nat) : Config := ⟨blank, cons false (rep n [true, false] (cons true blank)), .C⟩

def T (x z : Nat) : Config :=
  ⟨blank, cons false (rep x [true, false] (cons true (cons true (cons true (cons false
    (rep z [true, false] (cons true blank))))))), .C⟩

def U (k m : Nat) : Config := ⟨cons false (rep k [true] blank), cons false (rep m [true, false] (cons true blank)), .A⟩

theorem rot_tf (n : Nat) (s : Tape) : cons false (rep n [true, false] s) = rep n [false, true] (cons false s) :=
  rep_rotate n [false] [true, false] [false, true] rfl s

theorem rep_tt (n : Nat) (s : Tape) : rep n [true, true] s = rep (2 * n) [true] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    show cons true (cons true (rep n [true, true] s)) = cons true (cons true (rep (2 * n) [true] s))
    rw [ih]

theorem u1 (x z : Nat) : steps (2 * x + 4 * z + 20) (T (x + 1) z) = some (U (2 * x + 1) (z + 3)) := by
  have h := t1 x z
  simp only [← rot_tf, rep_tt] at h
  exact h

theorem u1z (z : Nat) : steps 4 (T 0 z) = some (U 1 (z + 1)) := t1z z

theorem u2 (k m : Nat) : steps (4 * m + 10) (U (k + 2) m) = some (U k (m + 2)) := by
  have h := t2 k m
  simp only [← rot_tf] at h
  exact h

theorem u3 (m : Nat) : steps (4 * m + 10) (U 1 m) = some (S (m + 3)) := by
  have h := t3 m
  simp only [← rot_tf] at h
  exact h

theorem u2_iter (j m : Nat) : ∃ n, steps n (U (2 * j + 1) m) = some (U 1 (m + 2 * j)) := by
  induction j generalizing m with
  | zero => exact ⟨0, rfl⟩
  | succ j ih =>
    obtain ⟨n, h⟩ := ih (m + 2)
    refine ⟨4 * m + 10 + n, ?_⟩
    have h0 := u2 (2 * j + 1) m
    rw [show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by omega] at h0
    rw [show m + 2 * (j + 1) = m + 2 + 2 * j by omega]
    exact steps_seq trans h0 h

/-- **The second phase**: `T x z` reaches `S (2x + z + 4)`, for all `x` and `z`. -/
theorem phase2 (x z : Nat) : ∃ n, steps n (T x z) = some (S (2 * x + z + 4)) := by
  cases x with
  | zero =>
    refine ⟨4 + (4 * (z + 1) + 10), ?_⟩
    have h := steps_seq trans (u1z z) (u3 (z + 1))
    rw [show z + 1 + 3 = 2 * 0 + z + 4 by omega] at h
    exact h
  | succ x =>
    obtain ⟨n, h⟩ := u2_iter x (z + 3)
    refine ⟨2 * x + 4 * z + 20 + (n + (4 * (z + 3 + 2 * x) + 10)), ?_⟩
    have h3 := u3 (z + 3 + 2 * x)
    rw [show z + 3 + 2 * x + 3 = 2 * (x + 1) + z + 4 by omega] at h3
    exact steps_seq trans (u1 x z) (steps_seq trans h h3)

end H87254
