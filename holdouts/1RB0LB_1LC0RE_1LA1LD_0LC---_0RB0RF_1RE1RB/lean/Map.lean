import Rules

/-!
# The E-event map of 1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB

`Ecfg a m` is the configuration `1 0 0 (10)^a 0^m E> 1` (blank elsewhere): E reads the last 1 of the tape, `a` copies
of `10` (the counter) sit at the left end and a gap of `m` zeros separates them from the head.  One *E-step* takes it
to the next such configuration (`emap`):

    m = 3k     →  Ecfg (a + 6) (4k + 4)    in 4k² + 23k + 16a + 94 steps
    m = 3k + 1 →  Ecfg (a − 1) (4k + 7)    in 4k² + 23k + 28 steps
    m = 3k + 2 →  Ecfg (a + 4) (4k + 4)    in 4k² + 23k + 8a + 56 steps

for every counter `a ≥ 1` and gap `m ≥ 2` (`emap_sound`, kernel-checked for all values).  Inside an E-step the head
runs a loop (`loops`): each round turns three 0s of the gap into two more `10` on the right; when fewer than three 0s
are left, the remainder `m mod 3` decides what happens to the counter (`end1`, `end2`, `end0` in `Rules.lean`).

The run from blank tape reaches `Ecfg 4 124` at step 9008 (`blank_reaches_E`), so it follows `emap` for as long as
the counter stays positive (`orbit_sound`): halting needs the counter to come down to 0.
-/

namespace H48788

open TM

/-- The counter `1 0 (01)^a`, nearest cell first. -/
def Ctr (a : Nat) : Tape := rep a [true, false] (cons false (cons true blank))

/-- `1 0 0 (10)^a 0^m E> 1`. -/
def Ecfg (a m : Nat) : Config := ⟨rep (m + 1) [false] (Ctr a), cons true blank, .E⟩

/-- The loop: `P 0^x 1 B> 1 (10)^j 1 1`. -/
def Lp (P : Tape) (x j : Nat) : Config :=
  ⟨cons true (rep x [false] P), cons true (rep j [true, false] (cons true (cons true blank))), .B⟩

theorem rot_tail (j : Nat) :
    rep j [true, false] (cons true (cons true blank)) = cons true (rep j [false, true] (cons true blank)) := by
  have h := rep_rotate j [true] [false, true] [true, false] rfl (cons true blank)
  simp only [app_cons, app_nil] at h
  exact h.symm

theorem ff_rep (j : Nat) (X : Tape) : rep j [false, false] X = rep (2 * j) [false] X := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 2 * (j + 1) = (2 * j + 1) + 1 by omega, rep_succ, rep_succ, rep_succ, ih]
    rfl

theorem tf_rep (a b : Nat) (X : Tape) : rep a [true, false] (rep b [true, false] X) = rep (a + b) [true, false] X :=
  (rep_add a b _ X).symm

theorem f_rep (a b : Nat) (X : Tape) : rep a [false] (rep b [false] X) = rep (a + b) [false] X :=
  (rep_add a b _ X).symm

/-- One round of the loop. -/
theorem loop1 (P : Tape) (x j : Nat) : steps (4 * j + 11) (Lp P (x + 3) j) = some (Lp P x (j + 2)) := by
  have h := loop j x P
  rw [← rot_tail] at h
  exact h

/-- `k` rounds of the loop. -/
theorem loops (P : Tape) : ∀ k x j : Nat,
    steps (k * (4 * j + 11) + 4 * k * (k - 1)) (Lp P (x + 3 * k) j) = some (Lp P x (j + 2 * k)) := by
  intro k
  induction k with
  | zero => intro x j; simp only [Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.zero_sub]; rfl
  | succ k ih =>
    intro x j
    have h₁ := loop1 P (x + 3 * k) j
    have h₂ := ih x (j + 2)
    rw [show x + 3 * k + 3 = x + 3 * (k + 1) by omega] at h₁
    rw [show j + 2 + 2 * k = j + 2 * (k + 1) by omega] at h₂
    have e : (k + 1) * (4 * j + 11) + 4 * (k + 1) * (k + 1 - 1) = (4 * j + 11) + (k * (4 * (j + 2) + 11) + 4 * k * (k - 1)) := by
      cases k with
      | zero => simp
      | succ k => simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.add_sub_cancel]; omega
    rw [e]
    exact steps_seq trans h₁ h₂

/-- From an E-configuration to the loop. -/
theorem start' (P : Tape) (x : Nat) : steps 9 ⟨rep (x + 2) [false] P, cons true blank, .E⟩ = some (Lp P x 1) :=
  start x P

/-- m = 3k + 1 (counter at least 1): the counter loses one. -/
theorem map1 (a k : Nat) : steps (4 * k * k + 23 * k + 28) (Ecfg (a + 1) (3 * k + 1)) = some (Ecfg a (4 * k + 7)) := by
  have h₁ := start' (Ctr (a + 1)) (3 * k)
  have h₂ := loops (Ctr (a + 1)) k 0 1
  rw [Nat.zero_add, show 1 + 2 * k = 2 * k + 1 by omega] at h₂
  have h₃ := end1 a (2 * k)
  change steps _ (Lp (Ctr (a + 1)) 0 (2 * k + 1)) =
    some ⟨cons false (rep (2 * k + 1) [false, false] (rep 5 [false] (Ctr a))), cons true blank, .E⟩ at h₃
  rw [ff_rep, f_rep] at h₃
  have h := steps_seq trans h₁ (steps_seq trans h₂ h₃)
  rw [show 2 * (2 * k + 1) + 5 = 4 * k + 7 by omega] at h
  have e : 9 + (k * (4 * 1 + 11) + 4 * k * (k - 1) + (6 * (2 * k) + 19)) = 4 * k * k + 23 * k + 28 := by
    cases k with
    | zero => simp
    | succ k => simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.add_sub_cancel]; omega
  rw [e] at h
  exact h

/-- m = 3k + 2 (counter at least 1): the counter gains four. -/
theorem map2 (a k : Nat) :
    steps (4 * k * k + 23 * k + 8 * (a + 1) + 56) (Ecfg (a + 1) (3 * k + 2)) = some (Ecfg (a + 5) (4 * k + 4)) := by
  have h₁ := start' (Ctr (a + 1)) (3 * k + 1)
  have h₂ := loops (Ctr (a + 1)) k 1 1
  rw [show 1 + 3 * k = 3 * k + 1 by omega, show 1 + 2 * k = 2 * k + 1 by omega] at h₂
  have h₃ := end2 a (2 * k)
  change steps _ (Lp (Ctr (a + 1)) 1 (2 * k + 1)) =
    some ⟨cons false (rep (2 * k + 1) [false, false] (rep 2 [false] (cons true (cons false
      (rep a [true, false] (rep 4 [true, false] (cons false (cons true blank)))))))), cons true blank, .E⟩ at h₃
  rw [tf_rep] at h₃
  change steps _ _ = some ⟨cons false (rep (2 * k + 1) [false, false] (rep 2 [false] (Ctr (a + 4 + 1)))),
    cons true blank, .E⟩ at h₃
  rw [ff_rep, f_rep] at h₃
  have h := steps_seq trans h₁ (steps_seq trans h₂ h₃)
  rw [show 2 * (2 * k + 1) + 2 = 4 * k + 4 by omega, show a + 4 + 1 = a + 5 by omega] at h
  have e : 9 + (k * (4 * 1 + 11) + 4 * k * (k - 1) + (8 * a + 6 * (2 * k) + 55)) =
      4 * k * k + 23 * k + 8 * (a + 1) + 56 := by
    cases k with
    | zero => simp; omega
    | succ k => simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.add_sub_cancel]; omega
  rw [e] at h
  exact h

/-- The common tail of `map0`: what `end0`, `end0_1`, `end0_2` leave, as an E-configuration. -/
theorem end0_tail (j : Nat) (X : Tape) :
    cons false (rep (j + 1) [false, false] (rep 6 [false] X)) = rep (2 * j + 8 + 1) [false] X := by
  rw [ff_rep, f_rep, show 2 * (j + 1) + 6 = 2 * j + 8 by omega]
  rfl

/-- m = 3k + 3 (counter at least 3): the counter gains six. -/
theorem map0 (a k : Nat) :
    steps (4 * (k + 1) * (k + 1) + 23 * (k + 1) + 16 * (a + 3) + 94) (Ecfg (a + 3) (3 * k + 3)) =
      some (Ecfg (a + 9) (4 * k + 8)) := by
  have h₁ := start' (Ctr (a + 3)) (3 * k + 2)
  have h₂ := loops (Ctr (a + 3)) k 2 1
  rw [show 2 + 3 * k = 3 * k + 2 by omega, show 1 + 2 * k = 2 * k + 1 by omega] at h₂
  have h₃ := end0 a (2 * k)
  change steps _ (Lp (Ctr (a + 3)) 2 (2 * k + 1)) =
    some ⟨cons false (rep (2 * k + 1) [false, false] (rep 6 [false] (cons true (cons false
      (rep a [true, false] (rep 8 [true, false] (cons false (cons true blank)))))))), cons true blank, .E⟩ at h₃
  rw [tf_rep] at h₃
  change steps _ _ = some ⟨cons false (rep (2 * k + 1) [false, false] (rep 6 [false] (Ctr (a + 8 + 1)))),
    cons true blank, .E⟩ at h₃
  rw [end0_tail] at h₃
  have h := steps_seq trans h₁ (steps_seq trans h₂ h₃)
  rw [show 2 * (2 * k) + 8 = 4 * k + 8 by omega, show a + 8 + 1 = a + 9 by omega] at h
  have e : 9 + (k * (4 * 1 + 11) + 4 * k * (k - 1) + (16 * a + 10 * (2 * k) + 160)) =
      4 * (k + 1) * (k + 1) + 23 * (k + 1) + 16 * (a + 3) + 94 := by
    cases k with
    | zero => simp; omega
    | succ k => simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.add_sub_cancel]; omega
  rw [e] at h
  exact h

/-- m = 3k + 3 with a counter of 1. -/
theorem map0_1 (k : Nat) :
    steps (4 * (k + 1) * (k + 1) + 23 * (k + 1) + 16 * 1 + 94) (Ecfg 1 (3 * k + 3)) = some (Ecfg 7 (4 * k + 8)) := by
  have h₁ := start' (Ctr 1) (3 * k + 2)
  have h₂ := loops (Ctr 1) k 2 1
  rw [show 2 + 3 * k = 3 * k + 2 by omega, show 1 + 2 * k = 2 * k + 1 by omega] at h₂
  have h₃ := end0_1 (2 * k)
  change steps _ (Lp (Ctr 1) 2 (2 * k + 1)) =
    some ⟨cons false (rep (2 * k + 1) [false, false] (rep 6 [false] (Ctr 7))), cons true blank, .E⟩ at h₃
  rw [end0_tail] at h₃
  have h := steps_seq trans h₁ (steps_seq trans h₂ h₃)
  rw [show 2 * (2 * k) + 8 = 4 * k + 8 by omega] at h
  have e : 9 + (k * (4 * 1 + 11) + 4 * k * (k - 1) + (10 * (2 * k) + 128)) =
      4 * (k + 1) * (k + 1) + 23 * (k + 1) + 16 * 1 + 94 := by
    cases k with
    | zero => simp
    | succ k => simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.add_sub_cancel]; omega
  rw [e] at h
  exact h

/-- m = 3k + 3 with a counter of 2. -/
theorem map0_2 (k : Nat) :
    steps (4 * (k + 1) * (k + 1) + 23 * (k + 1) + 16 * 2 + 94) (Ecfg 2 (3 * k + 3)) = some (Ecfg 8 (4 * k + 8)) := by
  have h₁ := start' (Ctr 2) (3 * k + 2)
  have h₂ := loops (Ctr 2) k 2 1
  rw [show 2 + 3 * k = 3 * k + 2 by omega, show 1 + 2 * k = 2 * k + 1 by omega] at h₂
  have h₃ := end0_2 (2 * k)
  change steps _ (Lp (Ctr 2) 2 (2 * k + 1)) =
    some ⟨cons false (rep (2 * k + 1) [false, false] (rep 6 [false] (Ctr 8))), cons true blank, .E⟩ at h₃
  rw [end0_tail] at h₃
  have h := steps_seq trans h₁ (steps_seq trans h₂ h₃)
  rw [show 2 * (2 * k) + 8 = 4 * k + 8 by omega] at h
  have e : 9 + (k * (4 * 1 + 11) + 4 * k * (k - 1) + (10 * (2 * k) + 144)) =
      4 * (k + 1) * (k + 1) + 23 * (k + 1) + 16 * 2 + 94 := by
    cases k with
    | zero => simp
    | succ k => simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.add_sub_cancel]; omega
  rw [e] at h
  exact h

/-! ## The map as a function -/

/-- One E-step: the next counter, the next gap and the number of steps. -/
def emap (a m : Nat) : Nat × Nat × Nat :=
  let k := m / 3
  if m % 3 = 0 then (a + 6, 4 * k + 4, 4 * k * k + 23 * k + 16 * a + 94)
  else if m % 3 = 1 then (a - 1, 4 * k + 7, 4 * k * k + 23 * k + 28)
  else (a + 4, 4 * k + 4, 4 * k * k + 23 * k + 8 * a + 56)

/-- Every E-step with a positive counter and a gap of at least 2 is what `emap` says. -/
theorem emap_sound (a m : Nat) (ha : 1 ≤ a) (hm : 2 ≤ m) :
    steps (emap a m).2.2 (Ecfg a m) = some (Ecfg (emap a m).1 (emap a m).2.1) := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  obtain ⟨k, r, hr3, rfl⟩ : ∃ k r, r < 3 ∧ m = 3 * k + r :=
    ⟨m / 3, m % 3, Nat.mod_lt _ (by decide), (Nat.div_add_mod m 3).symm⟩
  have hr : (3 * k + r) % 3 = r := by omega
  have hq : (3 * k + r) / 3 = k := by omega
  simp only [emap, hr, hq]
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl
  · simp only [ite_true]
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [show 3 * (k' + 1) + 0 = 3 * k' + 3 by omega, show 4 * (k' + 1) + 4 = 4 * k' + 8 by omega]
    rcases (by omega : b = 0 ∨ b = 1 ∨ 2 ≤ b) with rfl | rfl | hb
    · exact map0_1 k'
    · exact map0_2 k'
    · obtain ⟨c, rfl⟩ : ∃ c, b = c + 2 := ⟨b - 2, by omega⟩
      have h := map0 c k'
      rw [show c + 2 + 1 = c + 3 by omega, show c + 2 + 1 + 6 = c + 9 by omega]
      exact h
  · simp only [show (1 = 0) = False from by simp, ite_false, ite_true]
    rw [show b + 1 - 1 = b by omega]
    exact map1 b k
  · simp only [show (2 = 0) = False from by simp, show (2 = 1) = False from by simp, ite_false]
    rw [show b + 1 + 4 = b + 5 by omega]
    exact map2 b k

end H48788
