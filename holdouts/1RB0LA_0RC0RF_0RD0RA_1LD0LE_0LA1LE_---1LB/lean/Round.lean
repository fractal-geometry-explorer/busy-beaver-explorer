import Rules

/-!
# 1RB0LA_0RC0RF_0RD0RA_1LD0LE_0LA1LE_---1LB: a whole round when the first block has length 4k + 4

At the left end, in state E, the tape is blocks of ones separated by single 0s: `E> 0 1^x 0 1^a 0 1^b ...`.  When
`x = 4k + 4` the round is: the sweep turns the first block into `0 1` pairs; the glider it ends with crosses the
second block and lands on the hole after it; the hole moves 3 cells left; then every two pairs make another glider,
each moving the hole 3 more cells left (`cycle`, iterated here by induction: `gliders`).  The round ends with E at the
left end again and the blocks `[x, a, b, ...]` turned into `[a + k + 1, 3(k + 1) + 3 + b, ...]` (`round_mod4`): the
hole after the second block is gone, 3 ones are new.
-/

namespace H77933

open TM

/-- `n` copies of `111` are `3n` ones. -/
theorem rep_three (n : Nat) (S : Tape) : rep (3 * n) [true] S = rep n [true, true, true] S := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by omega]; simp only [rep_succ, ih]; rfl

/-- `j` gliders in a row: `L 1 0 (10)^(2j) 1 E> 0 1^(p+2) 0 1 R` becomes `L 1 0 1 E> 0 1^(p+2+j) 0 1 (111)^j R`. -/
theorem gliders (X : Tape) (j : Nat) : ∀ (p : Nat) (R : Tape), ∃ n,
    steps n ⟨cons true (rep (2 * j) [false, true] X), cons false (rep (p + 2) [true] (cons false (cons true R))), .E⟩ =
      some ⟨cons true X, cons false (rep (p + 2 + j) [true] (cons false (cons true (rep j [true, true, true] R)))), .E⟩ := by
  induction j with
  | zero => intro p R; exact ⟨0, by simp [steps]⟩
  | succ j ih =>
    intro p R
    have h1 := cycle p (rep (2 * j) [false, true] X) R
    have e1 : rep (2 * (j + 1)) [false, true] X =
        cons false (cons true (cons false (cons true (rep (2 * j) [false, true] X)))) := by
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega]; rfl
    have e2 : cons true (cons true (cons true (rep p [true]
        (cons false (cons true (cons true (cons true (cons true R)))))))) =
        rep (p + 1 + 2) [true] (cons false (cons true (app [true, true, true] R))) := rfl
    rw [e2] at h1
    obtain ⟨n, h2⟩ := ih (p + 1) (app [true, true, true] R)
    rw [rep_app_comm, show p + 1 + 2 + j = p + 2 + (j + 1) by omega] at h2
    exact ⟨_, by rw [e1]; exact steps_seq trans h1 h2⟩

/-- A round from a first block of length `4k + 4` (second block `a + 3`, third block starting with a 1):
`E> 0 1^(4k+4) 0 1^(a+3) 0 1 R` at the left end becomes `E> 0 1^(a+k+4) 0 1^(3k+7) R`, again at the left end. -/
theorem round_mod4 (k a : Nat) (R : Tape) : ∃ n,
    steps n ⟨blank, cons false (rep (2 * k + 2) [true, true] (cons false (rep (a + 3) [true] (cons false (cons true R))))), .E⟩ =
      some ⟨blank, cons false (rep (a + k + 4) [true] (cons false (rep (3 * k + 7) [true] R))), .E⟩ := by
  have h1 := first a (2 * k) R
  have e1 : cons true (cons true (cons true (rep a [true] (cons false (cons true (cons true (cons true (cons true R)))))))) =
      rep (a + 1 + 2) [true] (cons false (cons true (app [true, true, true] R))) := rfl
  rw [e1] at h1
  obtain ⟨n2, h2⟩ := gliders (cons false (cons true blank)) k (a + 1) (app [true, true, true] R)
  have h3 := last (a + 1 + k) (rep k [true, true, true] (app [true, true, true] R))
  rw [show a + 1 + 2 + k = a + 1 + k + 2 by omega] at h2
  have e3 : cons false (cons true (cons true (cons true (rep (a + 1 + k) [true] (cons false (cons true (cons true
      (cons true (cons true (rep k [true, true, true] (app [true, true, true] R))))))))))) =
      cons false (rep (a + k + 4) [true] (cons false (rep (3 * k + 7) [true] R))) := by
    rw [← rep_three]
    show cons false (rep 3 [true] (rep (a + 1 + k) [true] (cons false (rep 4 [true] (rep (3 * k) [true]
      (rep 3 [true] R)))))) = _
    rw [← rep_add 3 (a + 1 + k), ← rep_add (3 * k) 3, ← rep_add 4 (3 * k + 3),
      show 3 + (a + 1 + k) = a + k + 4 by omega, show 4 + (3 * k + 3) = 3 * k + 7 by omega]
  rw [e3] at h3
  exact ⟨_, steps_seq trans h1 (steps_seq trans h2 h3)⟩

/-- A round from a first block of length `4k + 6` (second block `a + 4`, third block starting with a 1):
`E> 0 1^(4k+6) 0 1^(a+4) 0 1 R` at the left end becomes `E> 0 1^(a+k+5) 0 1^(3k+10) R`, again at the left end.
The last pair of the sweep and the two 0s it leaves at the left end make one glider more than in `round_mod4`. -/
theorem round_mod2 (k a : Nat) (R : Tape) : ∃ n,
    steps n ⟨blank, cons false (rep (2 * k + 3) [true, true] (cons false (rep (a + 4) [true] (cons false (cons true R))))), .E⟩ =
      some ⟨blank, cons false (rep (a + k + 5) [true] (cons false (rep (3 * k + 10) [true] R))), .E⟩ := by
  have h1 := first (a + 1) (2 * k + 1) R
  have e0 : rep (2 * k + 1) [false, true] (cons false (cons true blank)) =
      rep (2 * k) [false, true] (cons false (cons true (cons false (cons true blank)))) := by
    rw [rep_add]; rfl
  have e1 : cons true (cons true (cons true (rep (a + 1) [true] (cons false (cons true (cons true (cons true (cons true R)))))))) =
      rep (a + 2 + 2) [true] (cons false (cons true (app [true, true, true] R))) := rfl
  rw [e0, e1] at h1
  obtain ⟨n2, h2⟩ := gliders (cons false (cons true (cons false (cons true blank)))) k (a + 2) (app [true, true, true] R)
  have h3 := last2 (a + k) (rep k [true, true, true] (app [true, true, true] R))
  rw [show a + 2 + 2 + k = a + k + 4 by omega] at h2
  have e3 : cons false (cons true (cons true (cons true (cons true (cons true (rep (a + k) [true] (cons false (cons true
      (cons true (cons true (cons true (cons true (cons true (cons true (rep k [true, true, true]
      (app [true, true, true] R)))))))))))))))) =
      cons false (rep (a + k + 5) [true] (cons false (rep (3 * k + 10) [true] R))) := by
    rw [← rep_three]
    show cons false (rep 5 [true] (rep (a + k) [true] (cons false (rep 7 [true] (rep (3 * k) [true]
      (rep 3 [true] R)))))) = _
    rw [← rep_add 5 (a + k), ← rep_add (3 * k) 3, ← rep_add 7 (3 * k + 3),
      show 5 + (a + k) = a + k + 5 by omega, show 7 + (3 * k + 3) = 3 * k + 10 by omega]
  rw [e3] at h3
  exact ⟨_, steps_seq trans h1 (steps_seq trans h2 h3)⟩

end H77933
