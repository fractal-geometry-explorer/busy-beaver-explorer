import Rules

/-!
# Whole phases of 1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---

A phase starts at PS(M, T) = `0^inf F> 0 1^M T`.  It runs `start`, then one `round` per three ones, then one of the
`end_*` rules of `Rules.lean`, which turn the wall back into ones.  Here they are chained, for the empty tail and for
the tail `0 1^6` (written T6), in each residue of M mod 3: all six cases.  Written by hand.
-/

namespace H103424

open TM

theorem ones_cons (n : Nat) (X : Tape) : cons true (rep n [true] X) = rep (n + 1) [true] X := rfl

theorem ones_snoc (n : Nat) (X : Tape) : rep n [true] (cons true X) = rep (n + 1) [true] X :=
  rep_app_comm n [true] X

theorem steps_ones {s a b : Nat} {c : Config} {X : Tape} (h : a = b)
    (h3 : steps s c = some ⟨blank, cons false (rep a [true] X), .F⟩) :
    steps s c = some ⟨blank, cons false (rep b [true] X), .F⟩ := h ▸ h3

theorem pairs_ones (k : Nat) (X : Tape) : rep k [true, true] (cons true X) = rep (2 * k + 1) [true] X := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by omega, rep_succ, ih]
    rfl

theorem wall_four (k : Nat) (X : Tape) :
    cons true (cons false (cons true (cons false (cons true (cons false
      (rep k [true, false] (cons true (cons false X)))))))) = rep (k + 4) [true, false] X := by
  have h : rep k [true, false] (cons true (cons false X)) = rep (k + 1) [true, false] X :=
    rep_app_comm k [true, false] X
  rw [h]
  rfl

/-- j rounds: 3j ones are eaten and the wall gains 4j pairs. -/
theorem rounds (j k m : Nat) (R : Tape) : ∃ s,
    steps s ⟨blank, cons false (cons true (rep k [true, false] (rep (3 * j + m) [true] R))), .D⟩ =
      some ⟨blank, cons false (cons true (rep (k + 4 * j) [true, false] (rep m [true] R))), .D⟩ := by
  induction j generalizing k with
  | zero =>
    refine ⟨0, ?_⟩
    rw [show 3 * 0 + m = m by omega, show k + 4 * 0 = k by omega]
    rfl
  | succ j ih =>
    have h1 := round k (3 * j + m) R
    rw [wall_four] at h1
    obtain ⟨s, hs⟩ := ih (k + 4)
    rw [show 3 * (j + 1) + m = (3 * j + m) + 3 by omega, show k + 4 * (j + 1) = (k + 4) + 4 * j by omega]
    exact ⟨_, steps_seq trans h1 hs⟩

/-- The tail `0 1^6`. -/
abbrev T6 : Tape := cons false (rep 6 [true] blank)
/-- The tail `0 1 0 1 0 1^3` (blocks 1, 1, 3). -/
abbrev T113 : Tape := cons false (cons true (cons false (cons true (cons false (rep 3 [true] blank)))))

/-- PS(3j + 5, []) to PS(8j + 17, []): M = 2 mod 3, M' = (8M + 11)/3. -/
theorem phase_e0 (j : Nat) : ∃ s, steps s ⟨blank, cons false (rep (3 * j + 5) [true] blank), .F⟩ =
    some ⟨blank, cons false (rep (8 * j + 17) [true] blank), .F⟩ := by
  have h1 := start (3 * j) blank
  obtain ⟨s2, h2⟩ := rounds j 5 0 blank
  have h3 := end_e0 (5 + 4 * j)
  simp only [pairs_ones, ones_cons] at h3
  exact ⟨_, steps_seq trans h1 (steps_seq trans h2 (steps_ones (by omega) h3))⟩

/-- PS(3j + 6, []) to PS(8j + 19, []): M = 0 mod 3, M' = (8M + 9)/3. -/
theorem phase_e1 (j : Nat) : ∃ s, steps s ⟨blank, cons false (rep (3 * j + 6) [true] blank), .F⟩ =
    some ⟨blank, cons false (rep (8 * j + 19) [true] blank), .F⟩ := by
  have h1 := start (3 * j + 1) blank
  obtain ⟨s2, h2⟩ := rounds j 5 1 blank
  have h3 := end_e1 (5 + 4 * j)
  simp only [pairs_ones, ones_cons, ones_snoc] at h3
  rw [show 3 * j + 6 = 3 * j + 1 + 5 by omega]
  exact ⟨_, steps_seq trans h1 (steps_seq trans h2 (steps_ones (by omega) h3))⟩

/-- PS(3j + 7, []) to PS(8j + 13, [6]): M = 1 mod 3, M' = (8M - 17)/3, and a block of six ones is pushed. -/
theorem phase_e2 (j : Nat) : ∃ s, steps s ⟨blank, cons false (rep (3 * j + 7) [true] blank), .F⟩ =
    some ⟨blank, cons false (rep (8 * j + 13) [true] T6), .F⟩ := by
  have h1 := start (3 * j + 2) blank
  obtain ⟨s2, h2⟩ := rounds j 5 2 blank
  have h3 := end_e2 (3 + 4 * j)
  rw [show 3 + 4 * j + 2 = 5 + 4 * j by omega] at h3
  simp only [pairs_ones, ones_cons] at h3
  rw [show 3 * j + 7 = 3 * j + 2 + 5 by omega]
  exact ⟨_, steps_seq trans h1 (steps_seq trans h2 (steps_ones (by omega) h3))⟩

/-- PS(3j + 5, [6]) to PS(8j + 23, []): the tail is consumed. -/
theorem phase_s0 (j : Nat) : ∃ s, steps s ⟨blank, cons false (rep (3 * j + 5) [true] T6), .F⟩ =
    some ⟨blank, cons false (rep (8 * j + 23) [true] blank), .F⟩ := by
  have h1 := start (3 * j) T6
  obtain ⟨s2, h2⟩ := rounds j 5 0 T6
  have h3 := end_s0 (5 + 4 * j)
  simp only [pairs_ones, ones_cons, ones_snoc] at h3
  exact ⟨_, steps_seq trans h1 (steps_seq trans h2 (steps_ones (by omega) h3))⟩

/-- PS(3j + 6, [6]) to PS(8j + 35, []): the tail is consumed. -/
theorem phase_s1 (j : Nat) : ∃ s, steps s ⟨blank, cons false (rep (3 * j + 6) [true] T6), .F⟩ =
    some ⟨blank, cons false (rep (8 * j + 35) [true] blank), .F⟩ := by
  have h1 := start (3 * j + 1) T6
  obtain ⟨s2, h2⟩ := rounds j 5 1 T6
  have h3 := end_s1 (5 + 4 * j)
  simp only [pairs_ones, ones_cons, ones_snoc] at h3
  rw [show 3 * j + 6 = 3 * j + 1 + 5 by omega]
  exact ⟨_, steps_seq trans h1 (steps_seq trans h2 (steps_ones (by omega) h3))⟩

/-- PS(3j + 7, [6]) to PS(8j + 17, [1, 1, 3]). -/
theorem phase_s2 (j : Nat) : ∃ s, steps s ⟨blank, cons false (rep (3 * j + 7) [true] T6), .F⟩ =
    some ⟨blank, cons false (rep (8 * j + 17) [true] T113), .F⟩ := by
  have h1 := start (3 * j + 2) T6
  obtain ⟨s2, h2⟩ := rounds j 5 2 T6
  have h3 := end_s2 (4 + 4 * j)
  rw [show 4 + 4 * j + 1 = 5 + 4 * j by omega] at h3
  simp only [pairs_ones, ones_cons] at h3
  rw [show 3 * j + 7 = 3 * j + 2 + 5 by omega]
  exact ⟨_, steps_seq trans h1 (steps_seq trans h2 (steps_ones (by omega) h3))⟩

end H103424
