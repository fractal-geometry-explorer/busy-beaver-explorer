import Rules

/-!
# 1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD: the plain pass and the way to halt

At a *pass start* the tape is `B>0 0 (10)^a 1^b ...` with blank tape on the left.  `pass_plain` proves the plain
case of the pass map, `(a, b) ↦ (2a + 2, b − 2a − 2)` when `a ≥ 2` and `b ≥ 2a + 3`, for every `a`, `b` and every
tape `R` after the block of 1s: the pieces of `Rules.lean` (start, `a − 1` rounds by induction, end).  `zip_halts`
proves that the tape `B>0 0 (10)^n` with blank tape after it halts.  The other cases of the pass map (rebounds off
the right end) are not proved here; see the README.
-/

namespace H149707

open TM

theorem cons_rep_tt (n : Nat) (Y : Tape) : cons true (rep n [true, true] Y) = rep n [true, true] (cons true Y) :=
  rep_rotate n [true] [true, true] [true, true] rfl Y

theorem cons_rep_t (n : Nat) (Y : Tape) : cons true (rep n [true] Y) = rep (n + 1) [true] Y := by
  have h := rep_rotate n [true] [true] [true] rfl Y
  have h2 := rep_app_comm n [true] Y
  exact h.trans h2

theorem cons_rep_tf (n : Nat) (Y : Tape) : cons true (rep n [false, true] Y) = rep n [true, false] (cons true Y) :=
  rep_rotate n [true] [false, true] [true, false] rfl Y

/-- One round, in the form that iterates. -/
theorem round (k p s : Nat) (L R : Tape) :
    ∃ n, steps n ⟨rep (2 * k + 2) [true, true] (rep (p + 1) [false, true] L), rep (s + 3) [true] R, .A⟩ =
      some ⟨rep (2 * k + 4) [true, true] (rep p [false, true] L), rep (s + 1) [true] R, .A⟩ := by
  have h := cycle k p s L R
  have e1 : cons true (rep (2 * k + 2) [true, true] (cons true (cons true (cons true (rep p [false, true] L))))) =
      rep (2 * k + 4) [true, true] (rep p [false, true] L) := by
    rw [cons_rep_tt]
    have h1 := rep_app_comm (2 * k + 2) [true, true] (app [true, true] (rep p [false, true] L))
    have h2 := rep_app_comm (2 * k + 2 + 1) [true, true] (rep p [false, true] L)
    exact h1.trans h2
  rw [e1, cons_rep_t] at h
  exact ⟨_, h⟩

/-- `j` rounds. -/
theorem rounds (j : Nat) : ∀ (k p s : Nat) (L R : Tape),
    ∃ n, steps n ⟨rep (2 * k + 2) [true, true] (rep (p + j) [false, true] L), rep (s + 2 * j + 1) [true] R, .A⟩ =
      some ⟨rep (2 * (k + j) + 2) [true, true] (rep p [false, true] L), rep (s + 1) [true] R, .A⟩ := by
  induction j with
  | zero => intro k p s L R; exact ⟨0, by simp⟩
  | succ j ih =>
    intro k p s L R
    obtain ⟨n1, h1⟩ := round k (p + j) (s + 2 * j) L R
    obtain ⟨n2, h2⟩ := ih (k + 1) p s L R
    have e1 : p + (j + 1) = p + j + 1 := by omega
    have e2 : s + 2 * (j + 1) + 1 = s + 2 * j + 3 := by omega
    have e3 : 2 * (k + 1) + 2 = 2 * k + 4 := by omega
    have e4 : 2 * (k + 1 + j) + 2 = 2 * (k + (j + 1)) + 2 := by omega
    rw [e3, e4] at h2
    rw [e1, e2]
    exact ⟨n1 + n2, steps_seq trans h1 h2⟩

/-- The plain pass: `B>0 0 (10)^(a+2) 1^(s+2a+7) R` reaches `B>0 0 (10)^(2a+6) 1^(s+1) R`, for all a, s and R.
In pass-map terms: (A, B) ↦ (2A + 2, B − 2A − 2) for A ≥ 2 and B ≥ 2A + 3. -/
theorem pass_plain (a s : Nat) (R : Tape) :
    ∃ n, steps n ⟨blank, cons false (cons false (rep (a + 2) [true, false] (rep (s + 2 * a + 7) [true] R))), .B⟩ =
      some ⟨blank, cons false (cons false (rep (2 * a + 6) [true, false] (rep (s + 1) [true] R))), .B⟩ := by
  -- start
  have h1 := pass_start a (s + 2 * a + 4) R
  have eL : cons true (cons true (cons true (rep (a + 1) [true, false] (cons true (cons false blank))))) =
      rep (2 * 0 + 2) [true, true] (rep (0 + (a + 1)) [false, true] blank) := by
    rw [cons_false_blank, ← cons_rep_tf]
    simp only [Nat.mul_zero, Nat.zero_add]
    rfl
  have eR : cons true (cons true (rep (s + 2 * a + 4 + 1) [true] R)) = rep (s + 4 + 2 * (a + 1) + 1) [true] R := by
    rw [cons_rep_t, cons_rep_t]
    congr 1
    omega
  have eS : s + 2 * a + 4 + 3 = s + 2 * a + 7 := by omega
  rw [eL, eR, eS] at h1
  -- rounds
  obtain ⟨n2, h2⟩ := rounds (a + 1) 0 0 (s + 4) blank R
  -- end
  have h3 := pass_end (2 * a + 3) s R
  have e5 : 2 * (0 + (a + 1)) + 2 = 2 * a + 3 + 1 := by omega
  have e6 : s + 4 + 1 = s + 5 := by omega
  rw [e5, e6] at h2
  simp only [rep_zero] at h2
  have eE : cons false (cons false (cons true (cons false (cons true (rep (2 * a + 3 + 1) [false, true]
      (cons false (cons true (rep s [true] R)))))))) =
      cons false (cons false (rep (2 * a + 6) [true, false] (rep (s + 1) [true] R))) := by
    have hY : cons true (rep s [true] R) = rep (s + 1) [true] R := cons_rep_t s R
    have hX : cons true (rep (2 * a + 3 + 1) [false, true] (cons false (rep (s + 1) [true] R))) =
        rep (2 * a + 3 + 1 + 1) [true, false] (rep (s + 1) [true] R) := by
      rw [cons_rep_tf]
      exact rep_app_comm _ _ _
    rw [hY, hX, show 2 * a + 6 = (2 * a + 3 + 1 + 1) + 1 by omega, rep_succ]
    rfl
  rw [eE] at h3
  exact ⟨_, steps_seq trans h1 (steps_seq trans h2 h3)⟩

/-- From `B>0 0 (10)^n` and blank tape the machine halts after `2n + 5` steps: C and E zip right over the `10`s and E
reads a blank. -/
theorem zip_halts (n : Nat) :
    ∃ c, steps (2 * n + 4) ⟨blank, cons false (cons false (rep n [true, false] blank)), .B⟩ = some c ∧ step c = none :=
  ⟨_, zip_halt n, rfl⟩

end H149707
