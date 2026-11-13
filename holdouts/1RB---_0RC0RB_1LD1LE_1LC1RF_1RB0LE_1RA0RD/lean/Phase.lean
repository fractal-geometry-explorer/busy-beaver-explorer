import Rules

/-!
# The phases of 1RB---_0RC0RB_1LD1LE_1LC1RF_1RB0LE_1RA0RD

`Y P n g` is the tape  P (10)^n 111 0^(2g) B>0  with the head at the right end (P an arbitrary tape further left);
a phase starts at `Y P n 0`.  One round (`drain`) takes two pairs and moves the right end six cells; a phase repeats
it until one or no pair is left (`drain_iter`), and for P empty the last round is proved for all lengths
(`phase_even`, `phase_odd`): the phase from (ε, n) goes to (ε, 3n/2 + 6) for even n and to (1, (3n + 9)/2) for odd n.
-/

namespace H82614

open TM

/-- P (10)^n 111 0^(2g) B>0, the head at the right end. -/
def Y (P : Tape) (n g : Nat) : Config :=
  ⟨rep g [false, false] (cons true (cons true (cons true (rep n [false, true] P)))), blank, .B⟩

theorem rep_ff_cons (n : Nat) (s : Tape) :
    rep n [false, false] (cons false (cons false s)) = cons false (cons false (rep n [false, false] s)) :=
  rep_app_comm n [false, false] s

theorem rep_ft_cons (n : Nat) (s : Tape) :
    rep n [false, true] (cons false (cons true s)) = cons false (cons true (rep n [false, true] s)) :=
  rep_app_comm n [false, true] s

theorem rot_tf (n : Nat) (s : Tape) : cons false (rep n [true, false] s) = rep n [false, true] (cons false s) :=
  rep_rotate n [false] [true, false] [false, true] rfl s

/-- One round of a phase. -/
theorem drain_Y (P : Tape) (c g : Nat) : steps (4 * g + 22) (Y P (c + 2) g) = some (Y P c (g + 3)) := by
  have r := drain c g P
  simp only [Y, rep_succ, app_cons, app_nil, rep_ff_cons] at r ⊢
  exact r

/-- m rounds. -/
theorem drain_iter (P : Tape) (m : Nat) : ∀ c g, ∃ N, steps N (Y P (c + 2 * m) g) = some (Y P c (g + 3 * m)) := by
  induction m with
  | zero => intro c g; exact ⟨0, rfl⟩
  | succ m ih =>
    intro c g
    obtain ⟨N, hN⟩ := ih c (g + 3)
    refine ⟨4 * g + 22 + N, ?_⟩
    have h1 := drain_Y P (c + 2 * m) g
    rw [show c + 2 * (m + 1) = c + 2 * m + 2 by omega, show g + 3 * (m + 1) = g + 3 + 3 * m by omega]
    exact steps_seq trans h1 hN

/-- A phase from P empty and n = 2m + 2 even: back to P empty with n = 3m + 9. -/
theorem phase_even (m : Nat) : ∃ N, 0 < N ∧ steps N (Y blank (2 * m + 2) 0) = some (Y blank (3 * m + 9) 0) := by
  obtain ⟨N, hN⟩ := drain_iter blank m 2 0
  have r := end_even (3 * m)
  rw [show 2 + 2 * m = 2 * m + 2 by omega, show 0 + 3 * m = 3 * m by omega] at hN
  simp only [rot_tf] at r
  simp only [Y, rep_succ, rep_zero, app_cons, app_nil, rep_ft_cons, cons_false_blank] at r hN ⊢
  exact ⟨N + (16 * (3 * m) + 127), by omega, steps_seq trans hN r⟩

/-- A phase from P empty and n = 2m + 1 odd: to P = 1 with n = 3m + 6. -/
theorem phase_odd (m : Nat) :
    ∃ N, 0 < N ∧ steps N (Y blank (2 * m + 1) 0) = some (Y (cons true blank) (3 * m + 6) 0) := by
  obtain ⟨N, hN⟩ := drain_iter blank m 1 0
  have r := end_odd (3 * m)
  rw [show 1 + 2 * m = 2 * m + 1 by omega, show 0 + 3 * m = 3 * m by omega] at hN
  simp only [Y, rep_succ, rep_zero, app_cons, app_nil, rep_ft_cons, cons_false_blank] at r hN ⊢
  exact ⟨N + (12 * (3 * m) + 77), by omega, steps_seq trans hN r⟩

end H82614
