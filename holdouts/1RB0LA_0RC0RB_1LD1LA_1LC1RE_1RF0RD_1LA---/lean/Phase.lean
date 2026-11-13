import Rules

/-!
# The phases of 1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LA---

`Y P n g` is the tape  P (10)^n 111 0^(2g) B>0  with the head at the right end (P an arbitrary tape further left); a
phase starts at `Y P n 2`.  One round (`drain_Y`) takes two pairs and moves the right end six cells; a phase repeats
it until one or no pair is left (`drain_iter`).
-/

namespace H160156

open TM

/-- P (10)^n 111 0^(2g) B>0, the head at the right end. -/
def Y (P : Tape) (n g : Nat) : Config :=
  ⟨rep g [false, false] (cons true (cons true (cons true (rep n [false, true] P)))), blank, .B⟩

theorem rep_ff_cons (n : Nat) (s : Tape) :
    rep n [false, false] (cons false (cons false s)) = cons false (cons false (rep n [false, false] s)) :=
  rep_app_comm n [false, false] s

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

end H160156
