import Rules

/-!
# The phases of 1RB---_1LC0RB_0LD0LC_1RE1RB_1RD1LF_1LA0LE

`Y P n g` is the tape  C>0 0^(2g) 111 (01)^n P  with the head at the left end (P an arbitrary tape further right);
a phase starts at `Y P n 2`.  One round (`drain_Y`) takes two pairs and moves the right end six cells; a phase repeats
it until one or no pair is left (`drain_iter`).
-/

namespace H21328

open TM

/-- C>0 0^(2g) 111 (01)^n P, the head at the left end. -/
def Y (P : Tape) (n g : Nat) : Config :=
  ⟨blank, cons false (rep g [false, false] (cons true (cons true (cons true (rep n [false, true] P))))), .C⟩

theorem rep_ff_cons (n : Nat) (s : Tape) :
    rep n [false, false] (cons false (cons false s)) = cons false (cons false (rep n [false, false] s)) :=
  rep_app_comm n [false, false] s

theorem rep_f_cons (n : Nat) (s : Tape) : rep n [false, false] (cons false s) = cons false (rep n [false, false] s) :=
  (rep_rotate n [false] [false, false] [false, false] rfl s).symm

/-- One round of a phase. -/
theorem drain_Y (P : Tape) (c g : Nat) : steps (4 * g + 22) (Y P (c + 2) g) = some (Y P c (g + 3)) := by
  have r := drain c g P
  simp only [Y, rep_succ, app_cons, app_nil, rep_ff_cons, rep_f_cons] at r ⊢
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

end H21328
