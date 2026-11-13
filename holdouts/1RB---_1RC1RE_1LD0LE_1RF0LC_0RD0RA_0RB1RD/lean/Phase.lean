import Rules

/-!
# The phases of 1RB---_1RC1RE_1LD0LE_1RF0LC_0RD0RA_0RB1RD

`X P b c` is the tape  P 1^b (01)^c 0 A>0  with the head at the right end and P an arbitrary tape further left; a
phase starts at `X P n 2` (P 1^n 01010 A>0).  Each round turns three 1s of the counter into five pairs `01`
(`first_X`, `drain_X`), and any number of rounds at once (`drain_iter`).
-/

namespace H78977

open TM

def X (P : Tape) (b c : Nat) : Config := ⟨cons false (rep c [true, false] (rep b [true] P)), blank, .A⟩

theorem rep_tf_cons (n : Nat) (s : Tape) :
    rep n [true, false] (cons true (cons false s)) = cons true (cons false (rep n [true, false] s)) :=
  rep_app_comm n [true, false] s

theorem first_X (P : Tape) (b : Nat) : steps 57 (X P (b + 3) 2) = some (X P b 7) := by
  have r := first b P
  simp only [X, rep_succ, rep_zero, app_cons, app_nil, cons_false_blank] at r ⊢
  exact r

theorem drain_X (P : Tape) (b c : Nat) : steps (6 * c + 51) (X P (b + 3) (c + 1)) = some (X P b (c + 6)) := by
  have r := drain b c P
  simp only [X, rep_succ, app_cons, app_nil, rep_tf_cons, cons_false_blank] at r ⊢
  exact r

theorem drain_iter (P : Tape) (m : Nat) : ∀ b c, ∃ N, steps N (X P (b + 3 * m) (c + 1)) = some (X P b (c + 1 + 5 * m)) := by
  induction m with
  | zero => intro b c; exact ⟨0, rfl⟩
  | succ m ih =>
    intro b c
    obtain ⟨N, hN⟩ := ih b (c + 5)
    refine ⟨6 * c + 51 + N, ?_⟩
    have h1 := drain_X P (b + 3 * m) c
    rw [show b + 3 * (m + 1) = b + 3 * m + 3 by omega, show c + 1 + 5 * (m + 1) = c + 5 + 1 + 5 * m by omega]
    exact steps_seq trans h1 hN

end H78977
