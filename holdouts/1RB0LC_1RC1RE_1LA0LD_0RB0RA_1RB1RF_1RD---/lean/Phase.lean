import Rules

/-!
# The phases of 1RB0LC_1RC1RE_1LA0LD_0RB0RA_1RB1RF_1RD---

`W P n` is the tape  P 1^n 0 B>0  and `X P b c` the tape  P 1^b (01)^c B>0, both with the head at the right end and
P an arbitrary tape further left.  A phase starts at `W P n`.  Each round turns three 1s of the counter into four
pairs `01` (`first_X`, `drain_X`, any number of rounds: `drain_iter`).  When n is divisible by 3 and P ends with a
block `0 1^(a+1) 0`, the whole phase is proved for all values (`phase_zero`): that block is absorbed into the new
counter, n' = 8n/3 + a + 3.
-/

namespace H104936

open TM

def W (P : Tape) (n : Nat) : Config := ⟨cons false (rep n [true] P), blank, .B⟩

def X (P : Tape) (b c : Nat) : Config := ⟨rep c [true, false] (rep b [true] P), blank, .B⟩

theorem rep_tf_cons (n : Nat) (s : Tape) :
    rep n [true, false] (cons true (cons false s)) = cons true (cons false (rep n [true, false] s)) :=
  rep_app_comm n [true, false] s

theorem rep_add (x y : Nat) (w : List Bool) (s : Tape) : rep (x + y) w s = rep x w (rep y w s) := by
  induction x with
  | zero => simp
  | succ x ih => rw [show x + 1 + y = (x + y) + 1 by omega, rep_succ, rep_succ, ih]

theorem rep_two (k : Nat) (s : Tape) : rep k [true, true] s = rep (2 * k) [true] s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, rep_succ, rep_succ, rep_succ, ih]
    rfl

theorem first_X (P : Tape) (b : Nat) : steps 16 (W P (b + 3)) = some (X P b 3) := by
  have r := first b P
  simp only [W, X, rep_succ, rep_zero, app_cons, app_nil] at r ⊢
  exact r

theorem drain_X (P : Tape) (b c : Nat) : steps (6 * c + 33) (X P (b + 3) (c + 1)) = some (X P b (c + 5)) := by
  have r := drain b c P
  simp only [X, rep_succ, app_cons, app_nil, rep_tf_cons] at r ⊢
  exact r

theorem drain_iter (P : Tape) (m : Nat) : ∀ b c, ∃ N, steps N (X P (b + 3 * m) (c + 1)) = some (X P b (c + 1 + 4 * m)) := by
  induction m with
  | zero => intro b c; exact ⟨0, rfl⟩
  | succ m ih =>
    intro b c
    obtain ⟨N, hN⟩ := ih b (c + 4)
    refine ⟨6 * c + 33 + N, ?_⟩
    have h1 := drain_X P (b + 3 * m) c
    rw [show b + 3 * (m + 1) = b + 3 * m + 3 by omega, show c + 1 + 4 * (m + 1) = c + 4 + 1 + 4 * m by omega]
    exact steps_seq trans h1 hN

/-- A phase with n = 3m + 3 and P ending with the block `0 1^(a+1) 0`: the block joins the new counter. -/
theorem phase_zero (L : Tape) (a m : Nat) :
    ∃ N, 0 < N ∧ steps N (W (cons false (rep (a + 1) [true] (cons false L))) (3 * m + 3)) =
      some (W (cons false L) (a + 8 * m + 11)) := by
  obtain ⟨N, hN⟩ := drain_iter (cons false (rep (a + 1) [true] (cons false L))) m 0 2
  have h0 := first_X (cons false (rep (a + 1) [true] (cons false L))) (3 * m)
  have r := end0 a (4 * m + 2) L
  rw [rep_two] at r
  rw [show 0 + 3 * m = 3 * m by omega, show 2 + 1 + 4 * m = 4 * m + 2 + 1 by omega] at hN
  refine ⟨16 + (N + (4 * (4 * m + 2) + 16)), by omega, steps_seq trans h0 (steps_seq trans hN ?_)⟩
  rw [show a + 8 * m + 11 = 4 + (2 * (4 * m + 2) + (2 + (a + 1))) by omega, W, rep_add 4, rep_add (2 * (4 * m + 2)),
    rep_add 2]
  simp only [X, rep_zero] at r ⊢
  simp only [rep_succ (3 - 1), rep_succ (2 - 1), rep_succ 0, rep_succ 1, rep_succ 2, rep_zero, app_cons, app_nil] at r ⊢
  exact r

end H104936
