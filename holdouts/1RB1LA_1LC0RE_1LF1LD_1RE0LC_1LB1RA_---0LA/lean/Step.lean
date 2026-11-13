import Rules

/-!
# 1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA: the step of a phase

`W x b R` is `0^inf A> 1^x 0 1 0 1 1^b R`, the head in state A on the first cell.  `S x c R = W x 6 ((01)^c R)` is
the phase configuration S(x, c) of the README with the rest of the tape R (for the run, R is `1^t 0 1 1 0^inf`).

Each round turns W(x+2, b+1, R) into W(x, b+4, R) (`round`); at x = 2 or 1 the middle block becomes the new left
block and two copies of `01` are used (`end2`, `end1`).  Together: **S(x, c+2) reaches S(⌊3x/2⌋+7, c)** for every
x ≥ 1, c and R (`step_rule`).
-/

namespace H130861

open TM

def W (x b : Nat) (R : Tape) : Config :=
  ⟨blank, rep x [true] (cons false (cons true (cons false (cons true (rep b [true] R))))), .A⟩
def S (x c : Nat) (R : Tape) : Config := W x 6 (rep c [false, true] R)

theorem n_tt (n : Nat) (s : Tape) : rep n [true, true] s = rep (2 * n) [true] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    simp [ih]

theorem n_cons (n : Nat) (s : Tape) : cons true (rep n [true] s) = rep (n + 1) [true] s := rfl
theorem n_rep (a b : Nat) (s : Tape) : rep a [true] (rep b [true] s) = rep (a + b) [true] s := (rep_add a b _ s).symm
theorem n_false (s : Tape) : cons true (cons false s) = rep 1 [true] (cons false s) := rfl

theorem rep_congr {a b : Nat} {s s' : Tape} (w : List Bool) (h : a = b) (hs : s = s') : rep a w s = rep b w s' := by
  rw [h, hs]
theorem cons_congr {s s' : Tape} (x : Bool) (h : s = s') : cons x s = cons x s' := by rw [h]
theorem cfg_congr {l l' r r' : Tape} (q : St) (h₁ : l = l') (h₂ : r = r') :
    (⟨l, r, q⟩ : Config) = ⟨l', r', q⟩ := by rw [h₁, h₂]

/-- Normalise both sides to blocks `rep N [true]` and match the counts with `omega`. -/
macro "tnorm" : tactic => `(tactic| (
  simp only [W, S, n_tt, n_false, n_cons, n_rep, rep_zero];
  repeat (first | rfl | (apply cfg_congr) | (apply rep_congr; omega) | (apply cons_congr))))

/-- `c` reaches `c'` in a positive number of steps. -/
def Reaches1 (c c' : Config) : Prop := ∃ n, 0 < n ∧ steps n c = some c'

theorem of_rule {c c' d d' : Config} {n : Nat} (hn : 0 < n) (h : steps n c = some c') (e : d = c) (e' : d' = c') :
    Reaches1 d d' := ⟨n, hn, by rw [e, e']; exact h⟩

theorem Reaches1.trans {a b c : Config} (h₁ : Reaches1 a b) (h₂ : Reaches1 b c) : Reaches1 a c := by
  obtain ⟨n, hn, h⟩ := h₁
  obtain ⟨m, _, h'⟩ := h₂
  exact ⟨n + m, by omega, steps_seq H130861.trans h h'⟩

theorem parity (n : Nat) : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩

/-- One round: `W(x+2, b+1, R) -> W(x, b+4, R)` for x ≥ 1. -/
theorem round (x b : Nat) (R : Tape) : Reaches1 (W (x + 3) (b + 1) R) (W (x + 1) (b + 4) R) := by
  rcases parity x with ⟨k, rfl | rfl⟩
  · cases k with
    | zero => exact of_rule (by omega) (round_3 b R) (by tnorm) (by tnorm)
    | succ k => exact of_rule (by omega) (round_o b k R) (by tnorm) (by tnorm)
  · cases k with
    | zero => exact of_rule (by omega) (round_4 b R) (by tnorm) (by tnorm)
    | succ k => exact of_rule (by omega) (round_e b k R) (by tnorm) (by tnorm)

/-- r rounds: `W(x+2r, b+1, R) -> W(x, b+3r+1, R)` for x ≥ 1. -/
theorem rounds (r : Nat) : ∀ x b R, Reaches1 (W (x + 1 + 2 * (r + 1)) (b + 1) R) (W (x + 1) (b + 3 * (r + 1) + 1) R) := by
  induction r with
  | zero =>
    intro x b R
    have h := round x b R
    rw [show x + 1 + 2 * (0 + 1) = x + 3 by omega, show b + 3 * (0 + 1) + 1 = b + 4 by omega]; exact h
  | succ r ih =>
    intro x b R
    have h1 := round (x + 2 * (r + 1)) b R
    have h2 := ih x (b + 3) R
    rw [show x + 2 * (r + 1) + 3 = x + 1 + 2 * (r + 1 + 1) by omega,
      show x + 2 * (r + 1) + 1 = x + 1 + 2 * (r + 1) by omega] at h1
    rw [show b + 3 + 3 * (r + 1) + 1 = b + 3 * (r + 1 + 1) + 1 by omega] at h2
    exact h1.trans h2

/-- The end at x = 2: `W(2, b, (01)^(c+2) R) -> S(b+4, c, R)` for b ≥ 6. -/
theorem end2 (b c : Nat) (R : Tape) :
    Reaches1 (W 2 (b + 6) (rep (c + 2) [false, true] R)) (S (b + 10) c R) := by
  rcases parity b with ⟨k, rfl | rfl⟩
  · exact of_rule (by omega) (end_e_e k c R) (by simp only [rep_succ, app_cons, app_nil]; tnorm) (by tnorm)
  · exact of_rule (by omega) (end_e_o k c R) (by simp only [rep_succ, app_cons, app_nil]; tnorm) (by tnorm)

/-- The end at x = 1: `W(1, b, (01)^(c+2) R) -> S(b+2, c, R)` for b ≥ 6. -/
theorem end1 (b c : Nat) (R : Tape) :
    Reaches1 (W 1 (b + 6) (rep (c + 2) [false, true] R)) (S (b + 8) c R) := by
  rcases parity b with ⟨k, rfl | rfl⟩
  · exact of_rule (by omega) (end_o_e k c R) (by simp only [rep_succ, app_cons, app_nil]; tnorm) (by tnorm)
  · exact of_rule (by omega) (end_o_o k c R) (by simp only [rep_succ, app_cons, app_nil]; tnorm) (by tnorm)

/-- **The step: S(x, c+2) reaches S(⌊3x/2⌋+7, c), for every x ≥ 1, every c and every rest of the tape R.** -/
theorem step_rule (x c : Nat) (R : Tape) : Reaches1 (S (x + 1) (c + 2) R) (S (3 * (x + 1) / 2 + 7) c R) := by
  rcases parity x with ⟨r, rfl | rfl⟩
  · -- x + 1 = 2r + 1
    cases r with
    | zero =>
      have h := end1 0 c R
      simpa [S] using h
    | succ r =>
      have h1 := rounds r 0 5 (rep (c + 2) [false, true] R)
      have h2 := end1 (3 * (r + 1)) c R
      rw [show 5 + 3 * (r + 1) + 1 = 3 * (r + 1) + 6 by omega] at h1
      rw [show 3 * (r + 1) + 8 = 3 * (2 * (r + 1) + 1) / 2 + 7 by omega] at h2
      have h := h1.trans h2
      simpa [S, show 0 + 1 + 2 * (r + 1) = 2 * (r + 1) + 1 by omega] using h
  · -- x + 1 = 2r + 2
    cases r with
    | zero =>
      have h := end2 0 c R
      simpa [S] using h
    | succ r =>
      have h1 := rounds r 1 5 (rep (c + 2) [false, true] R)
      have h2 := end2 (3 * (r + 1)) c R
      rw [show 5 + 3 * (r + 1) + 1 = 3 * (r + 1) + 6 by omega] at h1
      rw [show 3 * (r + 1) + 10 = 3 * (2 * (r + 1) + 1 + 1) / 2 + 7 by omega] at h2
      have h := h1.trans h2
      simpa [S, show 1 + 1 + 2 * (r + 1) = 2 * (r + 1) + 1 + 1 by omega] using h

end H130861
