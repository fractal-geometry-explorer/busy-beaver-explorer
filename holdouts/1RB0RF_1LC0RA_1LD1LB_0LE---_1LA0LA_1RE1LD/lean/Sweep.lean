import Rules

/-!
# 1RB0RF_1LC0RA_1LD1LB_0LE---_1LA0LA_1RE1LD: the sweep that turns ones into copies of `01`

`Y m y` is `0^inf D> (01)^m 1 (11)^y 0^inf`: the whole tape is m copies of `01` followed by a block of 2y+1 ones,
the head in state D on the first cell.  `Ye m y` is the same with 2y ones.  Each round turns two ones into a copy of `01` and adds one more copy at the
left end; by induction, `Y (x+2) (y+j)` reaches `Y (x+2+2j) y`.
-/

namespace H10442

open TM

/-- `c` reaches `c'` in some number of steps. -/
def Reaches (c c' : Config) : Prop := ∃ n, steps n c = some c'

theorem Reaches.trans {a b c : Config} (h₁ : Reaches a b) (h₂ : Reaches b c) : Reaches a c := by
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, steps_seq H10442.trans hn hm⟩

/-- `0^inf D> (01)^m 1 (11)^y 0^inf`. -/
def Y (m y : Nat) : Config := ⟨blank, rep m [false, true] (cons true (rep y [true, true] blank)), .D⟩

/-- `0^inf D> (01)^m (11)^y 0^inf`. -/
def Ye (m y : Nat) : Config := ⟨blank, rep m [false, true] (rep y [true, true] blank), .D⟩

theorem round' (x y : Nat) : Reaches (Y (x + 2) (y + 1)) (Y (x + 4) y) := ⟨_, d_round x y⟩

theorem round_e (x y : Nat) : Reaches (Ye (x + 2) (y + 1)) (Ye (x + 4) y) := ⟨_, d_round_e x y⟩

theorem sweep (j : Nat) : ∀ x y, Reaches (Y (x + 2) (y + j)) (Y (x + 2 + 2 * j) y) := by
  induction j with
  | zero => intro x y; exact ⟨0, rfl⟩
  | succ j ih =>
    intro x y
    have h1 := round' x (y + j)
    rw [show y + j + 1 = y + (j + 1) by omega] at h1
    have h2 := ih (x + 2) y
    rw [show x + 2 + 2 + 2 * j = x + 2 + 2 * (j + 1) by omega] at h2
    exact h1.trans h2

theorem sweep_e (j : Nat) : ∀ x y, Reaches (Ye (x + 2) (y + j)) (Ye (x + 2 + 2 * j) y) := by
  induction j with
  | zero => intro x y; exact ⟨0, rfl⟩
  | succ j ih =>
    intro x y
    have h1 := round_e x (y + j)
    rw [show y + j + 1 = y + (j + 1) by omega] at h1
    have h2 := ih (x + 2) y
    rw [show x + 2 + 2 + 2 * j = x + 2 + 2 * (j + 1) by omega] at h2
    exact h1.trans h2

/-- `0^inf C> 1^(2x+2) 0^inf` reaches `Y (2x+3) 0`, that is `0^inf D> (01)^(2x+3) 1 0^inf`: a block of ones,
the head in C at its left end, is turned into copies of `01`. -/
theorem ones_to_pairs (x : Nat) :
    Reaches ⟨blank, cons true (cons true (rep x [true, true] blank)), .C⟩ (Y (2 * x + 3) 0) := by
  have h1 : Reaches ⟨blank, cons true (cons true (rep x [true, true] blank)), .C⟩ (Y 3 x) := by
    exact ⟨_, steps_seq H10442.trans (c_start x) (d_first x)⟩
  have h2 := sweep x 1 0
  rw [show (0 : Nat) + x = x by omega, show 1 + 2 + 2 * x = 2 * x + 3 by omega] at h2
  exact h1.trans h2

/-- `0^inf A> 1 1 (01)^x 0^inf` reaches `0^inf C> 1^(2x+6) 0^inf` (written `1^5 (11)^x 1`). -/
theorem pairs_to_ones (x : Nat) :
    Reaches ⟨blank, cons true (cons true (rep x [false, true] blank)), .A⟩
      ⟨blank, cons true (cons true (cons true (cons true (cons true (rep x [true, true] (cons true blank)))))), .C⟩ :=
  ⟨_, fill x⟩

end H10442
