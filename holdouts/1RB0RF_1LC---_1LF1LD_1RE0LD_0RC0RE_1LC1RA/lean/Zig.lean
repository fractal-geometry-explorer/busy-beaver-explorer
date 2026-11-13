import Rules

/-!
# 1RB0RF_1LC---_1LF1LD_1RE0LD_0RC0RE_1LC1RA: the E-zigzag

`Z x y L` is `L (10)^x 1 1 E> 0 1 1^(2y+1) 0^inf`: copies of `10` on the left, the head at the junction, a block of
ones at the right end of the tape.  Every round uses up two copies of `10` and adds six ones; by induction, j rounds
take `Z (x + 2j) y L` to `Z x (y + 3j) L`.  This is the half of a phase in which a stretch `(10)^k` is turned into
a block of about 3k ones.
-/

namespace H134470

open TM

/-- `c` reaches `c'` in some number of steps. -/
def Reaches (c c' : Config) : Prop := ∃ n, steps n c = some c'

theorem Reaches.trans {a b c : Config} (h₁ : Reaches a b) (h₂ : Reaches b c) : Reaches a c := by
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, steps_seq H134470.trans hn hm⟩

/-- `L (10)^x 1 1 E> 0 1 1 (11)^y 0^inf`. -/
def Z (x y : Nat) (L : Tape) : Config :=
  ⟨cons true (cons true (rep x [false, true] L)), cons false (cons true (cons true (rep y [true, true] blank))), .E⟩

theorem one_rot (m : Nat) (s : Tape) : cons true (rep m [true, true] s) = rep m [true, true] (cons true s) :=
  rep_rotate m [true] [true, true] [true, true] rfl s

theorem round' (x y : Nat) (L : Tape) : Reaches (Z (x + 2) y L) (Z x (y + 3) L) := by
  refine ⟨4 * y + 20, ?_⟩
  have h := e_round y (rep x [false, true] L)
  have e : cons true (cons true (cons true (cons true (cons true (cons true (rep y [true, true] (cons true blank))))))) =
      cons true (rep (y + 3) [true, true] blank) := by
    rw [← one_rot]; rfl
  rw [e] at h
  exact h

theorem zig (j : Nat) : ∀ x y L, Reaches (Z (x + 2 * j) y L) (Z x (y + 3 * j) L) := by
  induction j with
  | zero => intro x y L; exact ⟨0, rfl⟩
  | succ j ih =>
    intro x y L
    have h1 := round' (x + 2 * j) y L
    rw [show x + 2 * j + 2 = x + 2 * (j + 1) by omega] at h1
    have h2 := ih x (y + 3) L
    rw [show y + 3 + 3 * j = y + 3 * (j + 1) by omega] at h2
    exact h1.trans h2

end H134470
