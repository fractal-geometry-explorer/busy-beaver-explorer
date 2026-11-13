import Machine
import Rules

/-!
# 1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RD---: the feeding rule, restated and iterated

`Fd k m L` is the configuration `L (01)^k 1 (01)^m 1 F> 0^inf`: the head in state F just right of the tape, a
block of m copies of 01 at the end, and before it, past a single 1, a block of k copies.  One visit of the right
end (`feed`, from `Rules.lean`) takes `Fd (k+1) m L` to `Fd k (m+3) L` (`feed'`); `feeds` iterates it: the block
on the left is used up one copy at a time while the block at the end grows by three per copy, so a block of k
copies becomes one of 4k at the end (with the copy of the cursor).
-/

namespace H124060

open TM

/-- `L (01)^k 1 (01)^m 1 F> 0^inf` (left tape read from the head outwards). -/
def Fd (k m : Nat) (L : Tape) : Config :=
  ⟨cons true (rep m [true, false] (cons true (rep k [true, false] L))), blank, .F⟩

theorem rot (m : Nat) (Y : Tape) :
    cons true (rep m [false, true] Y) = rep m [true, false] (cons true Y) :=
  rep_rotate m [true] [false, true] [true, false] rfl Y

theorem feed' (k m : Nat) (L : Tape) :
    steps (6 * m + 24) (Fd (k + 1) m L) = some (Fd k (m + 3) L) := by
  have h := feed k m L
  rw [rot] at h
  have e : ∀ Y, cons true (cons false (rep m [true, false] Y)) = rep m [true, false] (cons true (cons false Y)) :=
    fun Y => by
      have := rep_app_comm m [true, false] Y
      simp only [rep_succ, app_cons, app_nil] at this
      exact this.symm
  rw [e] at h
  unfold Fd
  rw [rep_add m 3]
  exact h

/-- The steps of j visits from `Fd (k+j) m`. -/
def feeds_steps (m : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => (6 * m + 24) + feeds_steps (m + 3) j

theorem feeds (j k m : Nat) (L : Tape) :
    steps (feeds_steps m j) (Fd (k + j) m L) = some (Fd k (m + 3 * j) L) := by
  induction j generalizing m with
  | zero => rfl
  | succ j ih =>
    have h1 := feed' (k + j) m L
    have h2 := ih (m + 3)
    rw [show m + 3 * (j + 1) = m + 3 + 3 * j by omega, show k + (j + 1) = k + j + 1 by omega]
    exact steps_seq trans h1 h2

end H124060
