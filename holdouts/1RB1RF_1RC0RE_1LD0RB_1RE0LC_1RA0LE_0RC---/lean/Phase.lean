import Machine
import Rules

/-!
# 1RB1RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_0RC---: the feeding rules, restated and iterated

`Fd c k m L` is the configuration `L (01)^k c (01)^m 0 B> 0^inf`: the head in state B just right of the tape, a
block of m copies of 01 at the end, and before it, past a cursor cell c, a block of k copies.  One visit of the right
end (`feed0`, `feed1` of `Rules.lean`) moves one copy out of the k-block, adds two to the end block and flips the
cursor (`feed0'`, `feed1'`); two visits (`feed2`) take `Fd false (k+2) m` to `Fd false k (m+4)` in 8m+36 steps, and
`feeds` iterates that: a block of 2j copies is turned into 4j copies at the end.
-/

namespace H75404

open TM

/-- `L (01)^k c (01)^m 0 B> 0^inf` (left tape read from the head outwards). -/
def Fd (c : Bool) (k m : Nat) (L : Tape) : Config :=
  ⟨cons false (rep m [true, false] (cons c (rep k [true, false] L))), blank, .B⟩

theorem rot (m : Nat) (Y : Tape) :
    cons true (rep m [false, true] Y) = rep m [true, false] (cons true Y) :=
  rep_rotate m [true] [false, true] [true, false] rfl Y

theorem feed0' (k m : Nat) (L : Tape) :
    steps (4 * m + 18) (Fd false (k + 1) m L) = some (Fd true k (m + 2) L) := by
  have h := feed0 k m L
  rw [rot] at h
  unfold Fd
  rw [rep_add m 2]
  exact h

theorem feed1' (k m : Nat) (L : Tape) :
    steps (4 * m + 10) (Fd true (k + 1) m L) = some (Fd false k (m + 2) L) := by
  have h := feed1 k m L
  rw [rot] at h
  unfold Fd
  rw [rep_add m 2]
  exact h

theorem feed2 (k m : Nat) (L : Tape) :
    steps (8 * m + 36) (Fd false (k + 2) m L) = some (Fd false k (m + 4) L) := by
  have h1 := feed0' (k + 1) m L
  have h2 := feed1' k (m + 2) L
  have e : 8 * m + 36 = (4 * m + 18) + (4 * (m + 2) + 10) := by omega
  rw [e]
  exact steps_seq trans h1 h2

/-- The steps of j double visits from end block m. -/
def feeds_steps (m : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => (8 * m + 36) + feeds_steps (m + 4) j

theorem feeds (j k m : Nat) (L : Tape) :
    steps (feeds_steps m j) (Fd false (k + 2 * j) m L) = some (Fd false k (m + 4 * j) L) := by
  induction j generalizing m with
  | zero => rfl
  | succ j ih =>
    have h1 := feed2 (k + 2 * j) m L
    have h2 := ih (m + 4)
    rw [show m + 4 * (j + 1) = m + 4 + 4 * j by omega, show k + 2 * (j + 1) = k + 2 * j + 2 by omega]
    exact steps_seq trans h1 h2

end H75404
