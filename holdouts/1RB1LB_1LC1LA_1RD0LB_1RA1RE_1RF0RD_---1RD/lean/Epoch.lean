import Rules

/-!
# 1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD: an epoch, by induction on its rounds

`c0 j Y R` is the tape `0^inf 1 B> 1 01 (1^10)^j 0101 1^5 (01)^Y R`: a block of 10j ones, the marker `0101`, then the
counter of Y a's (`01`) and the digits R.  One round (`round_a`, `round_b` of `Rules.lean`) turns two a's of the
counter into ten more ones of the block.  `epoch` chains k rounds; `epoch_end` is where the counter runs out.
-/

namespace H89641

open TM

/-- `0^inf 1 B> 1 01 (1^10)^j 0101 1^5 (01)^Y R` -/
def c0 (j Y : Nat) (R : Tape) : Config :=
  ⟨cons true blank, cons true (cons false (cons true (rep j [true, true, true, true, true, true, true, true, true, true]
    (cons false (cons true (cons false (cons true (rep 5 [true] (rep Y [false, true] R))))))))), .B⟩

/-- `0^inf 1 B> 1 01 (1^10)^j 1^5 01 1^5 (01)^Y R` (half way through a round) -/
def c1 (j Y : Nat) (R : Tape) : Config :=
  ⟨cons true blank, cons true (cons false (cons true (rep j [true, true, true, true, true, true, true, true, true, true]
    (rep 5 [true] (cons false (cons true (rep 5 [true] (rep Y [false, true] R)))))))), .B⟩

/-- A one in front of a block of ones moves behind it. -/
theorem ones_rot (j : Nat) (s : Tape) :
    cons true (rep j [true, true, true, true, true, true, true, true, true, true] s)
      = rep j [true, true, true, true, true, true, true, true, true, true] (cons true s) := by
  have h := rep_rotate j [true] [true, true, true, true, true, true, true, true, true, true]
    [true, true, true, true, true, true, true, true, true, true] rfl s
  simpa [app] using h

theorem rep5 (s : Tape) : rep 5 [true] s = cons true (cons true (cons true (cons true (cons true s)))) := rfl

theorem round_a' (j Y : Nat) (R : Tape) : steps (30 * j + 19) (c0 j Y R) = some (c1 j Y R) := by
  have h := round_a Y j R
  simp only [c0, c1, rep5, ones_rot] at h ⊢
  exact h

theorem round_b' (j Y : Nat) (R : Tape) : steps (30 * j + 51) (c1 j (Y + 2) R) = some (c0 (j + 1) Y R) := by
  have h := round_b Y j R
  rw [c0, ← rep_app_comm]
  simp only [c1, rep5, ones_rot, app_cons, app_nil] at h ⊢
  exact h

/-- k rounds: the counter loses 2k a's and the block gains 10k ones. -/
theorem epoch (k : Nat) : ∀ j Y R, ∃ n, steps n (c0 j (Y + 2 * k) R) = some (c0 (j + k) Y R) := by
  induction k with
  | zero => intro j Y R; exact ⟨0, rfl⟩
  | succ k ih =>
    intro j Y R
    obtain ⟨n, hn⟩ := ih (j + 1) Y R
    have e1 : Y + 2 * (k + 1) = (Y + 2 * k) + 2 := by omega
    have e2 : j + 1 + k = j + (k + 1) := by omega
    rw [e2] at hn
    rw [e1]
    exact ⟨_, steps_seq trans (round_a' j _ R) (steps_seq trans (round_b' j _ R) hn)⟩

end H89641
