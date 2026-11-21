import Phase
import TailRules

/-!
# The end of a phase for whole families of tails

`PS M T` is a phase start `0^inf F> 0 1^M T` and `DW k X` the tape after the rounds, `0^inf D> 0 1 (10)^k X`, where
X begins with the 0, 1 or 2 ones left over.  `ps_rounds` takes a phase start with any tail to the wall; then the
rules of `TailRules.lean` end the phase, written here with every block of ones as one `rep`:

* `d_pop`: no ones left, the first block of the tail joins the ones (any tail);
* `d_merge`: one one left is a tape identity, the wall takes it with the separator and the rounds go on with the
  next block (any tail);
* `d_push2`, `d_zero2`, `d_ones2`: two ones left and a tail `(0 1)^j` followed by a block of at least three ones, by
  an empty block, or by the end of the tape.

What is left open is two ones left over with a block `0 1 1` before the first block of other length.
-/

namespace H103424

open TM

/-- A phase start `0^inf F> 0 1^M T`. -/
abbrev PS (M : Nat) (T : Tape) : Config := ⟨blank, cons false (rep M [true] T), .F⟩
/-- After the rounds: `0^inf D> 0 1 (10)^k X`. -/
abbrev DW (k : Nat) (X : Tape) : Config := ⟨blank, cons false (cons true (rep k [true, false] X)), .D⟩
/-- `b` is reached from `a`. -/
def Reach (a b : Config) : Prop := ∃ s, steps s a = some b

theorem pairs_rep (k n : Nat) (X : Tape) : rep k [true, true] (rep n [true] X) = rep (2 * k + n) [true] X := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [rep_succ, ih, show 2 * (k + 1) + n = (2 * k + n) + 1 + 1 by omega]
    rfl

theorem ones_rep (a b : Nat) (X : Tape) : rep a [true] (rep b [true] X) = rep (a + b) [true] X := by
  rw [← rep_add]

theorem reach_ps {c : Config} {a b : Nat} {T : Tape} (h : a = b) (hc : Reach c (PS a T)) : Reach c (PS b T) :=
  h ▸ hc

/-- Any phase start with at least five ones reaches the wall: M = 3q + 5 + m, k = 5 + 4q. -/
theorem ps_rounds (q m : Nat) (T : Tape) : Reach (PS (3 * q + 5 + m) T) (DW (5 + 4 * q) (rep m [true] T)) := by
  have h1 := start (3 * q + m) T
  obtain ⟨s2, h2⟩ := rounds q 5 m T
  rw [show 3 * q + 5 + m = 3 * q + m + 5 by omega]
  exact ⟨_, steps_seq trans h1 h2⟩

/-- No ones left: the first block `0 1^u` of any tail joins the 2k + 7 ones. -/
theorem d_pop (k u : Nat) (R : Tape) : Reach (DW k (cons false (rep u [true] R))) (PS (2 * k + 7 + u) R) := by
  have h := pop k u R
  simp only [ones_cons, pairs_rep] at h
  exact reach_ps (by omega) ⟨_, h⟩

/-- One one left: `(10)^k 1 0 = (10)^(k+1)`, so the wall goes on with the next block of the tail. -/
theorem d_merge (k : Nat) (R : Tape) : DW k (cons true (cons false R)) = DW (k + 1) R := by
  show (⟨blank, cons false (cons true (rep k [true, false] (app [true, false] R))), .D⟩ : Config) = _
  rw [rep_app_comm]

/-- Two ones left, j blocks `0 1` and a block of t + 3 ones: 2k + 7 ones, two more blocks `0 1`, three ones less. -/
theorem d_push2 (k j t : Nat) (R : Tape) :
    Reach (DW k (cons true (cons true (rep j [false, true] (cons false (rep (t + 3) [true] R))))))
      (PS (2 * k + 7) (rep (j + 2) [false, true] (cons false (rep t [true] R)))) := by
  have h := push2 j k t R
  have e : cons false (cons true (cons false (rep j [true, false] (cons true (cons false (rep t [true] R)))))) =
      rep (j + 2) [false, true] (cons false (rep t [true] R)) := by
    have r := rep_rotate j [false] [true, false] [false, true] rfl (cons true (cons false (rep t [true] R)))
    simp only [app_cons, app_nil] at r
    rw [r]
    show _ = app [false, true] (rep (j + 1) [false, true] _)
    rw [← rep_app_comm]
    rfl
  rw [e] at h
  simp only [ones_cons, pairs_ones, ones_snoc] at h
  exact reach_ps (by omega) ⟨_, h⟩

/-- Two ones left, j blocks `0 1` and an empty block: 2k + 3 ones, and the j blocks become a block of 2j + 6. -/
theorem d_zero2 (k j : Nat) (R : Tape) :
    Reach (DW k (cons true (cons true (rep j [false, true] (cons false (cons false R))))))
      (PS (2 * k + 3) (cons false (rep (2 * j + 6) [true] R))) := by
  have h := zero2 j k R
  have e : rep j [true, true] (cons true (cons true R)) = rep (2 * j + 2) [true] R := by
    rw [show cons true (cons true R) = rep 2 [true] R from rfl, pairs_rep]
  rw [e] at h
  simp only [ones_cons, pairs_ones] at h
  exact reach_ps (by omega) ⟨_, h⟩

/-- Two ones left and a tail of j + 1 blocks `0 1`: 2k + 3 ones and one block of 2j + 8. -/
theorem d_ones2 (k j : Nat) :
    Reach (DW k (cons true (cons true (rep (j + 1) [false, true] blank))))
      (PS (2 * k + 3) (cons false (rep (2 * j + 8) [true] blank))) := by
  have h := ones2 j k
  have e : rep j [true, true] (cons true (cons true (cons true blank))) = rep (2 * j + 3) [true] blank := by
    rw [show cons true (cons true (cons true blank)) = rep 3 [true] blank from rfl, pairs_rep]
  rw [e] at h
  simp only [ones_cons, pairs_ones] at h
  exact reach_ps (by omega) ⟨_, h⟩

end H103424
