import Rules

/-!
# The first regime as a theorem for all sizes

`Q a R` is the tape at the left end in state A: `A>(01110)^a 0 1 1 1 1 (001)^a R`, blank tape to the left. One round
trip (`trip1`, generated in `Rules.lean`) eats the first block `01111` of `R` (it needs a second one behind it) and
adds a block to each of the two repeats: `Q (a+1) (01111 01111 R) → Q (a+2) (01111 R)` in 28a + 55 steps. Iterated
over a reservoir `(01111)^(k+1+j)` it runs j trips.
-/

namespace H91503

open TM

def w5 : List Bool := [false, true, true, true, false]
def w3 : List Bool := [false, false, true]
/-- The reservoir block. -/
def wB : List Bool := [false, true, true, true, true]

/-- The first-regime configuration. -/
def Q (a : Nat) (R : Tape) : Config := ⟨blank, rep a w5 (app wB (rep a w3 R)), .A⟩

theorem rotL (n : Nat) (s : Tape) :
    cons false (cons true (rep n [true, true, false, false, true] s)) =
      rep n [false, true, true, true, false] (cons false (cons true s)) :=
  rep_rotate n [false, true] [true, true, false, false, true] w5 rfl s

theorem rotR (n : Nat) (s : Tape) :
    cons false (cons false (rep n [true, false, false] s)) = rep n [false, false, true] (cons false (cons false s)) :=
  rep_rotate n [false, false] [true, false, false] w3 rfl s

theorem absorb3 (n : Nat) (s : Tape) :
    rep n [false, false, true] (cons false (cons false (cons true s))) = rep (n + 1) [false, false, true] s :=
  rep_app_comm n w3 s

/-- One round trip, for all a and every tape R beyond the second reservoir block (kernel). -/
theorem Q_step (a : Nat) (R : Tape) :
    steps (28 * a + 55) (Q (a + 1) (app wB (app wB R))) = some (Q (a + 2) (app wB R)) := by
  have h := trip1 a R
  rw [rotL (a + 1), rotR (a + 1), absorb3 (a + 1)] at h
  exact h

/-- j round trips over a reservoir of k + 1 + j blocks (kernel). -/
theorem Q_iter (j : Nat) : ∀ (a k : Nat) (S : Tape),
    ∃ t, steps t (Q (a + 1) (rep (k + 1 + j) wB S)) = some (Q (a + 1 + j) (rep (k + 1) wB S)) := by
  induction j with
  | zero => intro a k S; exact ⟨0, rfl⟩
  | succ j ih =>
    intro a k S
    obtain ⟨t, ht⟩ := ih (a + 1) k S
    refine ⟨28 * a + 55 + t, ?_⟩
    have e1 : k + 1 + (j + 1) = (k + j) + 2 := by omega
    have e2 : a + 1 + (j + 1) = a + 1 + 1 + j := by omega
    rw [e1, e2]
    have h1 := Q_step a (rep (k + j) wB S)
    have e3 : k + 1 + j = (k + j) + 1 := by omega
    rw [e3] at ht
    exact steps_seq trans h1 ht

/-! ## The regime with a machine at the right end

`Z a c d = A>(01110)^a 0 1 1 1 1 (001)^c 1 1 0 0 1 0 0 1 1 1 1 (001)^d 1 1 0 0 1`, blank on both sides: the left part
grows as before, the reservoir `(001)^c` stays, and a small machine at the right end eats the blocks `(001)^d`. Its
shape returns every 14 round trips, 4 blocks fewer (`cycle3`). -/

def Z (a c d : Nat) : Config :=
  ⟨blank, rep a w5 (app wB (rep c w3 (app [true, true, false, false, true, false, false, true, true, true, true]
    (rep d w3 (app [true, true, false, false, true] blank))))), .A⟩

theorem rotA (n : Nat) (s : Tape) :
    cons false (rep n [true, true, true, false, false] s) = rep n [false, true, true, true, false] (cons false s) :=
  rep_rotate n [false] [true, true, true, false, false] w5 rfl s

theorem absorb001 (n : Nat) (s : Tape) :
    rep n [false, false, true] (cons false (cons false (cons true s))) = rep (n + 1) [false, false, true] s :=
  rep_app_comm n w3 s

theorem blank3 : cons false (cons false (cons false blank)) = blank := by
  rw [cons_false_blank, cons_false_blank, cons_false_blank]

/-- Fourteen round trips of the right-end eater regime (kernel). -/
theorem Z_step (a c d : Nat) : ∃ t, steps t (Z (a + 1) (c + 1) (d + 9)) = some (Z (a + 15) (c + 1) (d + 5)) := by
  have h := cycle3 a c d
  rw [rotA (a + 1), rotR c, absorb001 c, rotR (d + 3), absorb001 (d + 3), absorb001 (d + 4), blank3] at h
  exact ⟨_, h⟩

/-- j periods of the right-end eater regime (kernel). -/
theorem Z_iter (j : Nat) : ∀ (a c d : Nat),
    ∃ t, steps t (Z (a + 1) (c + 1) (d + 5 + 4 * j)) = some (Z (a + 1 + 14 * j) (c + 1) (d + 5)) := by
  induction j with
  | zero => intro a c d; exact ⟨0, rfl⟩
  | succ j ih =>
    intro a c d
    obtain ⟨t, ht⟩ := ih (a + 14) c d
    obtain ⟨t1, h1⟩ := Z_step a c (d + 4 * j)
    refine ⟨t1 + t, ?_⟩
    have e1 : d + 5 + 4 * (j + 1) = d + 4 * j + 9 := by omega
    have e2 : a + 1 + 14 * (j + 1) = a + 14 + 1 + 14 * j := by omega
    have e3 : d + 4 * j + 5 = d + 5 + 4 * j := by omega
    have e4 : a + 15 = a + 14 + 1 := by omega
    rw [e1, e2]
    rw [e3, e4] at h1
    exact steps_seq trans h1 ht

end H91503
