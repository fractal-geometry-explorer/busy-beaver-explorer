import Phase
import Counter

/-!
# Whole phases of 1RB0RE_0LC1LE_0RD1LD_1RA1LF_1LC0RA_0LB--- for any word on the left: the counters

The rules of Counter.lean chained with `to_end` (Phase.lean), for every tape L left of the counter and every a, b, j:

* `phase_keep`  (Z = 4j + 9):  a word ending in `0 1` stays, Z' = 6j + 15 = 3(Z + 1)/2;
* `phase_tick1` (Z = 4j + 11): C1 L (a+1) b → C1 L a (b+1), Z' = 6j + 15 = 3(Z − 1)/2;
* `phase_tick3` (Z = 4j + 11): C3 L (a+5) b → C3 L (a+1) (b+2), Z' = 6j + 15;

with C1 L a b = `L 1 0^a 1 0 1 (001)^b` and C3 L a b = `L 1 0^a 1 0 0 0 1 (001)^b`.  So between the ends of its
cycles the run is these three rules, whatever the word holds further left (D(a, b) of Phase.lean is C1 with L
blank).  Each phase is at least Z' steps long.  Written by hand.
-/

namespace H53125

open TM

/-- `L 1 0^a 1 0 1 (001)^b`, nearest cell first. -/
def C1 (L : Tape) (a b : Nat) : Tape :=
  rep b [true, false, false] (cons true (cons false (cons true (rep a [false] (cons true L)))))

/-- `L 1 0^a 1 0 0 0 1 (001)^b`, nearest cell first. -/
def C3 (L : Tape) (a b : Nat) : Tape :=
  rep b [true, false, false] (cons true (cons false (cons false (cons false (cons true (rep a [false] (cons true L)))))))

theorem C1_blank (a b : Nat) : C1 blank a b = Dw a b := rfl

/-- Z ≡ 1 mod 4: a word ending in `0 1` stays. -/
theorem phase_keep (L : Tape) (j : Nat) : ∃ s, 6 * j + 15 ≤ s ∧
    steps s (PS (cons true (cons false L)) (4 * j + 9)) = some (PS (cons true (cons false L)) (6 * j + 15)) := by
  obtain ⟨s, hs⟩ := to_end (rep 1 [false] (cons true (cons false L))) j
  rw [show 4 * j + 9 = 4 * j + 8 + 1 by omega, show PS (cons true (cons false L)) (4 * j + 8 + 1) =
    PS (rep 1 [false] (cons true (cons false L))) (4 * j + 8) by unfold PS; rw [rep_add]]
  have e : 3 * (2 * j + 1) + 12 = 6 * j + 15 := by omega
  have h := keep (2 * j + 1) L; rw [z12] at h
  exact ⟨_, by omega, fin (steps_seq trans hs h) e rfl⟩

theorem C1_ends (L : Tape) (a b : Nat) : ∃ X, C1 L a b = cons true (cons false X) := by
  cases b with
  | zero => exact ⟨_, rfl⟩
  | succ b => exact ⟨_, rfl⟩

theorem C3_ends (L : Tape) (a b : Nat) : ∃ X, C3 L a b = cons true (cons false X) := by
  cases b with
  | zero => exact ⟨_, rfl⟩
  | succ b => exact ⟨_, rfl⟩

/-- Z ≡ 3 mod 4: the counter of level 1 moves one unit. -/
theorem phase_tick1 (L : Tape) (a b j : Nat) : ∃ s, 6 * j + 15 ≤ s ∧
    steps s (PS (C1 L (a + 1) b) (4 * j + 11)) = some (PS (C1 L a (b + 1)) (6 * j + 15)) := by
  obtain ⟨s, hs⟩ := to_end (rep 3 [false] (C1 L (a + 1) b)) j
  rw [show 4 * j + 11 = 4 * j + 8 + 3 by omega, show PS (C1 L (a + 1) b) (4 * j + 8 + 3) =
    PS (rep 3 [false] (C1 L (a + 1) b)) (4 * j + 8) by unfold PS; rw [rep_add]]
  have e : 3 * (2 * j + 1) + 12 = 6 * j + 15 := by omega
  have h := tick1 a b (2 * j + 1) L; rw [z12] at h
  refine ⟨_, by omega, fin (steps_seq trans hs h) e ?_⟩
  unfold C1
  show _ = app [true, false] (app [false] (rep b [true, false, false] _))
  rw [rep_rotate b [false] [true, false, false] [false, true, false] rfl]
  rfl

/-- Z ≡ 3 mod 4: the counter that moves by four. -/
theorem phase_tick3 (L : Tape) (a b j : Nat) : ∃ s, 6 * j + 15 ≤ s ∧
    steps s (PS (C3 L (a + 5) b) (4 * j + 11)) = some (PS (C3 L (a + 1) (b + 2)) (6 * j + 15)) := by
  obtain ⟨s, hs⟩ := to_end (rep 3 [false] (C3 L (a + 5) b)) j
  rw [show 4 * j + 11 = 4 * j + 8 + 3 by omega, show PS (C3 L (a + 5) b) (4 * j + 8 + 3) =
    PS (rep 3 [false] (C3 L (a + 5) b)) (4 * j + 8) by unfold PS; rw [rep_add]]
  have e : 3 * (2 * j + 1) + 12 = 6 * j + 15 := by omega
  have h := tick3 a b (2 * j + 1) L; rw [z12] at h
  refine ⟨_, by omega, fin (steps_seq trans hs h) e ?_⟩
  unfold C3
  show _ = app [true, false, false] (rep (b + 1) [true, false, false] _)
  rw [← rep_app_comm b]
  show _ = app [true, false] (app [false] (rep b [true, false, false] _))
  rw [rep_rotate b [false] [true, false, false] [false, true, false] rfl]
  rfl

/-- `L 1 0^a 1`, nearest cell first (R(a) of Phase.lean is `R blank a`). -/
def Rl (L : Tape) (a : Nat) : Tape := cons true (rep a [false] (cons true L))

theorem Rl_blank (a : Nat) : Rl blank a = Rw a := rfl

theorem z9 (n : Nat) (X : Tape) :
    cons false (cons false (cons false (rep n [false, false, false] (cons false (cons false (cons false (cons false (cons false (cons false (X)))))))))) = rep (3 * n + 9) [false] X := by
  have h := zeros 3 n 6 X
  rw [show 3 + 3 * n + 6 = 3 * n + 9 by omega] at h
  exact h

/-- Z ≡ 2 mod 4: `1 0^(a+1) 1` becomes the level-1 counter with b = 0, any L. -/
theorem phase_rtwo (L : Tape) (a j : Nat) : ∃ s, 6 * j + 15 ≤ s ∧
    steps s (PS (Rl L (a + 1)) (4 * j + 10)) = some (PS (C1 L a 0) (6 * j + 15)) := by
  obtain ⟨s, hs⟩ := to_end (rep 2 [false] (Rl L (a + 1))) j
  rw [show 4 * j + 10 = 4 * j + 8 + 2 by omega, show PS (Rl L (a + 1)) (4 * j + 8 + 2) =
    PS (rep 2 [false] (Rl L (a + 1))) (4 * j + 8) by unfold PS; rw [rep_add]]
  have e : 3 * (2 * j + 1) + 12 = 6 * j + 15 := by omega
  have h := rtwo a (2 * j + 1) L; rw [z12] at h
  exact ⟨_, by omega, fin (steps_seq trans hs h) e rfl⟩

/-- Z ≡ 0 mod 4: `1 0^(a+8) 1` becomes the counter that moves by four, with b = 1, Z' = 3Z/2 − 3, any L. -/
theorem phase_rzero (L : Tape) (a j : Nat) : ∃ s, 6 * j + 9 ≤ s ∧
    steps s (PS (Rl L (a + 8)) (4 * j + 8)) = some (PS (C3 L (a + 4) 1) (6 * j + 9)) := by
  obtain ⟨s, hs⟩ := to_end (rep 0 [false] (Rl L (a + 8))) j
  have e : 3 * (2 * j) + 9 = 6 * j + 9 := by omega
  have h := rzero a (2 * j) L; rw [z9] at h
  exact ⟨_, by omega, fin (steps_seq trans hs h) e rfl⟩

end H53125
