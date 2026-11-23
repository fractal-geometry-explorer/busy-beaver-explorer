import CounterPhase
import Specials

/-!
# The cycle-end phases of 1RB0RE_0LC1LE_0RD1LD_1RA1LF_1LC0RA_0LB--- met in the first 1,000,000 phases

The rules of Specials.lean chained with `to_end` into whole phases (Z = 4j + 11), for every b and j.  Words are
written with the shapes of CounterPhase.lean and S2t L a b = `L 1 0^a 1 (001)^b`; the tape L left of the counter is
blank or one of five short words.  Written by hand (the proofs follow one pattern).
-/

namespace H53125

open TM

/-- `L 1 0^a 1 (001)^b`, nearest cell first; `S2t L a 0` is `Rl L a`. -/
def S2t (L : Tape) (a b : Nat) : Tape := rep b [true, false, false] (cons true (rep a [false] (cons true L)))

theorem S2t_zero (L : Tape) (a : Nat) : S2t L a 0 = Rl L a := rfl

theorem phase_sp2 (b j : Nat) : ∃ s, 6 * j + 15 ≤ s ∧
    steps s (PS (C3 blank 3 b) (4 * j + 11)) = some (PS (S2t blank 6 (b + 2)) (6 * j + 15)) := by
  obtain ⟨s, hs⟩ := to_end (rep 3 [false] (C3 blank 3 b)) j
  rw [show 4 * j + 11 = 4 * j + 8 + 3 by omega, show PS (C3 blank 3 b) (4 * j + 8 + 3) =
    PS (rep 3 [false] (C3 blank 3 b)) (4 * j + 8) by unfold PS; rw [rep_add]]
  have e : 3 * (2 * j + 1) + 12 = 6 * j + 15 := by omega
  have h := sp2 b (2 * j + 1); rw [z12] at h; try rw [cons_false_blank] at h
  refine ⟨_, by omega, fin (steps_seq trans hs h) e ?_⟩
  unfold S2t
  show _ = app [true, false, false] (rep (b + 1) [true, false, false] _)
  rw [← rep_app_comm b]
  show _ = app [true, false] (app [false] (rep b [true, false, false] _))
  rw [rep_rotate b [false] [true, false, false] [false, true, false] rfl]
  rfl

theorem phase_sp3 (b j : Nat) : ∃ s, 6 * j + 18 ≤ s ∧
    steps s (PS (S2t blank 6 (b + 1)) (4 * j + 11)) = some (PS (S2t (app [false, false, false, true] blank) (3 * b + 6) 0) (6 * j + 18)) := by
  obtain ⟨s, hs⟩ := to_end (rep 3 [false] (S2t blank 6 (b + 1))) j
  rw [show 4 * j + 11 = 4 * j + 8 + 3 by omega, show PS (S2t blank 6 (b + 1)) (4 * j + 8 + 3) =
    PS (rep 3 [false] (S2t blank 6 (b + 1))) (4 * j + 8) by unfold PS; rw [rep_add]]
  have e : 3 * (2 * j + 1) + 15 = 6 * j + 18 := by omega
  have h := sp3 b (2 * j + 1); rw [z15] at h; try rw [cons_false_blank] at h
  refine ⟨_, by omega, fin (steps_seq trans hs h) e ?_⟩
  unfold S2t
  rw [show 3 * b + 6 = 3 + 3 * b + 3 by omega, ← zeros]
  rfl

theorem phase_sp4 (b j : Nat) : ∃ s, 6 * j + 18 ≤ s ∧
    steps s (PS (C3 (app [false, false, false, true] blank) 2 (b + 1)) (4 * j + 11)) = some (PS (S2t (app [false, true, false, false, true] blank) (3 * b + 9) 0) (6 * j + 18)) := by
  obtain ⟨s, hs⟩ := to_end (rep 3 [false] (C3 (app [false, false, false, true] blank) 2 (b + 1))) j
  rw [show 4 * j + 11 = 4 * j + 8 + 3 by omega, show PS (C3 (app [false, false, false, true] blank) 2 (b + 1)) (4 * j + 8 + 3) =
    PS (rep 3 [false] (C3 (app [false, false, false, true] blank) 2 (b + 1))) (4 * j + 8) by unfold PS; rw [rep_add]]
  have e : 3 * (2 * j + 1) + 15 = 6 * j + 18 := by omega
  have h := sp4 b (2 * j + 1); rw [z15] at h; try rw [cons_false_blank] at h
  refine ⟨_, by omega, fin (steps_seq trans hs h) e ?_⟩
  unfold S2t
  rw [show 3 * b + 9 = 3 + 3 * b + 6 by omega, ← zeros]
  rfl

theorem phase_sp5 (b j : Nat) : ∃ s, 6 * j + 18 ≤ s ∧
    steps s (PS (C1 (app [false, true, false, false, true] blank) 0 (b + 1)) (4 * j + 11)) = some (PS (S2t blank (3 * b + 14) 0) (6 * j + 18)) := by
  obtain ⟨s, hs⟩ := to_end (rep 3 [false] (C1 (app [false, true, false, false, true] blank) 0 (b + 1))) j
  rw [show 4 * j + 11 = 4 * j + 8 + 3 by omega, show PS (C1 (app [false, true, false, false, true] blank) 0 (b + 1)) (4 * j + 8 + 3) =
    PS (rep 3 [false] (C1 (app [false, true, false, false, true] blank) 0 (b + 1))) (4 * j + 8) by unfold PS; rw [rep_add]]
  have e : 3 * (2 * j + 1) + 15 = 6 * j + 18 := by omega
  have h := sp5 b (2 * j + 1); rw [z15] at h; try rw [cons_false_blank] at h
  refine ⟨_, by omega, fin (steps_seq trans hs h) e ?_⟩
  unfold S2t
  rw [show 3 * b + 14 = 3 + 3 * b + 11 by omega, ← zeros]
  rfl

theorem phase_sp6 (b j : Nat) : ∃ s, 6 * j + 18 ≤ s ∧
    steps s (PS (C3 blank 1 (b + 1)) (4 * j + 11)) = some (PS (S2t blank (3 * b + 9) 0) (6 * j + 18)) := by
  obtain ⟨s, hs⟩ := to_end (rep 3 [false] (C3 blank 1 (b + 1))) j
  rw [show 4 * j + 11 = 4 * j + 8 + 3 by omega, show PS (C3 blank 1 (b + 1)) (4 * j + 8 + 3) =
    PS (rep 3 [false] (C3 blank 1 (b + 1))) (4 * j + 8) by unfold PS; rw [rep_add]]
  have e : 3 * (2 * j + 1) + 15 = 6 * j + 18 := by omega
  have h := sp6 b (2 * j + 1); rw [z15] at h; try rw [cons_false_blank] at h
  refine ⟨_, by omega, fin (steps_seq trans hs h) e ?_⟩
  unfold S2t
  rw [show 3 * b + 9 = 3 + 3 * b + 6 by omega, ← zeros]
  rfl

theorem phase_sp7 (b j : Nat) : ∃ s, 6 * j + 18 ≤ s ∧
    steps s (PS (C3 (app [false, false, false, true] blank) 4 (b + 1)) (4 * j + 11)) = some (PS (S2t (app [false, false, true, false, false, false, false, false, false, true] blank) (3 * b + 9) 0) (6 * j + 18)) := by
  obtain ⟨s, hs⟩ := to_end (rep 3 [false] (C3 (app [false, false, false, true] blank) 4 (b + 1))) j
  rw [show 4 * j + 11 = 4 * j + 8 + 3 by omega, show PS (C3 (app [false, false, false, true] blank) 4 (b + 1)) (4 * j + 8 + 3) =
    PS (rep 3 [false] (C3 (app [false, false, false, true] blank) 4 (b + 1))) (4 * j + 8) by unfold PS; rw [rep_add]]
  have e : 3 * (2 * j + 1) + 15 = 6 * j + 18 := by omega
  have h := sp7 b (2 * j + 1); rw [z15] at h; try rw [cons_false_blank] at h
  refine ⟨_, by omega, fin (steps_seq trans hs h) e ?_⟩
  unfold S2t
  rw [show 3 * b + 9 = 3 + 3 * b + 6 by omega, ← zeros]
  rfl

theorem phase_sp8 (b j : Nat) : ∃ s, 6 * j + 15 ≤ s ∧
    steps s (PS (C1 (app [false, false, true, false, false, false, false, false, false, true] blank) 0 b) (4 * j + 11)) = some (PS (S2t (app [false, false, false, true, false, false, true] blank) 4 (b + 1)) (6 * j + 15)) := by
  obtain ⟨s, hs⟩ := to_end (rep 3 [false] (C1 (app [false, false, true, false, false, false, false, false, false, true] blank) 0 b)) j
  rw [show 4 * j + 11 = 4 * j + 8 + 3 by omega, show PS (C1 (app [false, false, true, false, false, false, false, false, false, true] blank) 0 b) (4 * j + 8 + 3) =
    PS (rep 3 [false] (C1 (app [false, false, true, false, false, false, false, false, false, true] blank) 0 b)) (4 * j + 8) by unfold PS; rw [rep_add]]
  have e : 3 * (2 * j + 1) + 12 = 6 * j + 15 := by omega
  have h := sp8 b (2 * j + 1); rw [z12] at h; try rw [cons_false_blank] at h
  refine ⟨_, by omega, fin (steps_seq trans hs h) e ?_⟩
  unfold S2t
  show _ = app [true, false] (app [false] (rep b [true, false, false] _))
  rw [rep_rotate b [false] [true, false, false] [false, true, false] rfl]
  rfl

theorem phase_sp9 (b j : Nat) : ∃ s, 6 * j + 18 ≤ s ∧
    steps s (PS (S2t (app [false, false, false, true, false, false, true] blank) 4 (b + 1)) (4 * j + 11)) = some (PS (S2t (app [false, true, false, false, false, true, false, false, true] blank) (3 * b + 6) 0) (6 * j + 18)) := by
  obtain ⟨s, hs⟩ := to_end (rep 3 [false] (S2t (app [false, false, false, true, false, false, true] blank) 4 (b + 1))) j
  rw [show 4 * j + 11 = 4 * j + 8 + 3 by omega, show PS (S2t (app [false, false, false, true, false, false, true] blank) 4 (b + 1)) (4 * j + 8 + 3) =
    PS (rep 3 [false] (S2t (app [false, false, false, true, false, false, true] blank) 4 (b + 1))) (4 * j + 8) by unfold PS; rw [rep_add]]
  have e : 3 * (2 * j + 1) + 15 = 6 * j + 18 := by omega
  have h := sp9 b (2 * j + 1); rw [z15] at h; try rw [cons_false_blank] at h
  refine ⟨_, by omega, fin (steps_seq trans hs h) e ?_⟩
  unfold S2t
  rw [show 3 * b + 6 = 3 + 3 * b + 3 by omega, ← zeros]
  rfl

end H53125
