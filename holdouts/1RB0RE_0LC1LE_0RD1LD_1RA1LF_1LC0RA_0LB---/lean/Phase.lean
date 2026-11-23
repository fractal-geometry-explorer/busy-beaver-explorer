import Sweeps
import Ends

/-!
# Whole phases of 1RB0RE_0LC1LE_0RD1LD_1RA1LF_1LC0RA_0LB--- for the words D(a, b) and R(a)

A phase starts at `PS W Z` = `0^inf D 0^Z 1 0 0 E> 0^inf` (W is D read from its right end, the left tape nearest
cell first).  With

    D(a, b) = 0 1 0^a 1 0 1 (001)^b        R(a) = 0 1 0^a 1

(the leading 0 is the blank tape) a phase is `start` (Ends.lean), j sweeps (`sweeps`, Sweeps.lean) and one of the
`end_*` rules (Ends.lean).  Chained here, for every a, b and j:

* Z = 4j + 9  (Z ≡ 1 mod 4):  D(a, b)   → D(a, b),         Z' = 6j + 15 = 3(Z + 1)/2
* Z = 4j + 11 (Z ≡ 3 mod 4):  D(a+1, b) → D(a, b+1),       Z' = 6j + 15 = 3(Z − 1)/2
* Z = 4j + 11 (Z ≡ 3 mod 4):  D(0, b)   → R(3b + 5),       Z' = 6j + 18 = 3(Z + 1)/2
* Z = 4j + 10 (Z ≡ 2 mod 4):  R(a+1)    → D(a, 0),         Z' = 6j + 15 = 3Z/2

Written by hand.
-/

namespace H53125

open TM

/-- D(a, b) as a left tape, nearest cell first. -/
def Dw (a b : Nat) : Tape := rep b [true, false, false] (cons true (cons false (cons true (rep a [false] (cons true blank)))))

/-- R(a) as a left tape, nearest cell first. -/
def Rw (a : Nat) : Tape := cons true (rep a [false] (cons true blank))

/-- The phase start `0^inf W 0^Z 1 0 0 E> 0^inf`. -/
def PS (W : Tape) (Z : Nat) : Config := ⟨cons false (cons false (cons true (rep Z [false] W))), blank, .E⟩

theorem zeros3 (n : Nat) (X : Tape) : rep n [false, false, false] X = rep (3 * n) [false] X := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show app [false, false, false] (rep n [false, false, false] X) = _
    rw [show 3 * (n + 1) = 3 + 3 * n by omega, rep_add, ← ih]; rfl

/-- `k` zeros, `(000)^n`, `m` zeros. -/
theorem zeros (k n m : Nat) (X : Tape) :
    rep k [false] (rep n [false, false, false] (rep m [false] X)) = rep (k + 3 * n + m) [false] X := by
  rw [zeros3, ← rep_add, ← rep_add, Nat.add_assoc]

/-- 3 zeros, `(000)^n`, 9 zeros: the run of zeros at the end of a phase. -/
theorem z12 (n : Nat) (X : Tape) :
    cons false (cons false (cons false (rep n [false, false, false] (cons false (cons false (cons false (cons false (cons false (cons false (cons false (cons false (cons false (X))))))))))))) = rep (3 * n + 12) [false] X := by
  have h := zeros 3 n 9 X
  rw [show 3 + 3 * n + 9 = 3 * n + 12 by omega] at h
  exact h

/-- 6 zeros, `(000)^n`, 9 zeros. -/
theorem z15 (n : Nat) (X : Tape) :
    cons false (cons false (cons false (cons false (cons false (cons false (rep n [false, false, false] (cons false (cons false (cons false (cons false (cons false (cons false (cons false (cons false (cons false (X)))))))))))))))) = rep (3 * n + 15) [false] X := by
  have h := zeros 6 n 9 X
  rw [show 6 + 3 * n + 9 = 3 * n + 15 by omega] at h
  exact h

/-- The start and the sweeps: from `PS W (4j + 8)` to the end of the sweeps, wall `(100)^(2j+1)`, four zeros. -/
theorem to_end (W : Tape) (j : Nat) : ∃ s, steps s (PS W (4 * j + 8)) =
    some ⟨cons false (rep (2 * j + 1) [false, false, true] (cons false (cons false (cons false (cons true
      (rep 4 [false] W)))))), blank, .A⟩ := by
  have h1 := start (rep (4 * j) [false] W)
  obtain ⟨s, hs⟩ := sweeps j 1 W
  rw [show 1 + 2 * j = 2 * j + 1 by omega] at hs
  have e1 : rep (4 * j + 8) [false] W = rep 8 [false] (rep (4 * j) [false] W) := by rw [Nat.add_comm, rep_add]
  have e2 : rep (4 * j + 4) [false] W = rep 4 [false] (rep (4 * j) [false] W) := by rw [Nat.add_comm, rep_add]
  rw [e2] at hs
  unfold PS; rw [e1]
  exact ⟨_, steps_seq trans h1 hs⟩

theorem fin {c : Config} {s Z Z' : Nat} {W W' : Tape}
    (h : steps s c = some ⟨cons false (cons false (cons true (rep Z' [false] W'))), blank, .E⟩)
    (e1 : Z' = Z) (e2 : W' = W) : steps s c = some (PS W Z) := by
  subst e1 e2; exact h

/-- Z ≡ 1 mod 4: the word D(a, b) stays, Z' = 3(Z + 1)/2. -/
theorem phase_D1 (a b j : Nat) : ∃ s, 6 * j + 15 ≤ s ∧ steps s (PS (Dw a b) (4 * j + 9)) = some (PS (Dw a b) (6 * j + 15)) := by
  obtain ⟨s, hs⟩ := to_end (rep 1 [false] (Dw a b)) j
  rw [show 4 * j + 9 = 4 * j + 8 + 1 by omega, show PS (Dw a b) (4 * j + 8 + 1) = PS (rep 1 [false] (Dw a b))
    (4 * j + 8) by unfold PS; rw [rep_add]] 
  have e : 3 * (2 * j + 1) + 12 = 6 * j + 15 := by omega
  rcases a with _ | a <;> rcases b with _ | b
  · have h := end1_00 (2 * j + 1); rw [z12] at h
    exact ⟨_, by omega, fin (steps_seq trans hs h) e rfl⟩
  · have h := end1_0s b (2 * j + 1); rw [z12] at h
    exact ⟨_, by omega, fin (steps_seq trans hs h) e rfl⟩
  · have h := end1_s0 a (2 * j + 1); rw [z12] at h
    exact ⟨_, by omega, fin (steps_seq trans hs h) e rfl⟩
  · have h := end1_ss a b (2 * j + 1); rw [z12] at h
    exact ⟨_, by omega, fin (steps_seq trans hs h) e rfl⟩

/-- Z ≡ 3 mod 4, a ≥ 1: D(a+1, b) becomes D(a, b+1), Z' = 3(Z − 1)/2. -/
theorem phase_D3 (a b j : Nat) :
    ∃ s, 6 * j + 15 ≤ s ∧ steps s (PS (Dw (a + 1) b) (4 * j + 11)) = some (PS (Dw a (b + 1)) (6 * j + 15)) := by
  obtain ⟨s, hs⟩ := to_end (rep 3 [false] (Dw (a + 1) b)) j
  rw [show 4 * j + 11 = 4 * j + 8 + 3 by omega, show PS (Dw (a + 1) b) (4 * j + 8 + 3) =
    PS (rep 3 [false] (Dw (a + 1) b)) (4 * j + 8) by unfold PS; rw [rep_add]]
  have e : 3 * (2 * j + 1) + 12 = 6 * j + 15 := by omega
  rcases b with _ | b
  · have h := end3_s0 a (2 * j + 1); rw [z12] at h
    exact ⟨_, by omega, fin (steps_seq trans hs h) e rfl⟩
  · have h := end3_ss a b (2 * j + 1); rw [z12] at h
    refine ⟨_, by omega, fin (steps_seq trans hs h) e ?_⟩
    unfold Dw
    show _ = app [true, false] (app [false] (rep (b + 1) [true, false, false] _))
    rw [rep_rotate (b + 1) [false] [true, false, false] [false, true, false] rfl]
    rfl

/-- Z ≡ 3 mod 4, a = 0: D(0, b) becomes R(3b + 5), Z' = 3(Z + 1)/2. -/
theorem phase_D0 (b j : Nat) : ∃ s, 6 * j + 18 ≤ s ∧ steps s (PS (Dw 0 b) (4 * j + 11)) = some (PS (Rw (3 * b + 5)) (6 * j + 18)) := by
  obtain ⟨s, hs⟩ := to_end (rep 3 [false] (Dw 0 b)) j
  rw [show 4 * j + 11 = 4 * j + 8 + 3 by omega, show PS (Dw 0 b) (4 * j + 8 + 3) =
    PS (rep 3 [false] (Dw 0 b)) (4 * j + 8) by unfold PS; rw [rep_add]]
  have e : 3 * (2 * j + 1) + 15 = 6 * j + 18 := by omega
  rcases b with _ | b
  · have h := end3_00 (2 * j + 1); rw [z15, cons_false_blank] at h
    exact ⟨_, by omega, fin (steps_seq trans hs h) e rfl⟩
  · have h := end3_0s b (2 * j + 1); rw [z15, cons_false_blank] at h
    refine ⟨_, by omega, fin (steps_seq trans hs h) e ?_⟩
    unfold Rw
    have z := zeros 3 b 5 (cons true blank)
    rw [show 3 + 3 * b + 5 = 3 * (b + 1) + 5 by omega] at z
    rw [← z]; rfl

/-- Z ≡ 2 mod 4: R(a+1) becomes D(a, 0), Z' = 3Z/2. -/
theorem phase_R2 (a j : Nat) : ∃ s, 6 * j + 15 ≤ s ∧ steps s (PS (Rw (a + 1)) (4 * j + 10)) = some (PS (Dw a 0) (6 * j + 15)) := by
  obtain ⟨s, hs⟩ := to_end (rep 2 [false] (Rw (a + 1))) j
  rw [show 4 * j + 10 = 4 * j + 8 + 2 by omega, show PS (Rw (a + 1)) (4 * j + 8 + 2) =
    PS (rep 2 [false] (Rw (a + 1))) (4 * j + 8) by unfold PS; rw [rep_add]]
  have e : 3 * (2 * j + 1) + 12 = 6 * j + 15 := by omega
  have h := endR2 a (2 * j + 1); rw [z12] at h
  exact ⟨_, by omega, fin (steps_seq trans hs h) e rfl⟩

end H53125
