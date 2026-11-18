import Machine

/-!
# 1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC---: the four rules that differ from DeepMind's halting sibling

This machine's table, mirrored and with its states renamed, is `1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0RA---`
started in state C. DeepMind's busycoq PR 93 proves that `1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD---` halts; that
machine is the same table except for the one transition F0 (`0RD` there, `0LC` here). Its proof runs a fast engine
built from macro rules about three configurations, written in that file's (mirrored) orientation as

* `CfgR l r = l A> 0100 r`, `CfgL l r = l <B 1 r` and `CfgJ l r = l <C 100 r`.

All of its rules hold for this machine too except four, the ones that end in `CfgJ` (they pass through F0).  Here
they end in `CfgL` instead, with `11` more on the right: a `CfgJ l X` there is a `CfgL l (11 X)` here.  The four
theorems below are those rules for this machine, for every tape `L` and `R` (`L` is the far left of the mirrored
picture, so it is the right tape here) and every count.

In this machine's own orientation (head on `r 0`, left tape nearest cell first) the three configurations are
`CfgR X Y = ⟨100 Y, 0 X, C⟩`, `CfgL X Y = ⟨1 Y, X, D⟩` and `CfgJ X Y = ⟨100 Y, X, A⟩`; words are written
nearest the head first.  `D n = 1 (11)^n 00` is the digit word of the engine.

The engine with these four rules changed (`tools/coq/t4engine`) agrees with direct simulation.
-/

namespace H127983

open TM

/-- A crossing to the right with the head cell `h` carried along: `L` gains `v` for each `w` taken from `R`. -/
theorem crossH {s : Nat} {q : St} {h : Bool} {w v : List Bool}
    (hyp : ∀ L R : Tape, steps s ⟨L, cons h (app w R), q⟩ = some ⟨app v L, cons h R, q⟩) (k : Nat) :
    ∀ L R : Tape, steps (k * s) ⟨L, cons h (rep k w R), q⟩ = some ⟨rep k v L, cons h R, q⟩ := by
  induction k with
  | zero => intro L R; simp
  | succ k ih =>
    intro L R
    have e : (k + 1) * s = s + k * s := by rw [Nat.succ_mul, Nat.add_comm]
    rw [e]
    have h₂ := ih (app v L) R
    rw [rep_app_comm] at h₂
    exact TM.steps_seq trans (hyp L (rep k w R)) h₂

/-- A crossing to the left with the head cell `h` carried along: `R` gains `v` for each `w` taken from `L`. -/
theorem crossH' {s : Nat} {q : St} {h : Bool} {w v : List Bool}
    (hyp : ∀ L R : Tape, steps s ⟨app w L, cons h R, q⟩ = some ⟨L, cons h (app v R), q⟩) (k : Nat) :
    ∀ L R : Tape, steps (k * s) ⟨rep k w L, cons h R, q⟩ = some ⟨L, cons h (rep k v R), q⟩ := by
  induction k with
  | zero => intro L R; simp
  | succ k ih =>
    intro L R
    have e : (k + 1) * s = s + k * s := by rw [Nat.succ_mul, Nat.add_comm]
    rw [e]
    have h₂ := ih L (app v R)
    rw [rep_app_comm] at h₂
    exact TM.steps_seq trans (hyp (rep k w L) R) h₂

/-- Collision: `CfgL (001101 X) Y` reaches `CfgL X (111111 Y)` in 10 steps.  (DeepMind's sibling: `CfgJ X (1111 Y)`.) -/
theorem t4_collision (X Y : Tape) :
    steps 10 ⟨app [true] Y, app [false, false, true, true, false, true] X, .D⟩ =
      some ⟨app [true] (app [true, true, true, true, true, true] Y), X, .D⟩ := rfl

/-- Collide: `CfgR X (10 D0 D0 Y)` reaches `CfgL X (D3 10 Y)` in 39 steps.  (Sibling: `CfgJ X (D2 10 Y)`.) -/
theorem t4_collide (X Y : Tape) :
    steps 39 ⟨app [true, false, false, true, false, true, false, false, true, false, false] Y, cons false X, .C⟩ =
      some ⟨app [true, true, true, true, true, true, true, true, false, false, true, false] Y, X, .D⟩ := rfl

/-- Finish: `CfgL (1 (01)^(b+3) X) Y`, the left word `S0 · 01 · (10)^(1+b)` of the sibling's rule, reaches
`CfgL X (D (2+b) Y)` in `2b + 9` steps; `1 · D (2+b) = (11)^(b+3) 00`.  (Sibling: `CfgJ X (D (1+b) Y)`.) -/
theorem t4_finishP (b : Nat) (X Y : Tape) :
    steps (2 * b + 9) ⟨app [true] Y, cons true (cons false (rep (b + 2) [true, false] (cons true X))), .D⟩ =
      some ⟨rep (b + 3) [true, true] (cons false (cons false Y)), X, .D⟩ := by
  have h0 : steps 3 ⟨app [true] Y, cons true (cons false (rep (b + 2) [true, false] (cons true X))), .D⟩ =
      some ⟨app [false, false] Y, cons false (rep (b + 2) [true, false] (cons true X)), .D⟩ := rfl
  have c1 : ∀ L R : Tape, steps 2 ⟨L, cons false (app [true, false] R), .D⟩ =
      some ⟨app [true, true] L, cons false R, .D⟩ := fun _ _ => rfl
  have h1 := crossH c1 (b + 2) (app [false, false] Y) (cons true X)
  have h2 : steps 2 ⟨rep (b + 2) [true, true] (app [false, false] Y), cons false (cons true X), .D⟩ =
      some ⟨app [true, true] (rep (b + 2) [true, true] (app [false, false] Y)), X, .D⟩ := rfl
  have h := TM.steps_seq trans (TM.steps_seq trans h0 h1) h2
  exact TM.steps_congr trans (by omega) h

/-- Defect: `CfgR X (10 D0 1 (11)^m 0 Y)` reaches `CfgL X (111111 (D m) 1 Y)` in `8m + 39` steps;
`1 · 111111 · D m · 1 = (11)^(m+4) 001`.  (Sibling: `CfgJ X (1111 (D m) 1 Y)`.) -/
theorem t4_defect0 (m : Nat) (X Y : Tape) :
    steps (8 * m + 39)
        ⟨app [true, false, false, true, false, true, false, false, true] (rep m [true, true] (cons false Y)),
          cons false X, .C⟩ =
      some ⟨rep (m + 4) [true, true] (app [false, false, true] Y), X, .D⟩ := by
  have h0 : steps 15
        ⟨app [true, false, false, true, false, true, false, false, true] (rep m [true, true] (cons false Y)),
          cons false X, .C⟩ =
      some ⟨rep (m + 1) [true, true] (cons false Y),
        cons false (app [true, false, false, true, true, false, true] X), .C⟩ := rfl
  have c1 : ∀ L R : Tape, steps 6 ⟨app [true, true] L, cons false R, .C⟩ =
      some ⟨L, cons false (app [true, false] R), .C⟩ := fun _ _ => rfl
  have h1 := crossH' c1 (m + 1) (cons false Y) (app [true, false, false, true, true, false, true] X)
  have h2 : steps 6 ⟨cons false Y, cons false (rep (m + 1) [true, false] (app [true, false, false, true, true, false, true] X)), .C⟩ =
      some ⟨app [false, false, true] Y, cons false (rep m [true, false] (app [true, false, false, true, true, false, true] X)), .D⟩ := rfl
  have c3 : ∀ L R : Tape, steps 2 ⟨L, cons false (app [true, false] R), .D⟩ =
      some ⟨app [true, true] L, cons false R, .D⟩ := fun _ _ => rfl
  have h3 := crossH c3 (m + 1) (app [false, false, true] Y) (app [false, true, true, false, true] X)
  have e3 : rep (m + 1) [true, false] (app [false, true, true, false, true] X) =
      rep m [true, false] (app [true, false, false, true, true, false, true] X) := by
    rw [← rep_app_comm]; rfl
  rw [e3] at h3
  have h4 : steps 10 ⟨rep (m + 1) [true, true] (app [false, false, true] Y), cons false (app [false, true, true, false, true] X), .D⟩ =
      some ⟨rep (m + 4) [true, true] (app [false, false, true] Y), X, .D⟩ := rfl
  have h := TM.steps_seq trans (TM.steps_seq trans (TM.steps_seq trans (TM.steps_seq trans h0 h1) h2) h3) h4
  exact TM.steps_congr trans (by omega) h

end H127983
