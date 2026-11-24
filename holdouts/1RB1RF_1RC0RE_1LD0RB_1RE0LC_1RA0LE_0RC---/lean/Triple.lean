import Machine
import Rules
import Phase
import HaltRules

/-!
# 1RB1RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_0RC---: a triple with one block after it halts, for every even block size >= 12

A *triple* is three cursor cells 1 side by side (`a 1 1 1`, four 1s on the tape).  The run from blank tape forms
one each time a cursor reaches a cursor that a birth left half way across a separator, but the triple is gone one
visit later, because the cursor that made it is still the active one.  It is left standing only if the end block is
used up at exactly that visit (a birth): then a new cursor starts at the right end, and the triple stays until the
first cursor reaches it.  If that cursor comes as a 0 the machine halts.

`triple_halts` is the case of one block right of the triple: the tape just after such a birth,

    0^inf 1 a b a 0 a 1 1 1 a^10 b a^(2j+12) 0 a 1 B> 0^inf        (a = 01, b = 00110)

halts for every j, that is for every even block size 2j+12 >= 12, so for every size 4^i - 2 >= 14 that the run uses.
The new cursor walks through the block (`feeds`), crosses the separator (`hop0c`, `hop0d`), walks through the a^10
(`feedbs`) and arrives as a 0 with an end block of 4j+2 left; the next round trip halts (`tohalt`).  The left part
`1 a b a 0 a` is the one of `Escape.lean`; the head crosses it on every visit, so a statement for every left part needs
the rules for crossing the whole queue, which are not in Lean.
-/

namespace H75404

open TM

/-- `0^inf 1 a b a 0 a 1 1 1` read from its right end outwards: the four 1s, `0`, `b`, `a`, `1`. -/
def LT : Tape :=
  cons true (cons true (cons true (cons true (cons false (cons false (cons true (cons false (cons false (cons true
    (cons true (cons false (cons false (cons true (cons false (cons true blank)))))))))))))))

/-- `b = 00110` in front of `X`, read from the head outwards. -/
def bb (X : Tape) : Tape := cons false (cons true (cons true (cons false (cons false X))))

/-- `L a^k c a^m b a^n 0 B> 0^inf`: a cursor c with a separator between it and the end block. -/
def Fb (c : Bool) (k m n : Nat) (L : Tape) : Config :=
  ⟨cons false (rep n [true, false] (bb (rep m [true, false] (cons c (rep k [true, false] L))))), blank, .B⟩

theorem feedb0' (k m n : Nat) (L : Tape) :
    steps (4 * m + 4 * n + 52) (Fb false (k + 1) m (n + 2) L) = some (Fb true k (m + 4) n L) := by
  have h := feedb0 k m n L
  rw [rot] at h
  unfold Fb bb
  rw [show m + 4 = 2 + (m + 2) by omega, rep_add 2 (m + 2), rep_add m 2]
  exact h

theorem feedb1' (k m n : Nat) (L : Tape) :
    steps (4 * m + 4 * n + 44) (Fb true (k + 1) m (n + 2) L) = some (Fb false k (m + 4) n L) := by
  have h := feedb1 k m n L
  rw [rot] at h
  unfold Fb bb
  rw [show m + 4 = 2 + (m + 2) by omega, rep_add 2 (m + 2), rep_add m 2]
  exact h

theorem feedb2 (k m n : Nat) (L : Tape) :
    steps (8 * m + 8 * n + 120) (Fb false (k + 2) m (n + 4) L) = some (Fb false k (m + 8) n L) := by
  have h1 := feedb0' (k + 1) m (n + 2) L
  have h2 := feedb1' k (m + 4) n L
  rw [show m + 8 = m + 4 + 4 by omega, show 8 * m + 8 * n + 120 = (4 * m + 4 * (n + 2) + 52) +
    (4 * (m + 4) + 4 * n + 44) by omega]
  exact steps_seq trans h1 h2

/-- The steps of i double visits with a separator, from cursor block m and end block n + 4i. -/
def feedbs_steps (m n : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => (8 * m + 8 * (n + 4 * i) + 120) + feedbs_steps (m + 8) n i

theorem feedbs (i k m n : Nat) (L : Tape) :
    steps (feedbs_steps m n i) (Fb false (k + 2 * i) m (n + 4 * i) L) = some (Fb false k (m + 8 * i) n L) := by
  induction i generalizing m with
  | zero => rfl
  | succ i ih =>
    have h1 := feedb2 (k + 2 * i) m (n + 4 * i) L
    have h2 := ih (m + 8)
    rw [show m + 8 * (i + 1) = m + 8 + 8 * i by omega, show k + 2 * (i + 1) = k + 2 * i + 2 by omega,
      show n + 4 * (i + 1) = n + 4 * i + 4 by omega]
    exact steps_seq trans h1 h2

/-- The tape just after a birth that left a triple standing, with one block `b a^(2j+12)` right of it. -/
def tripleStart (j : Nat) : Config :=
  ⟨cons true (cons true (cons false (cons false (rep (2 * j + 12) [true, false] (bb (rep 10 [true, false] LT)))))),
    blank, .B⟩

theorem triple_halts (j : Nat) : Halts trans (tripleStart j) := by
  -- the visit after the birth: `L 0 a^2 0 B>`
  have h0 : steps 6 (tripleStart j) = some (Fd false (2 * j + 12) 2 (bb (rep 10 [true, false] LT))) :=
    birth2 _
  -- the new cursor walks through the block: the end block grows to 4j+26
  have h1 := feeds (j + 6) 0 2 (bb (rep 10 [true, false] LT))
  rw [show 0 + 2 * (j + 6) = 2 * j + 12 by omega, show 2 + 4 * (j + 6) = (4 * j + 24) + 2 by omega] at h1
  -- it crosses the separator
  have h2 := hop0c (4 * j + 24) (rep 10 [true, false] LT)
  have h3 := hop0d (4 * j + 22) (rep 10 [true, false] LT)
  -- and walks through a^10
  have h4 := feedbs 5 0 6 (4 * j + 2) LT
  rw [show 0 + 2 * 5 = 10 by omega, show 4 * j + 2 + 4 * 5 = 4 * j + 22 by omega,
    show 6 + 8 * 5 = 45 + 1 by omega] at h4
  -- it arrives as a 0 next to the triple: the next round trip halts
  have h5 := tohalt 45 (4 * j + 2)
  have h := steps_seq trans h0 (steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3
    (steps_seq trans h4 h5))))
  exact ⟨_, _, h, rfl⟩

end H75404
