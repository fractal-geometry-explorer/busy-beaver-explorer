import Rules

/-!
# The E and A phases, for all parameters

`E(x, z)` is `E>0 (10)^x 1^z` with blank tape around (the head at the left end).  From `E(x+1, z)` with
`z >= 2x + 9` the machine reaches `E(2x+6, z-2x-8)`: the alternating block doubles (plus 4) and the solid block pays
for it.  The run goes through the bounce frames `Q(m, j, t)` = `(10)^m 1 D>0 0 (1010)^j 1^t`: a start piece
(`startE` in `Rules.lean`), then one bounce `loopQ` per copy of `10` on the left (proved here for any number of
bounces by induction), then an end piece `endQ`.  The pieces' step counts add up to `4(x+1)^2 + 24(x+1) + 30`
(`Reach` below does not keep the count).

`A(x, y)` is `(10)^x 1^y A>0` (the head on the blank cell right of the tape).  From `A(x, y)` with `y >= 4` even and
`2x >= y + 4` the machine reaches `A(x - y/2 - 2, 2y + 6)`, through the same bounces: a start piece `startA`,
`y/2 - 1` bounces, an end piece `endA` (pieces' counts add up to `y^2 + 6y + 12`).  The E phase and its proof are
the same as for 1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE, which has the same rows D, E, F, A, B.

Written by hand on top of the generated `Rules.lean`.
-/

namespace H35167

open TM

/-- `c` reaches `c'` in some number of ordinary steps. -/
def Reach (c c' : Config) : Prop := ∃ n, steps n c = some c'

theorem Reach.join {a b c : Config} (h₁ : Reach a b) (h₂ : Reach b c) : Reach a c :=
  let ⟨n, hn⟩ := h₁
  let ⟨m, hm⟩ := h₂
  ⟨n + m, steps_seq trans hn hm⟩

theorem reach_of {n : Nat} {c c' c'' : Config} (h : steps n c = some c') (e : c' = c'') : Reach c c'' :=
  ⟨n, e ▸ h⟩

/-- `E(x, z)` = `E>0 (10)^x 1^z`, blank tape around. -/
def Ecfg (x z : Nat) : Config :=
  ⟨blank, cons false (rep x [true, false] (rep z [true] blank)), .E⟩

/-- `Q(m, j, t)` = `(10)^m 1 D>0 0 (1010)^j 1^t`, blank tape around. -/
def Q (m j t : Nat) : Config :=
  ⟨cons true (rep m [false, true] blank), cons false (cons false (rep j [true, false, true, false] (rep t [true] blank))), .D⟩

theorem start (x s : Nat) : Reach (Ecfg (x + 1) (s + 5)) (Q x 1 (s + 1)) :=
  reach_of (startE s x) rfl

theorem bounce (m j r : Nat) : Reach (Q (m + 1) j (r + 3)) (Q m (j + 1) (r + 1)) :=
  reach_of (loopQ j r (rep m [false, true] blank)) rfl

/-- `t` bounces at once. -/
theorem bounces (t : Nat) : ∀ m j r, Reach (Q (m + t) j (r + 2 * t + 1)) (Q m (j + t) (r + 1)) := by
  induction t with
  | zero => intro m j r; exact ⟨0, rfl⟩
  | succ t ih =>
    intro m j r
    have h := bounce (m + t) j (r + 2 * t)
    have h' := ih m (j + 1) r
    rw [show m + (t + 1) = m + t + 1 by omega, show r + 2 * (t + 1) + 1 = r + 2 * t + 3 by omega,
      show j + (t + 1) = j + 1 + t by omega]
    exact h.join h'

theorem rep2 (j : Nat) (Y : Tape) : rep j [true, false, true, false] Y = rep (2 * j) [true, false] Y := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 + 2 * j by omega, rep_add 2 (2 * j), ← ih]
    rfl

theorem endshape (j : Nat) (X : Tape) :
    cons true (cons false (cons true (cons false (cons true (cons false (cons true
      (rep j [false, true, false, true] (cons false (cons true X))))))))) = rep (2 * j + 4) [true, false] (cons true X) := by
  have h1 : cons true (rep j [false, true, false, true] (cons false (cons true X))) =
      rep j [true, false, true, false] (cons true (cons false (cons true X))) :=
    rep_rotate j [true] [false, true, false, true] [true, false, true, false] rfl _
  rw [h1, rep2, show 2 * j + 4 = 3 + (2 * j + 1) by omega, rep_add 3 (2 * j + 1), ← rep_app_comm (2 * j)]
  rfl

theorem finish (j s : Nat) : Reach (Q 0 j (s + 5)) (Ecfg (2 * j + 4) (s + 1)) :=
  reach_of (endQ j s) (by
    show _ = (⟨blank, cons false (rep (2 * j + 4) [true, false] (cons true (rep s [true] blank))), .E⟩ : Config)
    rw [endshape])

/-- The E phase: `E(x+1, u+2x+9)` reaches `E(2x+6, u+1)`. -/
theorem ephase (x u : Nat) : Reach (Ecfg (x + 1) (u + 2 * x + 9)) (Ecfg (2 * x + 6) (u + 1)) := by
  have a := start x (u + 2 * x + 4)
  have b := bounces x 0 1 (u + 4)
  have c := finish (x + 1) u
  rw [show u + 2 * x + 4 + 5 = u + 2 * x + 9 by omega, show u + 2 * x + 4 + 1 = u + 2 * x + 5 by omega] at a
  rw [Nat.zero_add, show u + 4 + 2 * x + 1 = u + 2 * x + 5 by omega, show 1 + x = x + 1 by omega,
    show u + 4 + 1 = u + 5 by omega] at b
  rw [show 2 * (x + 1) + 4 = 2 * x + 6 by omega] at c
  exact a.join (b.join c)

/-- `A(x, y)` = `(10)^x 1^y A>0`, blank tape around. -/
def Acfg (x y : Nat) : Config :=
  ⟨rep y [true] (rep x [false, true] blank), blank, .A⟩

theorem rep11 (n : Nat) (Y : Tape) : rep n [true, true] Y = rep (2 * n) [true] Y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 + 2 * n by omega, rep_add 2 (2 * n), ← ih]
    rfl

theorem rep1111 (n : Nat) (Y : Tape) : rep n [true, true, true, true] Y = rep (4 * n) [true] Y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 4 * (n + 1) = 4 + 4 * n by omega, rep_add 4 (4 * n), ← ih]
    rfl

theorem startA' (x n : Nat) : Reach (Acfg (x + 3) (2 * n + 4)) (Q x 1 (2 * n + 4)) := by
  have h := startA n x
  rw [rep11, rep11, cons_false_blank, show 2 * (n + 2) = 2 * n + 4 by omega,
    show 2 * (n + 1) = 2 * n + 2 by omega] at h
  exact reach_of h rfl

theorem endA' (m j : Nat) : Reach (Q m j 2) (Acfg m (4 * j + 6)) := by
  have h := endA j (rep m [false, true] blank)
  rw [rep1111] at h
  refine reach_of h ?_
  show _ = (⟨rep (4 * j + 6) [true] (rep m [false, true] blank), blank, .A⟩ : Config)
  rw [show 4 * j + 6 = 4 + (4 * j + 2) by omega, rep_add 4 (4 * j + 2), show 4 * j + 2 = 4 * j + 1 + 1 by omega,
    ← rep_app_comm (4 * j + 1), ← rep_app_comm (4 * j)]
  rfl

/-- The A phase: `A(a+n+4, 2n+4)` reaches `A(a, 4n+14)`, that is `A(x, y)` reaches `A(x - y/2 - 2, 2y + 6)` for
even `y >= 4` and `2x >= y + 4`. -/
theorem aphase (a n : Nat) : Reach (Acfg (a + n + 4) (2 * n + 4)) (Acfg a (4 * n + 14)) := by
  have s := startA' (a + n + 1) n
  have l := bounces (n + 1) a 1 1
  have e := endA' a (n + 2)
  rw [show a + n + 1 + 3 = a + n + 4 by omega] at s
  rw [show a + (n + 1) = a + n + 1 by omega, show 1 + 2 * (n + 1) + 1 = 2 * n + 4 by omega,
    show 1 + (n + 1) = n + 2 by omega] at l
  rw [show 4 * (n + 2) + 6 = 4 * n + 14 by omega] at e
  exact s.join (l.join e)

end H35167
