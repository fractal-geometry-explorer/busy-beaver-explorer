import Rules

/-!
# The E phase, for all parameters

`E(x, z)` is `E>0 (10)^x 1^z` with blank tape around (the head at the left end).  From `E(x+1, z)` with
`z >= 2x + 9` the machine reaches `E(2x+6, z-2x-8)`: the alternating block doubles (plus 4) and the solid block pays
for it.  The run goes through the bounce frames `Q(m, j, t)` = `(10)^m 1 A>0 0 (1010)^j 1^t`: a start piece
(`startE` in `Rules.lean`), then one bounce `loopQ` per copy of `10` on the left (proved here for any number of
bounces by induction), then an end piece `endQ`.  `Reach` below does not keep the step count.

The pieces and the frame `Q` are those of 1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE with its state D called A here.

Written by hand on top of the generated `Rules.lean`.
-/

namespace H137865

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

/-- `Q(m, j, t)` = `(10)^m 1 A>0 0 (1010)^j 1^t`, blank tape around. -/
def Q (m j t : Nat) : Config :=
  ⟨cons true (rep m [false, true] blank), cons false (cons false (rep j [true, false, true, false] (rep t [true] blank))), .A⟩

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

end H137865
