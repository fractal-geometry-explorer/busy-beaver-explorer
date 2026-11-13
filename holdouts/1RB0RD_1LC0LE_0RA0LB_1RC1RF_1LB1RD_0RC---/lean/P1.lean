import Rules

/-! # 1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RC---: phase P1 of the live block, for every size

`Live x y z L` is the tape `L 1 1 (001)^x 0 (001)^y (011)^z 0 A> 0^∞` (the left tape is listed nearest cell first).
One bounce of the inner bouncer maps (x, y, z) to (x+3, y−3, z+1) (`bounce_tail`, and `bounce_z0`, `bounce_z1` for
the first two bounces, in `Rules.lean`); here the bounces are chained by induction. -/

namespace H21160

open TM

def Live (x y z : Nat) (L : Tape) : Tape :=
  cons false (rep z [true, true, false] (rep y [true, false, false]
    (cons false (rep x [true, false, false] (cons true (cons true L))))))

theorem rot011 (n : Nat) (X : Tape) :
    cons true (cons true (rep n [false, true, true] (cons false X))) = rep (n + 1) [true, true, false] X := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    show cons true (cons true (cons false (cons true (cons true (rep n [false, true, true] (cons false X)))))) = _
    rw [ih]; rfl

/-- `bounce_tail` in the coordinates of `Live`: (x, y+4, z+2) → (x+3, y+1, z+3). -/
theorem bounce (x y z : Nat) (L : Tape) :
    steps (36 * y + 24 * z + 151) ⟨Live x (y + 4) (z + 2) L, blank, .A⟩ = some ⟨Live (x + 3) (y + 1) (z + 3) L, blank, .A⟩ := by
  have h := bounce_tail y z x L
  have e1 : Live x (y + 4) (z + 2) L =
      cons false (cons true (cons true (rep (z + 1) [false, true, true] (cons false (rep (y + 4) [true, false, false] (cons false (rep x [true, false, false] (cons true (cons true L))))))))) := by
    unfold Live; rw [rot011]
  have e2 : Live (x + 3) (y + 1) (z + 3) L =
      cons false (cons true (cons true (cons false (cons true (cons true (rep (z + 1) [false, true, true] (cons false (rep (y + 1) [true, false, false] (cons false (cons true (cons false (cons false (cons true (cons false (cons false (cons true (cons false (cons false (rep x [true, false, false] (cons true (cons true L))))))))))))))))))))) := by
    unfold Live; rw [rot011]; rfl
  rw [e1, e2]; exact h

/-- **Phase P1, n bounces.**  (x, y+1+3n, z+2) → (x+3n, y+1, z+2+n), for every x, y, z, n and every tape L. -/
theorem p1 (y : Nat) (L : Tape) (n : Nat) : ∀ x z : Nat,
    ∃ t, steps t ⟨Live x (y + 1 + 3 * n) (z + 2) L, blank, .A⟩ = some ⟨Live (x + 3 * n) (y + 1) (z + 2 + n) L, blank, .A⟩ := by
  induction n with
  | zero => intro x z; exact ⟨0, rfl⟩
  | succ n ih =>
    intro x z
    have h1 := bounce x (y + 3 * n) z L
    rw [show y + 3 * n + 4 = y + 1 + 3 * (n + 1) by omega, show y + 3 * n + 1 = y + 1 + 3 * n by omega,
      show z + 3 = (z + 1) + 2 by omega] at h1
    obtain ⟨t, h2⟩ := ih (x + 3) (z + 1)
    rw [show x + 3 + 3 * n = x + 3 * (n + 1) by omega, show z + 1 + 2 + n = z + 2 + (n + 1) by omega] at h2
    exact ⟨_, steps_seq trans h1 h2⟩

/-- **Phase P1 from an empty right part.**  (x, y+6+3n, 0) → (x+4+3n, y+2, n+2): `bounce_z0`, `bounce_z1`, then `p1`. -/
theorem p1_from0 (x y n : Nat) (L : Tape) :
    ∃ t, steps t ⟨Live x (y + 6 + 3 * n) 0 L, blank, .A⟩ = some ⟨Live (x + 4 + 3 * n) (y + 2) (n + 2) L, blank, .A⟩ := by
  have g0 := bounce_z0 x (y + 4 + 3 * n) L
  rw [show y + 4 + 3 * n + 2 = y + 6 + 3 * n by omega, show y + 4 + 3 * n + 1 = y + 5 + 3 * n by omega] at g0
  have h0 : steps _ ⟨Live x (y + 6 + 3 * n) 0 L, blank, .A⟩ = some ⟨Live (x + 1) (y + 5 + 3 * n) 1 L, blank, .A⟩ := g0
  have g1 := bounce_z1 (x + 1) (y + 1 + 3 * n) L
  rw [show y + 1 + 3 * n + 4 = y + 5 + 3 * n by omega, show y + 1 + 3 * n + 1 = y + 2 + 3 * n by omega] at g1
  have h1 : steps _ ⟨Live (x + 1) (y + 5 + 3 * n) 1 L, blank, .A⟩ = some ⟨Live (x + 4) (y + 2 + 3 * n) 2 L, blank, .A⟩ := g1
  obtain ⟨t, h2⟩ := p1 (y + 1) L n (x + 4) 0
  rw [show y + 1 + 1 + 3 * n = y + 2 + 3 * n by omega, show y + 1 + 1 = y + 2 by omega,
    show 0 + 2 + n = n + 2 by omega] at h2
  exact ⟨_, steps_seq trans (steps_seq trans h0 h1) h2⟩

end H21160
