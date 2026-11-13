import Leaves

/-!
# The bouncer and the doubling rounds of 1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC

Configurations (tapes read left to right, the head reads the cell after `S>`, `L`, `R` any tapes):

* `Pc x y L`   = `L 0 1^x 0 (10)^y 1 B>`     (the inner bouncer, B on the blank cell right of the tape)
* `Dc m c R`   = `C> 0 (10)^m 1^c R`          (start of a doubling round, at the left end)
* `Jc p i c R` = `1^p B> 1 0 (10)^i 1^c R`    (inside a round)

Proved here for all parameters (leaf rules from `Leaves.lean`, inductions by hand):

* `p_sweeps`: `Pc (x + 2b) y L → Pc x (y + 2b) L`, whatever `L` holds (the bouncer works inside any context);
* `p_one`: with blank tape on the left, `Pc 1 (y+2)` reaches `Dc 1 (2y+12)`: a top-level reset starts the rounds;
* `round`: `Dc m (c + 2m + 6) R → Dc (2m+3) (c+2) R` (the left block grows 1, 5, 13, 29, 61, ... = 2^(r+2) - 3),
  `rounds`: any number of them.

* `reset_halts`: the reset from `1 0 (10)^y 1 B>` on blank tape halts for every `y = 2^j - j - 5`, j ≥ 4.

The end of the other rounds, where the leftover 1s become the outer stock of a second-level counter, and the inner
resets of that level are in `Level2.lean`.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace H127123

open TM

theorem n_pair (n : Nat) (s : Tape) : rep n [true, true] s = rep (2 * n) [true] s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show app [true, true] (rep n [true, true] s) = rep (2 * n + 1 + 1) [true] s
    rw [ih]; rfl
theorem n_cons1 (n : Nat) (s : Tape) : cons true (rep n [true] s) = rep (n + 1) [true] s := rfl
theorem n_1cons (n : Nat) (s : Tape) : rep n [true] (cons true s) = rep (n + 1) [true] s :=
  rep_app_comm n [true] s

/-- `1 0 1 (01)^i 0 X = (10)^(i+2) X`. -/
theorem j_mid (i : Nat) (X : Tape) :
    cons true (cons false (cons true (rep i [false, true] (cons false X)))) = rep (i + 2) [true, false] X := by
  rw [show cons true (rep i [false, true] (cons false X)) = rep i [true, false] (cons true (cons false X)) from
    rep_rotate i [true] [false, true] [true, false] rfl _]
  show app [true, false] (rep i [true, false] (app [true, false] X)) = _
  rw [rep_app_comm]; rfl

/-- On the left, nearest first: `0 (10)^y 1 0 1 0 Z = (01)^(y+2) 0 Z`. -/
theorem p_mid (y : Nat) (Z : Tape) :
    cons false (rep y [true, false] (cons true (cons false (cons true (cons false Z)))))
      = rep (y + 2) [false, true] (cons false Z) := by
  rw [show cons false (rep y [true, false] (cons true (cons false (cons true (cons false Z)))))
      = rep y [false, true] (cons false (cons true (cons false (cons true (cons false Z))))) from
    rep_rotate y [false] [true, false] [false, true] rfl _]
  show rep y [false, true] (app [false, true] (app [false, true] (cons false Z))) = _
  rw [rep_app_comm, rep_app_comm]

/-- `1 (01)^k = (10)^k 1`, on the right. -/
theorem r_rot (k : Nat) (s : Tape) : cons true (rep k [false, true] s) = rep k [true, false] (cons true s) :=
  rep_rotate k [true] [false, true] [true, false] rfl s

/-! ## Configurations -/

/-- `L 0 1^x 0 (10)^y 1 B>`. -/
def Pc (x y : Nat) (L : Tape) : Config := ⟨cons true (rep y [false, true] (cons false (rep x [true] (cons false L)))), blank, .B⟩
/-- `C> 0 (10)^m 1^c R` at the left end. -/
def Dc (m c : Nat) (R : Tape) : Config := ⟨blank, cons false (rep m [true, false] (rep c [true] R)), .C⟩
/-- `1^p B> 1 0 (10)^i 1^c R`. -/
def Jc (p i c : Nat) (R : Tape) : Config := ⟨rep p [true] blank, cons true (cons false (rep i [true, false] (rep c [true] R))), .B⟩

def Reaches (c c' : Config) : Prop := ∃ n, steps n c = some c'
theorem Reaches.of {n : Nat} {c c' : Config} (h : steps n c = some c') : Reaches c c' := ⟨n, h⟩
theorem Reaches.tr {a b c : Config} : Reaches a b → Reaches b c → Reaches a c
  | ⟨n, h1⟩, ⟨m, h2⟩ => ⟨n + m, steps_seq H127123.trans h1 h2⟩

/-! ## The leaf rules on these configurations -/

theorem p_sweep (x y : Nat) (L : Tape) : steps (6 * y + 14) (Pc (x + 2) y L) = some (Pc x (y + 2) L) := by
  have h := l_psweep x y L
  rw [p_mid] at h
  exact h
theorem p_one (y : Nat) : steps (4 * y + 17) (Pc 1 (y + 2) blank) =
    some ⟨blank, cons false (rep (y + 4) [true, false] (cons true blank)), .C⟩ := by
  have h := l_pone y
  have e2 : cons true (cons false (cons true (cons false (cons true (rep (y + 2) [false, true] blank)))))
      = rep (y + 4) [true, false] (cons true blank) := by rw [r_rot]; rfl
  rw [e2] at h
  have e : Pc 1 (y + 2) blank
      = (⟨cons true (rep (y + 2) [false, true] (cons false (cons true blank))), blank, .B⟩ : Config) := by
    simp only [Pc]; rw [show rep 1 [true] (cons false blank) = cons true blank by rw [cons_false_blank]; rfl]
  rw [e]; exact h
theorem pass (n : Nat) : steps (4 * n + 13) ⟨blank, cons false (rep (n + 1) [true, false] (cons true blank)), .C⟩
    = some (Dc 1 (2 * n + 6) blank) := by
  have h := l_pass n
  simp only [n_pair, n_cons1, n_1cons, Nat.mul_add, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul] at h
  exact h
theorem d_start (m c : Nat) (R : Tape) : steps (2 * m + 5) (Dc m (c + 4) R) = some (Jc (2 * m + 1) 0 (c + 2) R) := by
  have h := l_dstart c m R
  rw [n_pair] at h
  exact h
theorem j_step (p i c : Nat) (R : Tape) : steps (6 * i + 14) (Jc (p + 2) i (c + 4) R) = some (Jc p (i + 2) (c + 2) R) := by
  have h := l_jstep c i p R
  rw [j_mid] at h
  exact h
theorem j_end (i c : Nat) (R : Tape) : steps (6 * i + 15) (Jc 1 i (c + 4) R) = some (Dc (i + 3) (c + 2) R) := by
  have h := l_jend c i R
  rw [j_mid] at h
  exact h

/-! ## Inductions -/

theorem p_sweeps (b : Nat) (L : Tape) : ∀ x y : Nat, Reaches (Pc (x + 2 * b) y L) (Pc x (y + 2 * b) L) := by
  induction b with
  | zero => intro x y; exact ⟨0, rfl⟩
  | succ b ih =>
    intro x y
    have h1 := p_sweep (x + 2 * b) y L
    rw [show x + 2 * b + 2 = x + 2 * (b + 1) by omega] at h1
    have h2 := ih x (y + 2)
    rw [show y + 2 + 2 * b = y + 2 * (b + 1) by omega] at h2
    exact (Reaches.of h1).tr h2

/-- A top-level reset: `1 0 (10)^(y+2) 1 B>` on blank tape reaches `C> 0 (10) 1^(2y+12)`. -/
theorem top_reset (y : Nat) : Reaches (Pc 1 (y + 2) blank) (Dc 1 (2 * y + 12) blank) := by
  have h2 := pass (y + 3)
  rw [show y + 3 + 1 = y + 4 by omega, show 2 * (y + 3) + 6 = 2 * y + 12 by omega] at h2
  exact (Reaches.of (p_one y)).tr (Reaches.of h2)

theorem j_iter (j : Nat) (R : Tape) : ∀ p i c : Nat, Reaches (Jc (p + 2 * j) i (c + 2 + 2 * j) R) (Jc p (i + 2 * j) (c + 2) R) := by
  induction j with
  | zero => intro p i c; exact ⟨0, rfl⟩
  | succ j ih =>
    intro p i c
    have h1 := j_step (p + 2 * j) i (c + 2 * j) R
    rw [show p + 2 * j + 2 = p + 2 * (j + 1) by omega, show c + 2 * j + 4 = c + 2 + 2 * (j + 1) by omega,
      show c + 2 * j + 2 = c + 2 + 2 * j by omega] at h1
    have h2 := ih p (i + 2) c
    rw [show i + 2 + 2 * j = i + 2 * (j + 1) by omega] at h2
    exact (Reaches.of h1).tr h2

/-- **One doubling round.** `C> 0 (10)^m 1^(c+2m+6) R` reaches `C> 0 (10)^(2m+3) 1^(c+2) R`. -/
theorem round (m c : Nat) (R : Tape) : Reaches (Dc m (c + 2 * m + 6) R) (Dc (2 * m + 3) (c + 2) R) := by
  have h1 := d_start m (c + 2 * m + 2) R
  rw [show c + 2 * m + 2 + 4 = c + 2 * m + 6 by omega, show c + 2 * m + 2 + 2 = c + 2 + 2 + 2 * m by omega,
    show 2 * m + 1 = 1 + 2 * m by omega] at h1
  have h2 := j_iter m R 1 0 (c + 2)
  rw [show 0 + 2 * m = 2 * m by omega, show c + 2 + 2 = c + 4 by omega] at h2
  have h3 := j_end (2 * m) c R
  exact (Reaches.of h1).tr (h2.tr (Reaches.of h3))

/-- The left block after `n` rounds from `m`, and the 1s they use. -/
def rM : Nat → Nat → Nat
  | 0, m => m
  | n + 1, m => rM n (2 * m + 3)
def rUse : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, m => 2 * m + 4 + rUse n (2 * m + 3)

theorem rounds (n : Nat) (R : Tape) : ∀ m c : Nat, Reaches (Dc m (c + 2 + rUse n m) R) (Dc (rM n m) (c + 2) R) := by
  induction n with
  | zero => intro m c; exact ⟨0, rfl⟩
  | succ n ih =>
    intro m c
    have h1 := round m (c + rUse n (2 * m + 3)) R
    rw [show c + rUse n (2 * m + 3) + 2 * m + 6 = c + 2 + rUse (n + 1) m by simp [rUse]; omega,
      show c + rUse n (2 * m + 3) + 2 = c + 2 + rUse n (2 * m + 3) by omega] at h1
    exact h1.tr (ih (2 * m + 3) c)

/-- From a top-level reset `1 0 (10)^(y+2) 1 B>` the doubling rounds run as long as the 1s last. -/
theorem reset_rounds (n y c : Nat) (h : 2 * y + 12 = c + 2 + rUse n 1) :
    Reaches (Pc 1 (y + 2) blank) (Dc (rM n 1) (c + 2) blank) := by
  have h2 := rounds n blank 1 c
  rw [← h] at h2
  exact (top_reset y).tr h2

/-! ## The halting resets -/

theorem d_halt (m : Nat) : Halts trans (Dc m 2 blank) := ⟨2 * m + 3, _, l_dhalt m, rfl⟩

theorem rUse_closed (n : Nat) : ∀ m : Nat, rUse n m + 2 * n + 2 * (m + 3) = 2 ^ (n + 1) * (m + 3) := by
  induction n with
  | zero => intro m; simp [rUse]
  | succ n ih =>
    intro m
    have h := ih (2 * m + 3)
    have e : 2 ^ (n + 1 + 1) * (m + 3) = 2 ^ (n + 1) * (2 * m + 3 + 3) := by
      rw [Nat.pow_succ, Nat.mul_assoc]; congr 1
    simp only [rUse]; rw [e]; omega

/-- **The halting resets.** From `1 0 (10)^y 1 B>` on blank tape (the top-level empty tank) the machine halts
whenever `y = 2^j - j - 5` (j ≥ 4: y = 7, 22, 53, 116, 243, ...): the doubling rounds leave exactly two 1s. -/
theorem reset_halts (n y : Nat) (h : y + n + 7 = 2 ^ (n + 2)) (hy : 2 ≤ y) : Halts trans (Pc 1 y blank) := by
  obtain ⟨y', rfl⟩ : ∃ y', y = y' + 2 := ⟨y - 2, by omega⟩
  have hc := rUse_closed n 1
  have hp : 2 ^ (n + 2) = 2 ^ (n + 1) * 2 := Nat.pow_succ 2 (n + 1)
  have hr := reset_rounds n y' 0 (by omega)
  obtain ⟨k, hk⟩ := hr
  obtain ⟨k2, c2, h2, h3⟩ := d_halt (rM n 1)
  exact ⟨k + k2, c2, steps_seq H127123.trans hk h2, h3⟩

end H127123
