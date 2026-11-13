import Leaves

/-!
# The bouncer and the ternary rounds of 1RB0RB_1LC0LF_1RD0LB_1RE1RC_0RA---_1LA1RE

Configurations (tapes read left to right, the head reads the cell after `S>`, `R` any tape):

* `Qc x y`     = `1^x 0 (10)^y A>`                     (the bouncer; A on the blank cell right of the tape)
* `Lc a k R`   = `C> 0 (10)^a 1 1 0 (10)^k R`           (start of a ternary round, at the left end)
* `Sc p m k R` = `1^p F> 1 0 0 (10)^m 1 1 0 (10)^k R`   (inside a round)

Proved here for all parameters (leaf rules from `Leaves.lean`, inductions by hand):

* `q_sweep`: `Qc (x+3) y → Qc (x+1) (y+2)`; `q_one`: `Qc 1 y → Qc (2y+8) 0`;
  `q_to_two`: every `Qc x y` with `x ≥ 1` reaches `Qc 2 y'` with an explicit `y'` (`next2`);
* `blank_to_q`: blank tape reaches `Qc 6 0`, then `Qc 2 4`;
* `q_two`: `Qc 2 (y+2) → Lc 2 (y+2) (1 0^∞)`: every reset of the bouncer starts ternary rounds;
* `round`: `Lc a (k + 2a + 1) R → Lc (3a+2) k R` for `a ≥ 2` (the middle block grows 2, 8, 26, 80, 242, ...),
  and `rounds`: any number of them.

Not proved: what happens when a round runs out of pairs (gaps of 0s appear and the rounds recurse into them); see
the README.  So every halt from blank tape happens inside the reset that starts from some `Qc 2 y`.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace H95029

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
theorem n_ft (n : Nat) (s : Tape) : rep n [false, true] (cons false (cons true s)) = rep (n + 1) [false, true] s :=
  rep_app_comm n [false, true] s
theorem n_ftl (n : Nat) (s : Tape) : cons false (cons true (rep n [false, true] s)) = rep (n + 1) [false, true] s :=
  rfl

/-- `1 0 1 (01)^m 0 1 0 1 T = (10)^(m+3) 1 T`. -/
theorem n_mid (m : Nat) (T : Tape) :
    cons true (cons false (cons true (rep m [false, true] (cons false (cons true (cons false (cons true T)))))))
      = rep (m + 3) [true, false] (cons true T) := by
  rw [show cons true (rep m [false, true] (cons false (cons true (cons false (cons true T)))))
      = rep m [true, false] (cons true (cons false (cons true (cons false (cons true T))))) from
    rep_rotate m [true] [false, true] [true, false] rfl _]
  show app [true, false] (rep m [true, false] (app [true, false] (app [true, false] (cons true T)))) = _
  rw [rep_app_comm, rep_app_comm]; rfl

/-! ## Configurations -/

/-- `1^x 0 (10)^y A>`. -/
def Qc (x y : Nat) : Config := ⟨rep y [false, true] (cons false (rep x [true] blank)), blank, .A⟩
/-- `C> 0 (10)^a 1 1 0 (10)^k R` at the left end. -/
def Lc (a k : Nat) (R : Tape) : Config :=
  ⟨blank, cons false (rep a [true, false] (cons true (cons true (cons false (rep k [true, false] R))))), .C⟩
/-- `1^p F> 1 0 0 (10)^m 1 1 0 (10)^k R`. -/
def Sc (p m k : Nat) (R : Tape) : Config :=
  ⟨rep p [true] blank, cons true (cons false (cons false (rep m [true, false] (cons true (cons true (cons false
    (rep k [true, false] R))))))), .F⟩

def Reaches (c c' : Config) : Prop := ∃ n, steps n c = some c'
theorem Reaches.of {n : Nat} {c c' : Config} (h : steps n c = some c') : Reaches c c' := ⟨n, h⟩
theorem Reaches.tr {a b c : Config} : Reaches a b → Reaches b c → Reaches a c
  | ⟨n, h1⟩, ⟨m, h2⟩ => ⟨n + m, steps_seq H95029.trans h1 h2⟩

/-! ## The leaf rules on these configurations -/

theorem q_sweep (x y : Nat) : steps (6 * y + 16) (Qc (x + 3) y) = some (Qc (x + 1) (y + 2)) := by
  have h := l_qsweep x y
  simp only [n_cons1, n_ft, n_ftl, Nat.add_assoc, Nat.reduceAdd] at h
  exact h
theorem q_one (y : Nat) : steps (4 * y + 15) (Qc 1 y) = some (Qc (2 * y + 8) 0) := by
  have h := l_qone y
  simp only [n_pair, n_cons1, n_1cons, Nat.add_assoc, Nat.reduceAdd] at h
  exact h
theorem q_two (y : Nat) : steps (2 * y + 21) (Qc 2 (y + 2)) = some (Lc 2 (y + 2) (cons true blank)) := l_qtwo y
theorem l_to_s (m k : Nat) (R : Tape) : steps (2 * m + 16) (Lc (m + 2) (k + 2) R) = some (Sc (2 * m + 2) 1 (k + 1) R) := by
  have h := l_ls k m R
  rw [n_pair, show 2 * (m + 1) = 2 * m + 2 by omega] at h
  exact h
theorem s_step (p m k : Nat) (R : Tape) : steps (6 * m + 24) (Sc (p + 2) m (k + 2) R) = some (Sc p (m + 3) k R) := by
  have h := l_sit k m p R
  rw [n_mid] at h
  exact h
theorem s_end (m k : Nat) (R : Tape) : steps (6 * m + 24) (Sc 0 m (k + 2) R) = some (Lc (m + 4) k R) := by
  have h := l_sl k m R
  rw [n_mid] at h
  exact h

/-! ## The bouncer -/

theorem q_sweeps (b : Nat) : ∀ x y : Nat, Reaches (Qc (x + 1 + 2 * b) y) (Qc (x + 1) (y + 2 * b)) := by
  induction b with
  | zero => intro x y; exact ⟨0, rfl⟩
  | succ b ih =>
    intro x y
    have h1 := q_sweep (x + 2 * b) y
    rw [show x + 2 * b + 3 = x + 1 + 2 * (b + 1) by omega, show x + 2 * b + 1 = (x + 2) + 1 + 2 * b - 2 by omega] at h1
    have h2 := ih x (y + 2)
    rw [show y + 2 + 2 * b = y + 2 * (b + 1) by omega] at h2
    have h1' : Reaches (Qc (x + 1 + 2 * (b + 1)) y) (Qc (x + 1 + 2 * b) (y + 2)) := by
      refine Reaches.of (n := 6 * y + 16) ?_
      rw [show x + 1 + 2 * b = x + 2 + 1 + 2 * b - 2 by omega]; exact h1
    exact h1'.tr h2

/-- The `y` of the `Qc 2 y` the bouncer reaches from `Qc x y` (`x ≥ 1`). -/
def next2 (x y : Nat) : Nat := if x % 2 = 0 then y + x - 2 else 2 * (y + x - 1) + 6

theorem q_to_two (x y : Nat) (hx : 1 ≤ x) : Reaches (Qc x y) (Qc 2 (next2 x y)) := by
  obtain ⟨b, hb | hb⟩ : ∃ b, x = 2 * b + 2 ∨ x = 2 * b + 1 := ⟨(x - 1) / 2, by omega⟩
  · subst hb
    have h := q_sweeps b 1 y
    rw [show 1 + 1 + 2 * b = 2 * b + 2 by omega] at h
    have e : next2 (2 * b + 2) y = y + 2 * b := by unfold next2; rw [if_pos (by omega)]; omega
    rw [e]; exact h
  · subst hb
    have h1 := q_sweeps b 0 y
    rw [show 0 + 1 + 2 * b = 2 * b + 1 by omega] at h1
    have h2 := Reaches.of (q_one (y + 2 * b))
    have h3 := q_sweeps (y + 2 * b + 3) 1 0
    rw [show 1 + 1 + 2 * (y + 2 * b + 3) = 2 * (y + 2 * b) + 8 by omega] at h3
    have e : next2 (2 * b + 1) y = 0 + 2 * (y + 2 * b + 3) := by unfold next2; rw [if_neg (by omega)]; omega
    rw [e]; exact h1.tr (h2.tr h3)

/-- Blank tape reaches `1^6 0 A>` in 11 steps. -/
theorem blank_to_q : steps 11 init = some (Qc 6 0) := by
  have h : TM.fsteps trans 11 (FCfg.blank .A) = some ⟨[false, true, true, true, true, true, true], [], .A⟩ := by
    decide
  have e := blank_reaches trans h
  have e2 : app [false, true, true, true, true, true, true] blank = rep 0 [false, true] (cons false (rep 6 [true] blank)) := rfl
  simp only [FCfg.toCfg] at e
  rw [e2] at e
  exact e

theorem blank_to_two : Reaches init (Qc 2 4) := (Reaches.of blank_to_q).tr (q_to_two 6 0 (by omega))

/-! ## The ternary rounds -/

theorem s_iter (j : Nat) (R : Tape) : ∀ p m k : Nat, Reaches (Sc (p + 2 * j) m (k + 2 * j) R) (Sc p (m + 3 * j) k R) := by
  induction j with
  | zero => intro p m k; exact ⟨0, rfl⟩
  | succ j ih =>
    intro p m k
    have h1 := s_step (p + 2 * j) m (k + 2 * j) R
    rw [show p + 2 * j + 2 = p + 2 * (j + 1) by omega, show k + 2 * j + 2 = k + 2 * (j + 1) by omega] at h1
    have h2 := ih p (m + 3) k
    rw [show m + 3 + 3 * j = m + 3 * (j + 1) by omega] at h2
    exact (Reaches.of h1).tr h2

/-- **One ternary round.** `C> 0 (10)^a 1 1 0 (10)^(k+2a+1) R` reaches `C> 0 (10)^(3a+2) 1 1 0 (10)^k R`. -/
theorem round (a k : Nat) (R : Tape) (ha : 2 ≤ a) : Reaches (Lc a (k + 2 * a + 1) R) (Lc (3 * a + 2) k R) := by
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 2 := ⟨a - 2, by omega⟩
  have h1 := l_to_s m (k + 2 * m + 3) R
  rw [show k + 2 * m + 3 + 2 = k + 2 * (m + 2) + 1 by omega, show k + 2 * m + 3 + 1 = (k + 2) + 2 * (m + 1) by omega,
    show 2 * m + 2 = 0 + 2 * (m + 1) by omega] at h1
  have h2 := s_iter (m + 1) R 0 1 (k + 2)
  have h3 := s_end (1 + 3 * (m + 1)) k R
  rw [show 1 + 3 * (m + 1) + 4 = 3 * (m + 2) + 2 by omega] at h3
  exact (Reaches.of h1).tr (h2.tr (Reaches.of h3))

/-- The middle block after `n` rounds from `a`, and the pairs they use. -/
def rA : Nat → Nat → Nat
  | 0, a => a
  | n + 1, a => rA n (3 * a + 2)
def rUse : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, a => 2 * a + 1 + rUse n (3 * a + 2)

theorem rounds (n : Nat) (R : Tape) : ∀ a k : Nat, 2 ≤ a → Reaches (Lc a (k + rUse n a) R) (Lc (rA n a) k R) := by
  induction n with
  | zero => intro a k _; exact ⟨0, rfl⟩
  | succ n ih =>
    intro a k ha
    have h1 := round a (k + rUse n (3 * a + 2)) R ha
    rw [show k + rUse n (3 * a + 2) + 2 * a + 1 = k + rUse (n + 1) a by simp [rUse]; omega] at h1
    exact h1.tr (ih (3 * a + 2) k (by omega))

/-- From any reset `Qc 2 y` with `y ≥ 2`: the ternary rounds run as long as the pairs last. -/
theorem two_rounds (n y k : Nat) (h : y = k + rUse n 2) (hy : 2 ≤ y) :
    Reaches (Qc 2 y) (Lc (rA n 2) k (cons true blank)) := by
  obtain ⟨y', rfl⟩ : ∃ y', y = y' + 2 := ⟨y - 2, by omega⟩
  have h1 := Reaches.of (q_two y')
  have h2 := rounds n (cons true blank) 2 k (by omega)
  rw [← h] at h2
  exact h1.tr h2

end H95029
