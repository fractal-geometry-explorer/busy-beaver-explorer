import Rules

/-!
# The P-map of 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---, for every n

* `P n  = 0^∞ (101)^n 01 A> 0^∞`
* `Q n  = 0^∞ (101)^n 110101 A> 0^∞` (the start of an excursion)
* `DL a b R = 0^∞ (101)^a D> 10 (01)^b R` (the D-loop)

From `P n` the head turns (`start`), the D-loop moves the `(101)^n` block one copy at a time to the right as
`(01)^(2n)` (`dloop`, iterated by induction in `diter`), and a right sweep turns every three `10` into two `101`
(`ph2a`, `ph2b`, `ph2c`).  The theorems `p0`, `p1`, `p2` are the three residues of n mod 3:

* `P (3k)   → P (4k+2)` in 27k² + 87k + 35 steps,
* `P (3k+1) → P (4k+3)` in 27k² + 105k + 62 steps,
* `P (3k+2) → Q (4k+4)` in 27k² + 123k + 117 steps.

`blank_Q80`: from blank tape the machine reaches P 1 after 14 steps and then, through P 3, 6, 10, 15, 22, 31, 43,
59, the excursion start Q 80 after 27,264 steps.  All of it is checked by Lean's kernel.
-/

namespace H107543

open TM

set_option linter.unusedSimpArgs false

/-- Polynomial step counts: expand products, then `omega` (with `k * k` as an atom). -/
macro "poly_steps" : tactic =>
  `(tactic| grind)

def P (n : Nat) : Config := ⟨cons true (cons false (rep n [true, false, true] blank)), blank, .A⟩
def Q (n : Nat) : Config :=
  ⟨cons true (cons false (cons true (cons false (cons true (cons true (rep n [true, false, true] blank)))))), blank, .A⟩
def DL (a b : Nat) (R : Tape) : Config :=
  ⟨rep a [true, false, true] blank, cons true (cons false (rep b [false, true] R)), .D⟩

theorem dloop (a b : Nat) (R : Tape) : steps (6 * a + 20) (DL (a + 1) b R) = some (DL a (b + 2) R) := by
  have h := r_dloop a b R
  simpa [DL, rep_succ] using h

theorem diter : ∀ a b (R : Tape), steps (3 * a * a + 17 * a) (DL a b R) = some (DL 0 (b + 2 * a) R) := by
  intro a
  induction a with
  | zero => intro b R; rfl
  | succ a ih =>
    intro b R
    have h := steps_seq trans (dloop a b R) (ih (b + 2) R)
    rw [show b + 2 + 2 * a = b + 2 * (a + 1) by omega] at h
    exact steps_congr trans (by poly_steps) h

theorem start (n : Nat) : steps 18 (P n) = some (DL n 2 blank) := by
  have h := r_start n
  simpa [P, DL, rep_succ] using h

theorem rep6 (k : Nat) (s : Tape) :
    rep (6 * k) [false, true] s
      = rep k [false, true, false, true, false, true, false, true, false, true, false, true] s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 6 * (k + 1) = 6 + 6 * k by omega, rep_add, ih, rep_succ]
    rfl

theorem rep4 (k : Nat) (s : Tape) :
    rep k [true, false, true, true, false, true, true, false, true, true, false, true] s
      = rep (4 * k) [true, false, true] s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [rep_succ, ih, show 4 * (k + 1) = 4 + 4 * k by omega, rep_add]
    rfl

theorem dl_split (k j : Nat) (R : Tape) :
    DL 0 (6 * k + j) R = ⟨blank, cons true (cons false (rep k
      [false, true, false, true, false, true, false, true, false, true, false, true] (rep j [false, true] R))), .D⟩ := by
  simp only [DL, rep_add, rep6, rep_zero]

theorem ph2a (k : Nat) : steps (36 * k + 17) (DL 0 (6 * k + 2) blank) = some (P (4 * k + 2)) := by
  have h := r_ph2a k
  rw [dl_split]
  have e : rep (4 * k + 2) [true, false, true] blank
      = app [true, false, true] (rep (4 * k) [true, false, true] (app [true, false, true] blank)) := by
    rw [rep_app_comm, show 4 * k + 2 = 4 * k + 1 + 1 by omega, rep_succ]
  simp only [P, e, ← rep4]
  simpa [rep_succ] using h

theorem ph2b (k : Nat) : steps (36 * k + 24) (DL 0 (6 * k + 4) blank) = some (P (4 * k + 3)) := by
  have h := r_ph2b k
  rw [dl_split]
  have e : rep (4 * k + 3) [true, false, true] blank
      = app [true, false, true] (app [true, false, true]
          (rep (4 * k) [true, false, true] (app [true, false, true] blank))) := by
    rw [rep_app_comm, show 4 * k + 3 = 4 * k + 1 + 1 + 1 by omega, rep_succ, rep_succ]
  simp only [P, e, ← rep4]
  simpa [rep_succ] using h

theorem ph2c (k : Nat) : steps (36 * k + 53) (DL 0 (6 * k + 6) blank) = some (Q (4 * k + 4)) := by
  have h := r_ph2c k
  rw [dl_split]
  have e : rep (4 * k + 4) [true, false, true] blank
      = app [true, false, true] (app [true, false, true] (app [true, false, true]
          (rep (4 * k) [true, false, true] (app [true, false, true] blank)))) := by
    rw [rep_app_comm, show 4 * k + 4 = 4 * k + 1 + 1 + 1 + 1 by omega, rep_succ, rep_succ, rep_succ]
  simp only [Q, e, ← rep4]
  simpa [rep_succ] using h

/-- n = 3k: P (3k) → P (4k+2). -/
theorem p0 (k : Nat) : steps (27 * k * k + 87 * k + 35) (P (3 * k)) = some (P (4 * k + 2)) := by
  have h := steps_seq trans (steps_seq trans (start (3 * k)) (diter (3 * k) 2 blank))
    (by rw [show 2 + 2 * (3 * k) = 6 * k + 2 by omega]; exact ph2a k)
  exact steps_congr trans (by poly_steps) h

/-- n = 3k+1: P (3k+1) → P (4k+3). -/
theorem p1 (k : Nat) : steps (27 * k * k + 105 * k + 62) (P (3 * k + 1)) = some (P (4 * k + 3)) := by
  have h := steps_seq trans (steps_seq trans (start (3 * k + 1)) (diter (3 * k + 1) 2 blank))
    (by rw [show 2 + 2 * (3 * k + 1) = 6 * k + 4 by omega]; exact ph2b k)
  exact steps_congr trans (by poly_steps) h

/-- n = 3k+2: P (3k+2) → Q (4k+4), the start of an excursion. -/
theorem p2 (k : Nat) : steps (27 * k * k + 123 * k + 117) (P (3 * k + 2)) = some (Q (4 * k + 4)) := by
  have h := steps_seq trans (steps_seq trans (start (3 * k + 2)) (diter (3 * k + 2) 2 blank))
    (by rw [show 2 + 2 * (3 * k + 2) = 6 * k + 6 by omega]; exact ph2c k)
  exact steps_congr trans (by poly_steps) h

theorem init_P1 : steps 14 init = some (P 1) := by
  have h := blank_reaches trans (q := St.A) (n := 14) (c := ⟨[true, false, true, false, true], [], .A⟩)
    (by decide +kernel)
  simpa [FCfg.toCfg, P, app, rep] using h

theorem p0' (k n : Nat) (h : n = 3 * k) : steps (27 * k * k + 87 * k + 35) (P n) = some (P (4 * k + 2)) := by
  subst h; exact p0 k
theorem p1' (k n : Nat) (h : n = 3 * k + 1) : steps (27 * k * k + 105 * k + 62) (P n) = some (P (4 * k + 3)) := by
  subst h; exact p1 k

/-- From blank tape to the first excursion: P 1, 3, 6, 10, 15, 22, 31, 43, 59, then Q 80 at step 27,264. -/
theorem blank_Q80 : steps 27264 init = some (Q 80) := by
  have h1 := steps_seq trans init_P1 (p1' 0 1 rfl)          -- P 3
  have h2 := steps_seq trans h1 (p0' 1 3 rfl)               -- P 6
  have h3 := steps_seq trans h2 (p0' 2 6 rfl)               -- P 10
  have h4 := steps_seq trans h3 (p1' 3 10 rfl)              -- P 15
  have h5 := steps_seq trans h4 (p0' 5 15 rfl)              -- P 22
  have h6 := steps_seq trans h5 (p1' 7 22 rfl)              -- P 31
  have h7 := steps_seq trans h6 (p1' 10 31 rfl)             -- P 43
  have h8 := steps_seq trans h7 (p1' 14 43 rfl)             -- P 59
  have h9 := steps_seq trans h8 (p2 19)                     -- Q 80
  exact h9

end H107543
