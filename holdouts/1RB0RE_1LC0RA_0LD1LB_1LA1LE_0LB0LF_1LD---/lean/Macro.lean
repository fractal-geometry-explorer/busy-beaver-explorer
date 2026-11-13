import Rules

/-!
# 1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---: the phase map

Hand-written; the rules it uses (`round`, `zero`, `one`, `restart`, `start`) are proved in `Rules.lean`.

`T x m R` is the tape `1 1 1 0 (10)^x 1^m R` and `S m` the configuration `0^∞ A> 1 1 1 0 10 1^m 0^∞`
(`T 1 m blank` in state A at the left end). One phase of the machine:

* `S (3j)     →  S (10j + 12)`
* `S (3j + 1) →  S (10j + 14)`
* `S (3j + 2)`: not covered (the leftover pair of 1s leaves a remnant on the tape; see README).

From blank tape the run reaches `S 12` (75 steps) and then, by the map, `S 52, S 184, ..., S 31957652`; the last one
is the first value ≡ 2 (mod 3), so the run does not halt before it.
-/

namespace H145615

open TM

/-- `1 1 1 0 (10)^x 1^m R`. -/
def T (x m : Nat) (R : Tape) : Tape :=
  cons true (cons true (cons true (cons false (rep x [true, false] (rep m [true] R)))))

/-- `S m`: the start of a phase. -/
def S (m : Nat) : Config := ⟨blank, T 1 m blank, .A⟩

theorem T_add5 (x m : Nat) (R : Tape) :
    T (x + 5) m R = cons true (cons true (cons true (cons false (cons true (cons false (cons true (cons false
      (cons true (cons false (cons true (cons false (rep x [true, false] (cons true (cons false
      (rep m [true] R))))))))))))))) := by
  simp only [T]
  rw [show x + 5 = 4 + (x + 1) by omega, rep_add, ← rep_app_comm x]
  rfl

theorem round' (x m : Nat) (R : Tape) :
    steps (6 * x + 51) ⟨blank, T x (m + 3) R, .A⟩ = some ⟨blank, T (x + 5) m R, .A⟩ := by
  rw [T_add5]; exact round m x R

/-- Steps of `j` rounds starting from `x` (in closed form `j(6x+51) + 15j(j-1)`). -/
def roundSteps : Nat → Nat → Nat
  | 0, _ => 0
  | j + 1, x => (6 * x + 51) + roundSteps j (x + 5)

theorem rounds (j : Nat) : ∀ (x m : Nat) (R : Tape),
    steps (roundSteps j x) ⟨blank, T x (m + 3 * j) R, .A⟩ = some ⟨blank, T (x + 5 * j) m R, .A⟩ := by
  induction j with
  | zero => intro x m R; rfl
  | succ j ih =>
    intro x m R
    have h1 := round' x (m + 3 * j) R
    rw [show m + 3 * j + 3 = m + 3 * (j + 1) by omega] at h1
    have h2 := ih (x + 5) m R
    rw [show x + 5 + 5 * j = x + 5 * (j + 1) by omega] at h2
    exact steps_seq trans h1 h2

theorem rep_tt (y : Nat) (s : Tape) : rep y [true, true] s = rep (2 * y) [true] s := by
  induction y with
  | zero => rfl
  | succ y ih => rw [show 2 * (y + 1) = 2 * y + 1 + 1 by omega, rep_succ, ih]; rfl

theorem ones_cons (n : Nat) (s : Tape) : cons true (rep n [true] s) = rep (n + 1) [true] s := rfl

/-- `S (3j) → S (10j + 12)`. -/
theorem phase0 (j : Nat) : ∃ n, steps n (S (3 * j)) = some (S (10 * j + 12)) := by
  have h1 := rounds j 1 0 blank
  rw [show 0 + 3 * j = 3 * j by omega] at h1
  have h2 := zero (1 + 5 * j)
  have e2 : T (1 + 5 * j) 0 blank = cons true (cons true (cons true (cons false
      (rep (1 + 5 * j) [true, false] blank)))) := rfl
  rw [← e2] at h2
  have h3 := restart (rep (2 * (5 * j + 6)) [true] blank)
  have e3 : cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true
      (cons true (cons true (rep (1 + 5 * j) [true, true] (cons true blank)))))))))))) =
      cons true (cons true (rep (2 * (5 * j + 6)) [true] blank)) := by
    rw [rep_tt, show cons true blank = rep 1 [true] blank from rfl, ← rep_add]
    simp only [ones_cons]
    congr 2; omega
  rw [e3] at h2
  have e4 : cons true (cons true (cons true (cons false (cons true (cons false
      (rep (2 * (5 * j + 6)) [true] blank)))))) = T 1 (10 * j + 12) blank := by
    simp only [T]; rw [show 2 * (5 * j + 6) = 10 * j + 12 by omega]; rfl
  rw [e4] at h3
  exact ⟨_, steps_seq trans (steps_seq trans h1 h2) h3⟩

/-- `S (3j + 1) → S (10j + 14)`. -/
theorem phase1 (j : Nat) : ∃ n, steps n (S (3 * j + 1)) = some (S (10 * j + 14)) := by
  have h1 := rounds j 1 1 blank
  rw [show 1 + 3 * j = 3 * j + 1 by omega] at h1
  have h2 := one (1 + 5 * j)
  have e2 : T (1 + 5 * j) 1 blank = cons true (cons true (cons true (cons false
      (rep (1 + 5 * j) [true, false] (cons true blank))))) := rfl
  rw [← e2] at h2
  have h3 := restart (rep (2 * (5 * j + 7)) [true] blank)
  have e3 : cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true (cons true
      (cons true (cons true (cons true (rep (1 + 5 * j) [true, true] (cons true (cons true blank)))))))))))))) =
      cons true (cons true (rep (2 * (5 * j + 7)) [true] blank)) := by
    rw [rep_tt, show cons true (cons true blank) = rep 2 [true] blank from rfl, ← rep_add]
    simp only [ones_cons]
    congr 2; omega
  rw [e3] at h2
  have e4 : cons true (cons true (cons true (cons false (cons true (cons false
      (rep (2 * (5 * j + 7)) [true] blank)))))) = T 1 (10 * j + 14) blank := by
    simp only [T]; rw [show 2 * (5 * j + 7) = 10 * j + 14 by omega]; rfl
  rw [e4] at h3
  exact ⟨_, steps_seq trans (steps_seq trans h1 h2) h3⟩

theorem reach_trans {c c' c'' : Config} (h1 : ∃ n, steps n c = some c') (h2 : ∃ n, steps n c' = some c'') :
    ∃ n, steps n c = some c'' := by
  obtain ⟨a, ha⟩ := h1; obtain ⟨b, hb⟩ := h2; exact ⟨a + b, steps_seq trans ha hb⟩

theorem p0 (j m m' : Nat) (h : m = 3 * j) (h' : m' = 10 * j + 12) : ∃ n, steps n (S m) = some (S m') := by
  subst h; subst h'; exact phase0 j

theorem p1 (j m m' : Nat) (h : m = 3 * j + 1) (h' : m' = 10 * j + 14) : ∃ n, steps n (S m) = some (S m') := by
  subst h; subst h'; exact phase1 j

theorem init_S12 : steps 75 init = some (S 12) := start

/-- From blank tape the machine reaches `S 31957652` (about 10^14 steps), the first phase start whose count of 1s
is ≡ 2 (mod 3); in particular it does not halt before. -/
theorem reaches_S31957652 : ∃ n, steps n init = some (S 31957652) := by
  refine reach_trans ⟨75, init_S12⟩ ?_
  refine reach_trans (p0 4 _ 52 rfl rfl) ?_
  refine reach_trans (p1 17 _ 184 rfl rfl) ?_
  refine reach_trans (p1 61 _ 624 rfl rfl) ?_
  refine reach_trans (p0 208 _ 2092 rfl rfl) ?_
  refine reach_trans (p1 697 _ 6984 rfl rfl) ?_
  refine reach_trans (p0 2328 _ 23292 rfl rfl) ?_
  refine reach_trans (p0 7764 _ 77652 rfl rfl) ?_
  refine reach_trans (p0 25884 _ 258852 rfl rfl) ?_
  refine reach_trans (p0 86284 _ 862852 rfl rfl) ?_
  refine reach_trans (p1 287617 _ 2876184 rfl rfl) ?_
  refine reach_trans (p0 958728 _ 9587292 rfl rfl) ?_
  exact p0 3195764 _ 31957652 rfl rfl

end H145615
