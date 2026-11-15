import Machine

/-!
# The left counter of 1RB1RF_1LC0LB_1RE1LD_1RE0LB_1RA0RE_---0RC, for every word list

Left of a fixed cell (the *seam*) the tape is a row of 3-cell words `x 0 1`, one bit `x` each (`dw`, nearest word
first).  Whenever the head steps onto the last cell of the nearest word in state B or D, it comes back to the cell it
came from, and the row has changed in one way only (`inc_zero`, `inc_ones`):

* the nearest word with bit 0 gets bit 1 (if there is none: a new word with bit 0 is put on at the far end, on
  blank tape), and
* the `j` words in front of it, which all had bit 1, get the bits 1, 0, 1, 0, ... counted from that word towards the
  head (`alt`); with a new word at the far end they get 0, 1, 0, 1, ...;
* the head comes back in state A if the number `j` of words it crossed is even and in state E if it is odd (the
  other way round after a new word): `fl`.

The steady visits of `Visit.lean` are the special case where every second word (the odd positions) has bit 1 and the
words between are the binary digits of V: then the nearest 0 is at an even position, the words below it become
1 0 1 0 ..., that is: the fixed words stay 1 and the digits below become 0: V + 1, and the head comes back in state
A.  The four theorems at the end are the four ways the row can be full, one for each *phase* of the counter:

| phase | row (far end first) | full: becomes | comes back in |
|---|---|---|---|
| A  | digits at even positions, top digit 1 | B, all digits 0 (`ovf_A`) | A |
| B  | the same under a lone word 0 | A', digits at **odd** positions, 0...01 (`ovf_B`) | **E** |
| A' | digits at odd positions, top digit 1 | B', all digits 0 (`ovf_A'`) | E |
| B' | the same under a lone word 0 | A, one digit more, 0...01 (`ovf_B'`) | **A** |

(`ovf_A'` and `ovf_B'` are stated for at least one digit.)

Kernel only; no evaluation of runs.
-/

namespace H154101

open TM

/-- A word `x 0 1` of the left counter, nearest cell first. -/
abbrev Wd (x : Bool) : List Bool := [true, false, x]

/-- The words `xs` (nearest first) in front of `s`. -/
def dw : List Bool → Tape → Tape
  | [], s => s
  | x :: xs, s => app (Wd x) (dw xs s)

@[simp] theorem dw_nil (s : Tape) : dw [] s = s := rfl
@[simp] theorem dw_cons (x : Bool) (xs : List Bool) (s : Tape) : dw (x :: xs) s = app (Wd x) (dw xs s) := rfl

theorem dw_append (xs ys : List Bool) (s : Tape) : dw (xs ++ ys) s = dw xs (dw ys s) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, dw_cons, ih]

/-- The head stands on the first cell of the left tape `X` (it has just stepped off the cell to the right). -/
def onL (X R : Tape) (q : St) : Config := ⟨tail X, cons (X 0) R, q⟩

/-- A or E. -/
def ae (a : Bool) : St := if a then .A else .E

/-- The bits written on the way back over `k` words when the first of them (the farthest) gets `a`: nearest first,
alternating. -/
def alt : Bool → Nat → List Bool
  | _, 0 => []
  | a, k + 1 => alt (!a) k ++ [a]

/-- The state after the way back over `k` words (`true` is A, `false` is E). -/
def fl : Bool → Nat → Bool
  | a, 0 => a
  | a, k + 1 => fl (!a) k

/-- Crossing one word with bit 1 to the left, in state B or D: it is left behind as `1 1 0`. -/
theorem pass_one (T R : Tape) (q : St) (hq : q = .B ∨ q = .D) :
    steps 3 (onL (app (Wd true) T) R q) = some (onL T (app [true, true, false] R) .D) := by
  rcases hq with rfl | rfl <;> rfl

/-- Crossing `j` words with bit 1 to the left. -/
theorem pass_ones (j : Nat) (T R : Tape) (q : St) (hq : q = .B ∨ q = .D) :
    ∃ q', (q' = .B ∨ q' = .D) ∧ (0 < j → q' = .D) ∧
      steps (3 * j) (onL (dw (List.replicate j true) T) R q) = some (onL T (rep j [true, true, false] R) q') := by
  induction j generalizing R q with
  | zero => exact ⟨q, hq, fun h => absurd h (Nat.lt_irrefl 0), rfl⟩
  | succ j ih =>
    obtain ⟨q', hq', _, h⟩ := ih (app [true, true, false] R) .D (Or.inr rfl)
    have h1 := pass_one (dw (List.replicate j true) T) R q hq
    rw [rep_app_comm] at h
    refine ⟨q', hq', fun _ => ?_, ?_⟩
    · cases j with
      | zero => simp only [Nat.mul_zero, steps_zero, Option.some.injEq] at h; cases h; rfl
      | succ j => rename_i hD _; exact hD (Nat.succ_pos j)
    · have := steps_seq trans h1 h
      exact steps_congr trans (by omega) this

/-- The turn at a word with bit 0: it gets bit 1 and the head goes back in state A. -/
theorem turn_zero (T R : Tape) (q : St) (hq : q = .B ∨ q = .D) :
    steps 5 (onL (app (Wd false) T) R q) = some ⟨app (Wd true) T, R, .A⟩ := by
  rcases hq with rfl | rfl <;> rfl

/-- The turn on blank tape, in state D: a new word with bit 0, and the head goes back in state E. -/
theorem turn_blank (R : Tape) : steps 1 (onL blank R .D) = some ⟨dw [false] blank, R, .E⟩ := by
  have e : dw [false] blank = cons true blank := by
    simp only [dw_cons, dw_nil, app_cons, app_nil, cons_false_blank]
  rw [e]; rfl

/-- The way back over one word `1 1 0`: in state A it becomes `1 0 1` (bit 1) and the state E, in state E it becomes
`0 0 1` (bit 0) and the state A. -/
theorem back_one (a : Bool) (L R : Tape) :
    steps 3 ⟨L, app [true, true, false] R, ae a⟩ = some ⟨app (Wd a) L, R, ae (!a)⟩ := by
  cases a <;> rfl

/-- The way back over `k` words. -/
theorem back_words (k : Nat) (a : Bool) (L R : Tape) :
    steps (3 * k) ⟨L, rep k [true, true, false] R, ae a⟩ = some ⟨dw (alt a k) L, R, ae (fl a k)⟩ := by
  induction k generalizing a L with
  | zero => rfl
  | succ k ih =>
    have h1 := back_one a L (rep k [true, true, false] R)
    have h2 := ih (!a) (app (Wd a) L)
    have e : dw (alt (!a) k) (app (Wd a) L) = dw (alt a (k + 1)) L := by
      simp only [alt, dw_append, dw_cons, dw_nil]
    rw [e] at h2
    exact steps_congr trans (by omega) (steps_seq trans h1 h2)

/-- **One increment, the nearest 0 found**: `j` words with bit 1, then a word with bit 0, then anything. -/
theorem inc_zero (j : Nat) (rest : List Bool) (T R : Tape) (q : St) (hq : q = .B ∨ q = .D) :
    steps (6 * j + 5) (onL (dw (List.replicate j true ++ false :: rest) T) R q) =
      some ⟨dw (alt true j ++ true :: rest) T, R, ae (fl true j)⟩ := by
  obtain ⟨q', hq', _, h1⟩ := pass_ones j (dw (false :: rest) T) R q hq
  have h2 := turn_zero (dw rest T) (rep j [true, true, false] R) q' hq'
  have h3 := back_words j true (app (Wd true) (dw rest T)) R
  rw [dw_append]
  have e : dw (alt true j ++ true :: rest) T = dw (alt true j) (app (Wd true) (dw rest T)) := by
    rw [dw_append]; rfl
  rw [e]
  exact steps_congr trans (by omega) (steps_seq trans h1 (steps_seq trans h2 h3))

/-- **One increment of a full row** (`j + 1` words, all with bit 1, on blank tape): a new word with bit 0. -/
theorem inc_ones (j : Nat) (R : Tape) (q : St) (hq : q = .B ∨ q = .D) :
    steps (6 * (j + 1) + 1) (onL (dw (List.replicate (j + 1) true) blank) R q) =
      some ⟨dw (alt false (j + 1) ++ [false]) blank, R, ae (fl false (j + 1))⟩ := by
  obtain ⟨q', _, hD, h1⟩ := pass_ones (j + 1) blank R q hq
  have hq' : q' = .D := hD (Nat.succ_pos j)
  subst hq'
  have h2 := turn_blank (rep (j + 1) [true, true, false] R)
  have h3 := back_words (j + 1) false (dw [false] blank) R
  rw [dw_append]
  exact steps_congr trans (by omega) (steps_seq trans h1 (steps_seq trans h2 h3))

/-! ## The four phases -/

/-- The row with the fixed word 1 at every second place: `1, d₀, 1, d₁, ...` (nearest first). -/
def pr : List Bool → List Bool
  | [] => []
  | d :: ds => true :: d :: pr ds

theorem fl_two (a : Bool) (k : Nat) : fl a (k + 2) = fl a k := by
  simp only [fl, Bool.not_not]

theorem fl_even (a : Bool) (n : Nat) : fl a (2 * n) = a := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 2 * (n + 1) = 2 * n + 2 by omega, fl_two, ih]

theorem fl_odd (a : Bool) (n : Nat) : fl a (2 * n + 1) = !a := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, fl_two, ih]

theorem pr_ones (n : Nat) : pr (List.replicate n true) = List.replicate (2 * n) true := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]; simp only [List.replicate_succ, pr, ih]

theorem alt_two (a : Bool) (k : Nat) : alt a (k + 2) = alt a k ++ [!a, a] := by
  simp only [alt, Bool.not_not, List.append_assoc, List.cons_append, List.nil_append]

/-- `alt false (2n)` is `1 0 1 0 ... 1 0`: the fixed words 1, the digits 0. -/
theorem alt_false_even (n : Nat) : alt false (2 * n) = pr (List.replicate n false) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, alt_two, ih]
    clear ih
    induction n with
    | zero => rfl
    | succ n ih => simp only [List.replicate_succ, pr, List.cons_append, ih]

/-- `alt true (2n)` is `0 1 0 1 ... 0 1`. -/
theorem alt_true_even (n : Nat) : alt true (2 * n) = (List.replicate n [false, true]).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, alt_two, ih]
    clear ih
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [List.replicate_succ, List.flatten_cons, List.cons_append, List.nil_append] at ih ⊢
      rw [ih]

theorem flat_false (n : Nat) (l : List Bool) :
    (List.replicate n [false, true]).flatten ++ false :: l = false :: pr (List.replicate n false) ++ l := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons, List.cons_append, List.nil_append, pr] at ih ⊢
    rw [ih]

theorem flat_true (n : Nat) :
    (List.replicate (n + 1) [false, true]).flatten ++ [true] = false :: pr (List.replicate n false ++ [true]) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, List.append_assoc, ih]
    rfl

/-- Phase A is full (`2n + 1` words 1: the digits and the fixed words): phase B with all digits 0; back in A. -/
theorem ovf_A (n : Nat) (R : Tape) (q : St) (hq : q = .B ∨ q = .D) :
    steps (6 * (2 * n + 1) + 1) (onL (dw (true :: pr (List.replicate n true)) blank) R q) =
      some ⟨dw (false :: pr (List.replicate n false) ++ [false]) blank, R, .A⟩ := by
  have h := inc_ones (2 * n) R q hq
  rw [pr_ones]
  have e1 : alt false (2 * n + 1) ++ [false] = false :: pr (List.replicate n false) ++ [false] := by
    have : alt false (2 * n + 1) = alt true (2 * n) ++ [false] := rfl
    rw [this, alt_true_even, List.append_assoc]
    exact flat_false n [false]
  rw [e1, fl_odd] at h
  exact h

/-- Phase B is full (the digits and the fixed words 1 under the lone word 0): the lone word becomes 1, the fixed
words become 0 and the digits 1, so the digits are now at the odd places: phase A' with digits 0...01; back in **E**. -/
theorem ovf_B (n : Nat) (R : Tape) (q : St) (hq : q = .B ∨ q = .D) :
    steps (6 * (2 * n + 1) + 5) (onL (dw (true :: pr (List.replicate n true) ++ [false]) blank) R q) =
      some ⟨dw (pr (List.replicate n false ++ [true])) blank, R, .E⟩ := by
  have h := inc_zero (2 * n + 1) [] blank R q hq
  rw [pr_ones]
  have e0 : true :: List.replicate (2 * n) true ++ [false] = List.replicate (2 * n + 1) true ++ [false] := rfl
  rw [e0]
  have e1 : alt true (2 * n + 1) ++ [true] = pr (List.replicate n false ++ [true]) := by
    have : alt true (2 * n + 1) = alt false (2 * n) ++ [true] := rfl
    rw [this, alt_false_even]
    clear this h e0
    induction n with
    | zero => rfl
    | succ n ih => simp only [List.replicate_succ, pr, List.cons_append] at ih ⊢; rw [ih]
  rw [e1, fl_odd] at h
  exact h

/-- Phase A' is full (`2n` words 1, `n ≥ 1`): phase B' with all digits 0; back in E. -/
theorem ovf_A' (n : Nat) (R : Tape) (q : St) (hq : q = .B ∨ q = .D) :
    steps (6 * (2 * n + 2) + 1) (onL (dw (pr (List.replicate (n + 1) true)) blank) R q) =
      some ⟨dw (pr (List.replicate (n + 1) false) ++ [false]) blank, R, .E⟩ := by
  have h := inc_ones (2 * n + 1) R q hq
  rw [pr_ones]
  rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega, alt_false_even, fl_even] at h
  exact steps_congr trans (by omega) h

/-- Phase B' is full: the lone word becomes 1, the digits become the fixed words and the fixed words the digits
0...01, one digit more than before: phase A again; back in **A**. -/
theorem ovf_B' (n : Nat) (R : Tape) (q : St) (hq : q = .B ∨ q = .D) :
    steps (6 * (2 * (n + 1)) + 5) (onL (dw (pr (List.replicate (n + 1) true) ++ [false]) blank) R q) =
      some ⟨dw (false :: pr (List.replicate n false ++ [true])) blank, R, .A⟩ := by
  have h := inc_zero (2 * (n + 1)) [] blank R q hq
  rw [pr_ones]
  rw [alt_true_even, flat_true, fl_even] at h
  exact h

end H154101
