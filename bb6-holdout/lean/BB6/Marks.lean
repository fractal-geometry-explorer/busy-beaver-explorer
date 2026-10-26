import BB6.Rows2

/-!
# Marks and positions

The mark model reads the tape as marks (gap `000`, marker `11`, wall `00`, block `111`) separated by stripes
`1010…`.  A stripe between two marks starts with the complement of the previous mark's last cell and ends with the
complement of the next mark's first cell, so its length is odd between marks of the same value and even otherwise.

`build prev pos ms` is the tape from cell `pos` on, when the cell before `pos` has value `prev` and the marks to the
right are `ms` (positions increasing, each at least `pos` away): a stripe to the next mark, the mark's cells, and so
on; blank after the last mark.  `roundStart ms` is a round start: the leftmost 1 at cell 0, the gap at cells 1–3 with
the head on cell 3 in state E, and the marks `ms` to the right.

The first theorem at this level is the first row of the round recurrence read off positions: a marker at
`p = 4k + 4` (d = p − 4 ≡ 0 mod 4 stripe cells after the gap) is met by k bounces and a swap, after which the marker
sits at 2k and the gap at 2k + 2, the marks beyond are untouched, and the head is on the new gap's last cell.
-/

namespace BB6

inductive MarkT where
  | G | M | W | B
  deriving DecidableEq, Repr

structure Mark where
  t : MarkT
  p : Nat
  deriving Repr

def mlen : MarkT → Nat
  | .G => 3 | .M => 2 | .W => 2 | .B => 3

def mcells : MarkT → List Bool
  | .G => [false, false, false] | .M => [true, true] | .W => [false, false] | .B => [true, true, true]

/-- The value of a mark's cells, which fixes the stripes around it. -/
def mval : MarkT → Bool
  | .G => false | .M => true | .W => false | .B => true

/-- `n` alternating cells starting with `b`. -/
def stripe : Bool → Nat → Tape → Tape
  | _, 0, s => s
  | b, n + 1, s => cons b (stripe (!b) n s)

@[simp] theorem stripe_zero (b : Bool) (s : Tape) : stripe b 0 s = s := rfl
@[simp] theorem stripe_succ (b : Bool) (n : Nat) (s : Tape) : stripe b (n + 1) s = cons b (stripe (!b) n s) := rfl

theorem stripe_two_add (b : Bool) (k n : Nat) (s : Tape) :
    stripe b (2 * k + n) s = rep k [b, !b] (stripe b n s) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : 2 * (k + 1) + n = (2 * k + n) + 1 + 1 := by omega
    rw [e, stripe_succ, stripe_succ, Bool.not_not, ih]
    rfl

theorem stripe_even (b : Bool) (k : Nat) (s : Tape) : stripe b (2 * k) s = rep k [b, !b] s := by
  have := stripe_two_add b k 0 s
  simpa using this

/-- The tape from cell `pos` on, with the marks `ms` and then a stripe up to the width `W` (blank from `W` on). -/
def build (prev : Bool) (pos : Nat) : List Mark → Nat → Tape
  | [], W => stripe (!prev) (W - pos) blank
  | m :: ms, W => stripe (!prev) (m.p - pos) (app (mcells m.t) (build (mval m.t) (m.p + mlen m.t) ms W))

/-- A round start: `0^∞ 1 0 0 E>0 ...` with the marks `ms` to the right of the gap at 1 and width `W`. -/
def roundStart (ms : List Mark) (W : Nat) : Cfg :=
  ⟨cons false (cons false (cons true blank)), cons false (build false 4 ms W), .E⟩

/-- First row of the round recurrence, at the level of positions: the gap at 1 meets a marker at 4k + 4 (4k stripe
cells apart), bounces k times and swaps.  The marker ends at 2k, the gap at 2k + 2 with the head on its last cell,
and everything to the right of the marker's old position is unchanged; 6k² + 24k + 21 steps. -/
theorem row_swap (k : Nat) (m' : Mark) (ms : List Mark) (W : Nat) (hnext : 4 * k + 6 < m'.p) :
    steps (6 * k * k + 24 * k + 21) (roundStart (⟨.M, 4 * k + 4⟩ :: m' :: ms) W)
      = some ⟨cons false (cons false (cons true (cons true (rep k [false, true] blank)))),
              cons false (build false (2 * k + 5) (m' :: ms) W), .E⟩ := by
  obtain ⟨n, hn⟩ : ∃ n, m'.p - (4 * k + 6) = n + 1 := ⟨m'.p - (4 * k + 6) - 1, by omega⟩
  have hstart : roundStart (⟨.M, 4 * k + 4⟩ :: m' :: ms) W
      = ⟨cons false (cons false (cons true blank)),
         cons false (stripe true (4 * k) (cons true (cons true (stripe false (m'.p - (4 * k + 6))
           (app (mcells m'.t) (build (mval m'.t) (m'.p + mlen m'.t) ms W)))))), .E⟩ := rfl
  have hend : build false (2 * k + 5) (m' :: ms) W
      = stripe true (m'.p - (2 * k + 5)) (app (mcells m'.t) (build (mval m'.t) (m'.p + mlen m'.t) ms W)) := rfl
  have e₁ : 4 * k = 2 * (2 * k) := by omega
  have e₂ : m'.p - (2 * k + 5) = 2 * (k + 1) + n := by omega
  conv at hstart => rhs; rw [hn, e₁, stripe_even, stripe_succ, Bool.not_false, Bool.not_true]
  rw [e₂, stripe_two_add, Bool.not_true] at hend
  rw [hstart, hend, ← gap_marker_swap_steps]
  exact gap_marker_swap k blank _

/-- The same row when the marker met is the end marker (at W − 2 = 4k + 4): afterwards the gap at 2k + 2 has only
a stripe of 2k + 1 cells to its right, up to the unchanged width W. -/
theorem row_swap_end (k : Nat) :
    steps (6 * k * k + 24 * k + 21) (roundStart [⟨.M, 4 * k + 4⟩] (4 * k + 6))
      = some ⟨cons false (cons false (cons true (cons true (rep k [false, true] blank)))),
              cons false (build false (2 * k + 5) [] (4 * k + 6)), .E⟩ := by
  have hstart : roundStart [⟨.M, 4 * k + 4⟩] (4 * k + 6)
      = ⟨cons false (cons false (cons true blank)),
         cons false (stripe true (4 * k) (cons true (cons true (stripe false (4 * k + 6 - (4 * k + 6)) blank)))), .E⟩ := rfl
  have hend : build false (2 * k + 5) [] (4 * k + 6) = stripe true (4 * k + 6 - (2 * k + 5)) blank := rfl
  have e₀ : 4 * k + 6 - (4 * k + 6) = 0 := by omega
  have e₁ : 4 * k = 2 * (2 * k) := by omega
  have e₂ : 4 * k + 6 - (2 * k + 5) = 2 * k + 1 := by omega
  conv at hstart => rhs; rw [e₀, stripe_zero, e₁, stripe_even, Bool.not_true]
  rw [e₂, stripe_two_add, Bool.not_true, stripe_succ, Bool.not_true, stripe_zero] at hend
  rw [hstart, hend, ← gap_marker_swap_steps]
  have h : steps (bounceSteps k 0 + 21)
      ⟨cons false (cons false (cons true blank)), cons false (rep (2 * k) [true, false] (cons true (cons true (cons false blank)))), .E⟩
      = some ⟨cons false (cons false (cons true (cons true (rep k [false, true] blank)))), cons false (rep (k + 1) [true, false] blank), .E⟩ :=
    gap_marker_swap k blank blank
  rw [cons_false_blank, ← rep_cons2 k true false blank, cons_false_blank] at h
  exact h

/-- Second row: the gap at 1 meets a marker at 4k + 6 (4k + 2 stripe cells apart), bounces k times and merges.
The packet `1 1` under the head (state A) sits at 2k, a wall `0 0` at 2k + 5, and the marks beyond are unchanged;
6k² + 30k + 31 steps. -/
theorem row_merge (k : Nat) (m' : Mark) (ms : List Mark) (W : Nat) (hnext : 4 * k + 8 < m'.p) :
    steps (6 * k * k + 30 * k + 31) (roundStart (⟨.M, 4 * k + 6⟩ :: m' :: ms) W)
      = some ⟨rep k [false, true] blank,
              cons true (cons true (cons true (cons false (cons true (cons false (cons false
                (build false (2 * k + 7) (m' :: ms) W))))))), .A⟩ := by
  obtain ⟨n, hn⟩ : ∃ n, m'.p - (4 * k + 8) = n + 1 := ⟨m'.p - (4 * k + 8) - 1, by omega⟩
  have hstart : roundStart (⟨.M, 4 * k + 6⟩ :: m' :: ms) W
      = ⟨cons false (cons false (cons true blank)),
         cons false (stripe true (4 * k + 2) (cons true (cons true (stripe false (m'.p - (4 * k + 8))
           (app (mcells m'.t) (build (mval m'.t) (m'.p + mlen m'.t) ms W)))))), .E⟩ := rfl
  have hend : build false (2 * k + 7) (m' :: ms) W
      = stripe true (m'.p - (2 * k + 7)) (app (mcells m'.t) (build (mval m'.t) (m'.p + mlen m'.t) ms W)) := rfl
  have e₁ : 4 * k + 2 = 2 * (2 * k + 1) := by omega
  have e₂ : m'.p - (2 * k + 7) = 2 * (k + 1) + n := by omega
  conv at hstart => rhs; rw [hn, e₁, stripe_even, stripe_succ, Bool.not_false, Bool.not_true]
  rw [e₂, stripe_two_add, Bool.not_true] at hend
  rw [hstart, hend, ← gap_marker_merge_steps]
  exact gap_marker_merge k blank _

end BB6
