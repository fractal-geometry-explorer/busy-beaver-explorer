import Rules

/-!
# The visit configurations of 1RB1RF_1LC0LB_1RE1LD_1RE0LB_1RA0RE_---0RC

A *visit* is a configuration with the head in state C on the blank cell right of the tape.  At a steady visit the
tape is, left to right,

    0^inf  [1]  U(b_top) ... U(b_1)  b_0 0 1   M(t)   I(i)   (1011)^m 1 0   C>0

with `U(b) = b 0 1 1 0 1`.  Here the left stream (nearest cell first) is written with

* `vis m X`: the block `(1011)^m 1 0` and the head, `X` the tape left of the block;
* `Xv pre b0 ds t i0 i1 i2`: `I(i)`, `M(t)`, the short digit `b0 0 1`, the digits `ds = [b_1, ..., b_top]` (low
  first, each `U(b)`), and `pre`: blank tape (phase A) or a lone 1 in front of blank tape (phase B).

`visit` glues a middle part (proved in `Counter.lean`/`Overflow.lean`) between the two block crossings of
`Rules.lean`.
-/

namespace H154101

open TM

/-- One digit `U(b) = b 0 1 1 0 1`, nearest cell first. -/
abbrev Ur (b : Bool) : List Bool := [true, false, true, true, false, b]

/-- The digits `ds` (low first) in front of `s`. -/
def digs : List Bool → Tape → Tape
  | [], s => s
  | b :: bs, s => app (Ur b) (digs bs s)

@[simp] theorem digs_nil (s : Tape) : digs [] s = s := rfl
@[simp] theorem digs_cons (b : Bool) (bs : List Bool) (s : Tape) : digs (b :: bs) s = app (Ur b) (digs bs s) := rfl

theorem digs_rep (b : Bool) (n : Nat) (l : List Bool) (s : Tape) :
    digs (List.replicate n b ++ l) s = rep n (Ur b) (digs l s) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, digs_cons, ih, rep_succ]

theorem digs_rep_nil (b : Bool) (n : Nat) (s : Tape) : digs (List.replicate n b) s = rep n (Ur b) s := by
  simpa using digs_rep b n [] s

/-- `M(t)`, nearest cell first (the cell `t` is cell 11 of M read left to right). -/
abbrev Mrev (t : Bool) : List Bool :=
  [true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false,
   true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, t, true, false, true,
   true, true, false, true, true, false, true, true]

/-- `I(i) = U(i2) U(i1) i0 0 1`, nearest cell first. -/
abbrev Irev (i0 i1 i2 : Bool) : List Bool := [true, false, i0] ++ Ur i1 ++ Ur i2

/-- The tape left of the block at a steady visit. -/
def Xv (pre : Tape) (b0 : Bool) (ds : List Bool) (t i0 i1 i2 : Bool) : Tape :=
  app (Irev i0 i1 i2) (app (Mrev t) (cons true (cons false (cons b0 (digs ds pre)))))

/-- A visit: the block `(1011)^m 1 0` and the head in state C on the blank cell after it. -/
def vis (m : Nat) (X : Tape) : Config := ⟨cons false (cons true (rep m [true, true, false, true] X)), blank, .C⟩

/-- The phase B lead: a lone 1 in front of blank tape. -/
abbrev preB : Tape := cons true blank

/-- One visit: `back` across the block, a middle part `h` that turns around left of the block, `forth`. -/
theorem visit (m s : Nat) (X Y : Tape)
    (h : ∀ R : Tape, steps s ⟨X, cons true R, .C⟩ = some ⟨cons true Y, R, .F⟩) :
    steps (8 * m + 12 + s + 1) (vis m X) = some (vis (m + 1) Y) := by
  have h1 := back m X
  have e1 : cons true (cons true (cons false (cons false (rep m [true, true, false, false]
      (cons true (cons true blank)))))) = cons true (rep m [true, false, false, true]
      (cons true (cons false (cons false (cons true (cons true blank)))))) := by
    have := rep_rotate m [true, false, false] [true, true, false, false] [true, false, false, true] rfl
      (cons true (cons true blank))
    simp only [app_cons, app_nil] at this
    rw [this]
  rw [e1] at h1
  have h2 := h (rep m [true, false, false, true] (cons true (cons false (cons false (cons true (cons true blank))))))
  have h3 := forth m Y
  have e3 : cons false (cons true (cons true (cons true (cons false (rep m [true, true, true, false]
      (cons true Y)))))) = cons false (cons true (rep (m + 1) [true, true, false, true] Y)) := by
    have := rep_rotate m [true, true, false] [true, true, true, false] [true, true, false, true] rfl (cons true Y)
    simp only [app_cons, app_nil] at this
    rw [this, ← rep_app_comm]
    rfl
  rw [e3] at h3
  have := steps_seq trans (steps_seq trans h1 h2) h3
  exact steps_congr trans (by omega) this

/-- The steady visits: phase A (`pre` blank) or B (`pre` a lone 1), at least 6 digits above `b_0`, and the block at
least as long as the counter is wide. -/
def Steady (c : Config) : Prop :=
  ∃ (pre : Tape) (b0 : Bool) (ds : List Bool) (t i0 i1 i2 : Bool) (m : Nat),
    (pre = blank ∨ pre = preB) ∧ 6 ≤ ds.length ∧ ds.length + 1 ≤ m ∧ c = vis m (Xv pre b0 ds t i0 i1 i2)

theorem steady_mk {pre : Tape} {b0 : Bool} {ds : List Bool} {t i0 i1 i2 : Bool} {m : Nat}
    (hp : pre = blank ∨ pre = preB) (hl : 6 ≤ ds.length) (hm : ds.length + 1 ≤ m) :
    Steady (vis m (Xv pre b0 ds t i0 i1 i2)) :=
  ⟨pre, b0, ds, t, i0, i1, i2, m, hp, hl, hm, rfl⟩

/-- A deep visit carries out of the five low digits: `lo + c >= 32` (c = 7 for t = 0, 10 for t = 1, the rest of
39 or 42 going to digit 5). -/
def lowCarry (t b0 b1 b2 b3 b4 : Bool) : Bool :=
  decide (32 ≤ b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat + 16 * b4.toNat + (if t then 10 else 7))

/-- A *B-overflow*: a deep visit in phase B whose carry runs through all the digits to the lone 1 in front (all
digits above the low five are 1, above digit 5 when the low digits carry).  What follows is the transient that
`Steps.lean` does not cover. -/
def BStart (c : Config) : Prop :=
  ∃ (b0 b1 b2 b3 b4 : Bool) (hi : List Bool) (t : Bool) (m : Nat),
    c = vis m (Xv preB b0 (b1 :: b2 :: b3 :: b4 :: hi) t true true true) ∧
    cond (lowCarry t b0 b1 b2 b3 b4) (∃ b5 h', hi = b5 :: h' ∧ h' = List.replicate h'.length true)
      (hi = List.replicate hi.length true)

/-- Every list of bits is some 1s and then a 0, or all 1s. -/
theorem split_ones (l : List Bool) :
    (∃ j rest, l = List.replicate j true ++ false :: rest) ∨ l = List.replicate l.length true := by
  induction l with
  | nil => right; rfl
  | cons b l ih =>
    cases b with
    | false => left; exact ⟨0, l, rfl⟩
    | true =>
      rcases ih with ⟨j, rest, h⟩ | h
      · left; exact ⟨j + 1, rest, by rw [h]; rfl⟩
      · right; simp only [List.length_cons, List.replicate_succ]; rw [← h]

end H154101
