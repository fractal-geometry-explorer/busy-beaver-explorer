import Wall

/-!
# The left sweep of a crossing

At a right turn inside a crossing the zone has one lone 1, `o`, between a near part `N` and a far part `O` (both
words in the 2-cell letters `a = 11`, `b = 10` of `Wall.lean`, nearest first).  Every letter ends in a 1, so `o`
followed by `O` is again `O` in letters, one cell further out: `o` is a one-cell buffer.  The left sweep takes the
running XOR over `N` as in `sweep2` and then:

* `cross_even`: the parity is even (D) at `o`.  D writes 1 over `o` and goes on over `O` in letters, to the left end.
* `cross_odd`: the parity is odd (C) at `o`.  C turns into E on `o`; E turns each `a` of `O` into the misaligned pair
  `1 0` (`erun`) and turns right at the first `b` of `O` (`eturn`), which becomes `a`.

So whether a crossing bounce reaches the left end is one bit, the parity of the `b`s in `N`, and where it turns
otherwise is the first `b` of `O`.  Observed in `py/turnshape.py`; proved here for every `N`, `O`, prefix, frozen word.
-/

namespace H75625

open TM

/-- A right turn inside a crossing: near zone `N`, a lone 1, far zone `O`, prefix `p`, E on `a`, frozen word `s`. -/
def Turn2 (N O : List Bool) (p : Bool) (s : List Bool) (R : Tape) : Config :=
  ⟨zl2 N (cons true (zl2 O (pre p))), app (lt2 false) (zl2 s R), .E⟩

/-- D on the lone 1 writes 1 and stays D. -/
theorem o_even (X R : Tape) : steps 1 (onL (cons true X) R (pst false)) = some (onL X (cons true R) (pst false)) := by
  rw [eta X]; rfl

/-- C on the lone 1 writes 1 and goes on in E. -/
theorem o_odd (X R : Tape) : steps 1 (onL (cons true X) R (pst true)) = some (onL X (cons true R) .E) := by
  rw [eta X]; rfl

/-- E over one `a`: `1 1` becomes `0 1` (read leftwards), E again. -/
theorem erun1 (X R : Tape) :
    steps 2 (onL (zl2 [false] X) R .E) = some (onL X (app [true, false] R) .E) := by
  rw [eta X]; cases h : X 0 <;> rfl

/-- E over `a^k`. -/
theorem erun (k : Nat) : ∀ (X R : Tape),
    steps (2 * k) (onL (zl2 (List.replicate k false) X) R .E) = some (onL X (rep k [true, false] R) .E) := by
  induction k with
  | zero => intro X R; rfl
  | succ k ih =>
    intro X R
    have h1 := erun1 (zl2 (List.replicate k false) X) R
    have h2 := ih X (app [true, false] R)
    have e : 2 * (k + 1) = 2 + 2 * k := by omega
    have e2 : rep k [true, false] (app [true, false] R) = rep (k + 1) [true, false] R := by
      rw [rep_app_comm]
    rw [e, ← e2]
    exact steps_seq trans h1 h2

/-- E on a `b` turns right: the `b` becomes `a` and F starts a right sweep. -/
theorem eturn (X R : Tape) :
    steps 1 (onL (zl2 [true] X) R .E) = some ⟨app [true, true] X, R, .F⟩ := rfl

/-- The first step and the sweep over `N`: the head is on the lone 1 in C (odd) or D (even). -/
theorem cross_near (N O : List Bool) (p : Bool) (s : List Bool) (R : Tape) :
    steps (1 + 2 * N.length) (Turn2 N O p s R) =
      some (onL (cons true (zl2 O (pre p))) (zl2 (sx true N).reverse (app (lt2 true) (zl2 s R))) (pst (par true N))) := by
  have h0 : steps 1 (Turn2 N O p s R) =
      some (onL (zl2 N (cons true (zl2 O (pre p)))) (app (lt2 true) (zl2 s R)) (pst true)) := rfl
  exact steps_seq trans h0 (sweep2 N _ true _)

/-- **Even parity at the lone 1**: the sweep goes through it and over `O` to the left end, as in a clean zone. -/
theorem cross_even (N O : List Bool) (p : Bool) (s : List Bool) (R : Tape) (h : par true N = false) :
    steps (1 + 2 * N.length + 1 + 2 * O.length) (Turn2 N O p s R) =
      some (onL (pre p) (zl2 (sx false O).reverse (cons true (zl2 (sx true N).reverse (app (lt2 true) (zl2 s R)))))
        (pst (par false O))) := by
  have h1 := cross_near N O p s R
  rw [h] at h1
  have h2 := o_even (zl2 O (pre p)) (zl2 (sx true N).reverse (app (lt2 true) (zl2 s R)))
  have h3 := sweep2 O (pre p) false (cons true (zl2 (sx true N).reverse (app (lt2 true) (zl2 s R))))
  exact steps_seq trans (steps_seq trans h1 h2) h3

/-- **Odd parity at the lone 1**: E turns the `a`s of `O` before its first `b` into `1 0` and turns right on that `b`,
which becomes `a`.  F then starts a right sweep over the misaligned pairs, the lone 1 and the sweep's output. -/
theorem cross_odd (N : List Bool) (k : Nat) (O' : List Bool) (p : Bool) (s : List Bool) (R : Tape)
    (h : par true N = true) :
    steps (1 + 2 * N.length + 1 + 2 * k + 1) (Turn2 N (List.replicate k false ++ true :: O') p s R) =
      some ⟨app [true, true] (zl2 O' (pre p)),
        rep k [true, false] (cons true (zl2 (sx true N).reverse (app (lt2 true) (zl2 s R)))), .F⟩ := by
  have h1 := cross_near N (List.replicate k false ++ true :: O') p s R
  rw [h] at h1
  have h2 := o_odd (zl2 (List.replicate k false ++ true :: O') (pre p))
    (zl2 (sx true N).reverse (app (lt2 true) (zl2 s R)))
  rw [zl2_append] at h1 h2
  have h3 := erun k (zl2 (true :: O') (pre p)) (cons true (zl2 (sx true N).reverse (app (lt2 true) (zl2 s R))))
  have h4 := eturn (zl2 O' (pre p))
    (rep k [true, false] (cons true (zl2 (sx true N).reverse (app (lt2 true) (zl2 s R)))))
  exact steps_seq trans (steps_seq trans (steps_seq trans h1 h2) h3) h4

end H75625
