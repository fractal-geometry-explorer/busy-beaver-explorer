import Trip

/-!
# Token mode: a lone 1 is read as if its holes were filled

`Trip.lean` covers round trips with no lone 1 before the first `00`. This file covers the rest. A lone 1 (`1 0`
after a 0) sends the right sweep into token mode: it crosses the `110` words that follow (each becomes `000`), and
the first `111` throws it back into the ordinary zigzag one cell late.

* `rtok`: over `1 0 (110)^j 1^(k+3) 0` the right sweep leaves **exactly the same cells and state** as over the single
  run `1^(3j+k+5) 0`, the tape with the holes of the lone 1 and of the `110` words filled in.
* So the left sweep cannot tell the difference, and `trip_tok`: a round trip over any sequence of pieces (ordinary
  runs and token chains, `Pc`) is `ca3` of the filled tape. Filling the holes at `i+1, i+4, ..., i+1+3j` changes the
  automaton's output only at `i-2` and `i+1+3j` (the other changes cancel in pairs), which is the defect's jump of
  `Hop.lean`, now as a rule on cells.
* `tok_halt`: if the `110` words run into a 0 instead (`1 0 (110)^j 0`), the machine halts in F. That is the only way
  it can halt from a tape of this shape.

Together with `Trip.lean`: every round trip from a tape whose cells up to the first `00` are runs and token chains is
`ca3` of the filled tape, and the machine halts exactly when a token chain meets a 0.
-/

namespace H696

open TM

/-- A piece of tape: an ordinary run `1^(k+2) 0`, or a token chain `1 0 (110)^j 1^(k+3) 0`. -/
inductive Pc where
  | run (k : Nat)
  | tok (j k : Nat)

/-- The cells of a piece, left to right. -/
def pcells : Pc → List Bool
  | .run k => run k
  | .tok j k => [true, false] ++ (List.replicate j [true, true, false]).flatten ++ run (k + 1)

/-- The ordinary run the piece behaves as (holes filled). -/
def pk : Pc → Nat
  | .run k => k
  | .tok j k => 3 * j + k + 3

def pcs : List Pc → List Bool
  | [] => []
  | p :: ps => pcells p ++ pcs ps

theorem app_y (j : Nat) (R : Tape) :
    app (List.replicate j [true, true, false]).flatten R = rep j [true, true, false] R := by
  induction j with
  | zero => rfl
  | succ j ih => rw [List.replicate_succ, List.flatten_cons, ← app_app, ih]; rfl

theorem rep_fff (j : Nat) (L : Tape) : rep j [false, false, false] L = rep (3 * j) [false] L := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [rep_succ, ih, show 3 * (j + 1) = 3 + 3 * j by omega, rep_add]; rfl

/-- F crosses `110` words: each becomes `000`. -/
theorem fys (j : Nat) : ∀ (L R : Tape),
    steps (3 * j) ⟨L, rep j [true, true, false] R, .F⟩ = some ⟨rep j [false, false, false] L, R, .F⟩ := by
  induction j with
  | zero => intro L R; rfl
  | succ j ih =>
    intro L R
    have h1 : steps 3 ⟨L, rep (j + 1) [true, true, false] R, .F⟩ =
        some ⟨app [false, false, false] L, rep j [true, true, false] R, .F⟩ := rfl
    have h2 := ih (app [false, false, false] L) R
    have e : rep j [false, false, false] (app [false, false, false] L) = rep (j + 1) [false, false, false] L :=
      rep_app_comm j _ L
    rw [e] at h2
    rw [show 3 * (j + 1) = 3 + 3 * j by omega]
    exact steps_seq trans h1 h2

/-- **The right sweep over a token chain** leaves the same cells and state as over the filled run. -/
theorem rtok (j k : Nat) (L R : Tape) :
    steps (2 + 3 * j + 1 + (3 * k + 3)) ⟨L, app (pcells (.tok j k)) R, .B⟩ =
      some ⟨cons true (cons true (rep (3 * j + k + 3 + 1) [false] L)), R, .B⟩ := by
  have e0 : app (pcells (.tok j k)) R = cons true (cons false (rep j [true, true, false] (app (run (k + 1)) R))) := by
    show app ([true, false] ++ (List.replicate j [true, true, false]).flatten ++ run (k + 1)) R = _
    rw [← app_app, ← app_app, app_y]; rfl
  rw [e0]
  have h1 : steps 2 ⟨L, cons true (cons false (rep j [true, true, false] (app (run (k + 1)) R))), .B⟩ =
      some ⟨cons false (cons false L), rep j [true, true, false] (app (run (k + 1)) R), .F⟩ := rfl
  have h2 := fys j (cons false (cons false L)) (app (run (k + 1)) R)
  have h3 : steps 1 ⟨rep j [false, false, false] (cons false (cons false L)), app (run (k + 1)) R, .F⟩ =
      some ⟨cons false (rep j [false, false, false] (cons false (cons false L))), app (run k) R, .B⟩ := rfl
  have h4 := rrun k (cons false (rep j [false, false, false] (cons false (cons false L)))) R
  have h := steps_seq trans (steps_seq trans (steps_seq trans h1 h2) h3) h4
  have e : rep (k + 1) [false] (cons false (rep j [false, false, false] (cons false (cons false L)))) =
      rep (3 * j + k + 3 + 1) [false] L := by
    rw [rep_fff]
    show rep (k + 1) [false] (rep 1 [false] (rep (3 * j) [false] (rep 2 [false] L))) = _
    rw [← rep_add, ← rep_add, ← rep_add]
    congr 1; omega
  rw [e] at h
  exact h

/-- The right sweep over one piece. -/
theorem rpiece (p : Pc) (L R : Tape) : ∃ n,
    steps n ⟨L, app (pcells p) R, .B⟩ = some ⟨cons true (cons true (rep (pk p + 1) [false] L)), R, .B⟩ := by
  cases p with
  | run k => exact ⟨_, rrun k L R⟩
  | tok j k => exact ⟨_, rtok j k L R⟩

/-- The third cell of the filled pieces. -/
def pfl : List Pc → Bool
  | [] => false
  | p :: _ => lng (pk p)

theorem pfl_eq (ps : List Pc) : pfl ps = fl (ps.map pk) := by
  cases ps <;> rfl

/-- **There and back over pieces**: as over the filled runs. -/
theorem psweep (ps : List Pc) : ∀ (Y R : Tape), ∃ n,
    steps n ⟨Y, app (pcs ps) (cons false R), .B⟩ =
      some (onL Y (app (out (ps.map pk)) (cons true R)) (sg true true (pfl ps))) := by
  induction ps with
  | nil => intro Y R; exact ⟨1, rfl⟩
  | cons p ps ih =>
    intro Y R
    obtain ⟨n1, h1⟩ := rpiece p Y (app (pcs ps) (cons false R))
    obtain ⟨n2, h2⟩ := ih (cons true (cons true (rep (pk p + 1) [false] Y))) R
    have h3 := lblock (pk p) (pfl ps) Y (app (out (ps.map pk)) (cons true R))
    have e1 : app (pcs (p :: ps)) (cons false R) = app (pcells p) (app (pcs ps) (cons false R)) := by
      show app (pcells p ++ pcs ps) _ = _; rw [← app_app]
    have e2 : app (blockOut (pk p) (pfl ps)) (app (out (ps.map pk)) (cons true R)) =
        app (out ((p :: ps).map pk)) (cons true R) := by
      rw [app_app]; cases ps <;> rfl
    rw [e2] at h3
    rw [e1]
    exact ⟨_, steps_seq trans (steps_seq trans h1 h2) h3⟩

/-- **A round trip over runs and token chains** is the cell automaton on the filled tape. -/
theorem trip_tok (ps : List Pc) (L R : Tape) : ∃ n,
    steps n ⟨L, cons false (app (pcs ps) (cons false R)), .A⟩ =
      some (onL L (app (ca3 (false :: runs (ps.map pk) ++ [true, true, false])) (cons true R)) .A) := by
  have h0 : steps 1 ⟨L, cons false (app (pcs ps) (cons false R)), .A⟩ =
      some ⟨cons true L, app (pcs ps) (cons false R), .B⟩ := rfl
  obtain ⟨n1, h1⟩ := psweep ps (cons true L) R
  have h2 := lstep false true true (pfl ps) (by cases pfl ps <;> rfl) rfl L (app (out (ps.map pk)) (cons true R))
  obtain ⟨r, hr⟩ := runs_ttf (ps.map pk)
  have e : ca3 (false :: runs (ps.map pk) ++ [true, true, false]) = (false == pfl ps) :: out (ps.map pk) := by
    rw [← out_ca3 (ps.map pk), List.cons_append, hr, pfl_eq]; rfl
  rw [e]
  have h12 := steps_seq trans h0 h1
  have e2 : onL (cons true L) (app (out (ps.map pk)) (cons true R)) (sg true true (pfl ps)) =
      onL (cons (!(false && true)) L) (app (out (ps.map pk)) (cons true R)) (sg true true (pfl ps)) := rfl
  rw [e2] at h12
  exact ⟨_, steps_seq trans h12 h2⟩

/-- **The halt**: B on a lone 1 whose `110` words run into a 0 stops in F on that 0. -/
theorem tok_halt (j : Nat) (L R : Tape) :
    ∃ c, steps (2 + 3 * j) ⟨L, cons true (cons false (rep j [true, true, false] (cons false R))), .B⟩ = some c ∧
      step c = none := by
  have h1 : steps 2 ⟨L, cons true (cons false (rep j [true, true, false] (cons false R))), .B⟩ =
      some ⟨cons false (cons false L), rep j [true, true, false] (cons false R), .F⟩ := rfl
  have h2 := fys j (cons false (cons false L)) (cons false R)
  exact ⟨_, steps_seq trans h1 h2, rfl⟩

/-- **Filling moves the output at two cells.** Changing input cells changes `ca3` at `p` exactly when one, but not
both, of `p` and `p + 3` changed. Filling the holes at `i+1, i+4, ..., i+1+3j` (a lone 1 at `i` and `j` words `110`)
therefore changes the output only at `p = i-2` and `p = i+1+3j`: the defect's jump. -/
theorem ca3_diff (w w' : List Bool) (hl : w'.length = w.length) (p : Nat) (hp : p + 3 < w.length) :
    ((ca3 w').getD p false != (ca3 w).getD p false) =
      ((w'.getD p false != w.getD p false) != (w'.getD (p + 3) false != w.getD (p + 3) false)) := by
  rw [ca3_getD w p hp, ca3_getD w' p (by omega)]
  cases w.getD p false <;> cases w'.getD p false <;> cases w.getD (p + 3) false <;>
    cases w'.getD (p + 3) false <;> rfl

end H696
