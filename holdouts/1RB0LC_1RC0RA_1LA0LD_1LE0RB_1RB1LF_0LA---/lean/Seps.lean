import Rules
import TM.ListFrame

/-!
# Rounds of 1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RB1LF_0LA--- with any number of separators

`Rules.lean` proves the rounds `round_one` and `round_zero` for a tape with one separator before the cursor.  Here
the same rounds are proved for every list of separators and runs before it, by induction over the list (the README's
"rounds with any number of separators as one Lean theorem").  At an event the tape reads

    m+2 | x1 | x2 | ... | xk | a  C          (runs of 01, | = 00110, C the cursor and what follows it)

and a round moves the cursor and leaves every `xi` alone, as long as each `xi` has at least two pairs (the left pass
moves two pairs across each separator and back).  `round_sep` takes the cursor's behaviour as a hypothesis (`turn`):
what the head does after the right pass has reached the cursor, until it is back on the left of the run `a`.
`round_one_sep` and `round_zero_sep` are the two walking rounds:

    m+2 | x1 | ... | xk | a "1" R         ->  m+1 | x1 | ... | xk | a+2 "0" R
    m+2 | x1 | ... | xk | a "0" b+2 R     ->  m+1 | x1 | ... | xk | a+4 "1" b R

with `xi = yi + 2` (any `yi`).  These are the double rounds that `py/tok.py` applies in bulk.  Kernel only; step
counts are existential.
-/

namespace H37843

open TM

/-- A separator and a run, on the right of the head: `00110 (01)^x`. -/
def P (x : Nat) (X : Tape) : Tape := app [false, false, true, true, false] (rep x [false, true] X)

/-- A separator after the right pass, on the left of the head (nearest cell first): `11010`. -/
def sl (L : Tape) : Tape := cons false (cons true (cons false (cons true (cons true L))))

/-- A run and the separator on its left after the right pass, on the left of the head. -/
def gR (x : Nat) (L : Tape) : Tape := rep x [false, true] (sl L)

/-- A separator, the two pairs on its left, and the rest `y` of that run, on the left of the head. -/
def B (y : Nat) (L : Tape) : Tape := sl (rep 2 [false, true] (rep y [false, true] L))

/-- What the left pass leaves on the right of the head for one block `B y`. -/
def G (y : Nat) (R : Tape) : Tape :=
  rep y [true, false] (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true
    (cons false R)))))))))

/-- The same in normal form: a run `y`, a separator and two pairs. -/
def H (y : Nat) (Z : Tape) : Tape := rep y [false, true] (app [false, false, true, true, false] (rep 2 [false, true] Z))

theorem pass_P (x : Nat) (L R : Tape) : ∃ n, steps n ⟨L, P x R, .A⟩ = some ⟨gR x L, R, .A⟩ :=
  ⟨_, steps_seq trans (pass_sep L (rep x [false, true] R)) (pass_run x (sl L) R)⟩

theorem back_B (y : Nat) (L R : Tape) :
    ∃ n, steps n ⟨B y L, cons true R, .A⟩ = some ⟨L, cons true (G y R), .A⟩ :=
  ⟨_, steps_seq trans (back_sep (rep y [false, true] L) R) (back_run y L _)⟩

/-- The right pass over separators and runs. -/
theorem pass_list (ts : List Nat) (L R : Tape) :
    ∃ n, steps n ⟨L, sq P ts R, .A⟩ = some ⟨sqr gR ts L, R, .A⟩ :=
  seqR trans P gR id .A (fun x L R => pass_P x L R) ts L R

/-- The left pass over separators and runs. -/
theorem back_list (ts : List Nat) (L R : Tape) :
    ∃ n, steps n ⟨sqr B ts L, cons true R, .A⟩ = some ⟨L, cons true (sq G ts R), .A⟩ :=
  seqL' trans B G (cons true) .A (fun y L R => back_B y L R) ts L R

theorem sl_sqr (ys : List Nat) (W : Tape) : sl (sqr gR (ys.map (· + 2)) W) = sqr B ys (sl W) := by
  induction ys generalizing W with
  | nil => rfl
  | cons y ys ih =>
    rw [List.map_cons, sqr_cons, ih, sqr_cons]
    show sqr B ys (sl (rep (y + 2) [false, true] (sl W))) = sqr B ys (sl (rep 2 [false, true] (rep y [false, true] (sl W))))
    rw [← rep_add, Nat.add_comm 2 y]

theorem cons_G (y : Nat) (X : Tape) : cons false (G y X) = H y (cons false X) := by
  have e := rep_rotate y [false] [true, false] [false, true] rfl
    (cons false (cons true (cons true (cons false (cons false (cons true (cons false (cons true (cons false X)))))))))
  simp only [app_cons, app_nil] at e
  simp only [G, H, e]; rfl

theorem cons_sqG (ys : List Nat) (X : Tape) : cons false (sq G ys X) = sq H ys (cons false X) := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp only [sq_cons, cons_G, ih]

theorem app_sqH (ys : List Nat) (Z : Tape) :
    app [false, false, true, true, false] (rep 2 [false, true] (sq H ys Z)) =
      sq P (ys.map (· + 2)) (app [false, false, true, true, false] (rep 2 [false, true] Z)) := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    simp only [sq_cons, List.map_cons, H, P]
    rw [← ih, ← rep_add, Nat.add_comm 2 y]

/-- A round over any list of separators, given what the cursor does (`turn`). -/
theorem round_sep (m a : Nat) (ys : List Nat) (C D : Tape)
    (turn : ∀ L, ∃ n, steps n ⟨rep a [false, true] L, C, .A⟩ = some ⟨L, cons true (rep a [true, false] D), .A⟩) :
    ∃ n, steps n ⟨blank, rep (m + 2) [false, true] (sq P (ys.map (· + 2) ++ [a]) C), .A⟩ =
      some ⟨blank, rep (m + 1) [false, true] (sq P (ys.map (· + 2) ++ [a + 2]) (cons false D)), .A⟩ := by
  have h1 := pass_run (m + 2) blank (sq P (ys.map (· + 2) ++ [a]) C)
  obtain ⟨n2, h2⟩ := pass_list (ys.map (· + 2) ++ [a]) (rep (m + 2) [false, true] blank) C
  rw [sqr_eq, List.reverse_append, List.reverse_singleton, List.singleton_append, sq_cons, ← sqr_eq] at h2
  obtain ⟨n3, h3⟩ := turn (sl (sqr gR (ys.map (· + 2)) (rep (m + 2) [false, true] blank)))
  have e1 : sl (sqr gR (ys.map (· + 2)) (rep (m + 2) [false, true] blank)) = sqr B (m :: ys) blank := by
    rw [sl_sqr, sqr_cons]
    simp only [B, Nat.add_comm m 2, rep_add]
  rw [e1] at h3
  simp only [gR] at h2
  rw [e1] at h2
  obtain ⟨n4, h4⟩ := back_list (m :: ys) blank (rep a [true, false] D)
  have h5 := left_end 0 (sq G (m :: ys) (rep a [true, false] D))
  simp only [rep_zero] at h5
  have hall := steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 (steps_seq trans h4 h5)))
  refine ⟨_, hall.trans ?_⟩
  congr 2
  rw [sq_cons, cons_G, cons_sqG]
  have e2 := rep_rotate a [false] [true, false] [false, true] rfl D
  simp only [app_cons, app_nil] at e2
  rw [e2, sq_append, sq_cons, sq_nil]
  show cons false (cons true (rep m [false, true] _)) = _
  rw [show cons false (cons true (rep m [false, true]
      (app [false, false, true, true, false] (rep 2 [false, true] (sq H ys (rep a [false, true] (cons false D))))))) =
      rep (m + 1) [false, true] (app [false, false, true, true, false] (rep 2 [false, true]
        (sq H ys (rep a [false, true] (cons false D))))) from rfl, app_sqH]
  rw [← rep_add, Nat.add_comm 2 a]
  rfl

/-- Cursor `1`: `m+2 | x1 | ... | xk | a "1" R  ->  m+1 | x1 | ... | xk | a+2 "0" R`. -/
theorem round_one_sep (m a : Nat) (ys : List Nat) (R : Tape) :
    ∃ n, steps n ⟨blank, rep (m + 2) [false, true] (sq P (ys.map (· + 2) ++ [a]) (cons true R)), .A⟩ =
      some ⟨blank, rep (m + 1) [false, true] (sq P (ys.map (· + 2) ++ [a + 2]) (cons false R)), .A⟩ :=
  round_sep m a ys (cons true R) R (fun L => ⟨_, back_run a L R⟩)

/-- Cursor `0`: `m+2 | x1 | ... | xk | a "0" b+2 R  ->  m+1 | x1 | ... | xk | a+4 "1" b R`. -/
theorem round_zero_sep (m a b : Nat) (ys : List Nat) (R : Tape) :
    ∃ n, steps n ⟨blank, rep (m + 2) [false, true]
        (sq P (ys.map (· + 2) ++ [a]) (cons false (rep (b + 2) [false, true] R))), .A⟩ =
      some ⟨blank, rep (m + 1) [false, true] (sq P (ys.map (· + 2) ++ [a + 4]) (cons true (rep b [false, true] R))),
        .A⟩ := by
  have turn : ∀ L, ∃ n, steps n ⟨rep a [false, true] L, cons false (rep (b + 2) [false, true] R), .A⟩ =
      some ⟨L, cons true (rep a [true, false] (cons true (cons false (cons true (cons true
        (rep b [false, true] R)))))), .A⟩ := by
    intro L
    have h1 := R2 1 (rep a [false, true] L) (cons true (rep b [false, true] R))
    have h2 := L1 (rep a [false, true] L) (cons true (cons true (rep b [false, true] R)))
    have h3 := back_run a L (cons true (cons false (cons true (cons true (rep b [false, true] R)))))
    exact ⟨_, steps_seq trans h1 (steps_seq trans h2 h3)⟩
  obtain ⟨n, h⟩ := round_sep m a ys _ _ turn
  refine ⟨n, ?_⟩
  rw [h]
  congr 3
  rw [sq_append, sq_append, sq_cons, sq_cons, sq_nil, sq_nil]
  congr 1
  simp only [P]
  congr 1
  simp only [show a + 4 = (a + 2) + 2 from rfl, rep_add (a + 2) 2, rep_add a 2]
  rfl

end H37843
