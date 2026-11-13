import Machine

/-!
# Normal forms of tapes for 1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE

The symbolic runs of `Pieces.lean` end in tapes bracketed the way the run wrote them (`1 (11)^n 1 1`, `0 1 (01)^n`, `(1010)^j`, `(1111)^j`, ...).
These lemmas rewrite them into one normal form: blocks of 1s as `rep n [true]`, runs of `10` as `rep n [true, false]`
read rightwards and `rep n [false, true]` read leftwards.  `tape_eq` closes an equation between two tapes that are
equal up to these rewritings and linear arithmetic in the repeat counts.
-/

namespace H113619

open TM

theorem rep_tt (n : Nat) (X : Tape) : rep n [true, true] X = rep (2 * n) [true] X := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, rep_succ, rep_succ, rep_succ, ih]; rfl

theorem rep_tftf (n : Nat) (X : Tape) : rep n [true, false, true, false] X = rep (2 * n) [true, false] X := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 2 * (n + 1) = 2 + 2 * n by omega, rep_add 2 (2 * n), ← ih]; rfl

theorem rep_ftft (n : Nat) (X : Tape) : rep n [false, true, false, true] X = rep (2 * n) [false, true] X := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 2 * (n + 1) = 2 + 2 * n by omega, rep_add 2 (2 * n), ← ih]; rfl

theorem rep_tttt (n : Nat) (X : Tape) : rep n [true, true, true, true] X = rep (4 * n) [true] X := by
  induction n with
  | zero => rfl
  | succ n ih => rw [show 4 * (n + 1) = 4 + 4 * n by omega, rep_add 4 (4 * n), ← ih]; rfl

theorem ones_ones (n k : Nat) (X : Tape) : rep n [true] (rep k [true] X) = rep (n + k) [true] X :=
  (rep_add n k [true] X).symm

theorem ones_cons (n : Nat) (X : Tape) : rep n [true] (cons true X) = rep (n + 1) [true] X :=
  rep_app_comm n [true] X

theorem cons_ones (n : Nat) (X : Tape) : cons true (rep n [true] X) = rep (n + 1) [true] X := by
  rw [show n + 1 = 1 + n by omega, rep_add]; rfl

theorem tf_tf (n k : Nat) (X : Tape) : rep n [true, false] (rep k [true, false] X) = rep (n + k) [true, false] X :=
  (rep_add n k [true, false] X).symm

theorem ft_ft (n k : Nat) (X : Tape) : rep n [false, true] (rep k [false, true] X) = rep (n + k) [false, true] X :=
  (rep_add n k [false, true] X).symm

theorem cons_tf (n : Nat) (X : Tape) : cons true (cons false (rep n [true, false] X)) = rep (n + 1) [true, false] X := by
  rw [show n + 1 = 1 + n by omega, rep_add]; rfl

theorem cons_ft (n : Nat) (X : Tape) : cons false (cons true (rep n [false, true] X)) = rep (n + 1) [false, true] X := by
  rw [show n + 1 = 1 + n by omega, rep_add]; rfl

theorem tf_t (n : Nat) (X : Tape) : rep n [true, false] (cons true X) = cons true (rep n [false, true] X) :=
  (rep_rotate n [true] [false, true] [true, false] rfl X).symm

theorem ft_f (n : Nat) (X : Tape) : rep n [false, true] (cons false X) = cons false (rep n [true, false] X) :=
  (rep_rotate n [false] [true, false] [false, true] rfl X).symm

theorem ones_blank_zero (X : Tape) : rep 0 [true] X = X := rfl

theorem rep_congr2 {x y : Nat} {w : List Bool} {X Y : Tape} (h : x = y) (h2 : X = Y) : rep x w X = rep y w Y := by
  rw [h, h2]

theorem cons_congr {a : Bool} {X Y : Tape} (h : X = Y) : cons a X = cons a Y := by rw [h]

theorem steps_eq_of {n : Nat} {c c' d d' : Config} (h : steps n c = some d) (hc : c = c') (hd : d = d') :
    steps n c' = some d' := by rw [← hc, ← hd]; exact h

theorem cfg_eq {l l' r r' : Tape} {q : St} (hl : l = l') (hr : r = r') :
    (⟨l, r, q⟩ : Config) = ⟨l', r', q⟩ := by rw [hl, hr]

/-- Normalise both sides (pairs `11`, `1111` into 1s, `1010` and `0101` into `10` and `01`, literal repeat counts unfolded, then 1s folded into blocks and `10`/`01`
runs rotated one way), then match them repeat by repeat, leaving the counts to `omega`. -/
macro "tape_eq" : tactic =>
  `(tactic| focus
    try simp only [rep_tt, rep_tftf, rep_ftft, rep_tttt]
    try simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, rep_succ, rep_zero, app_cons, app_nil, cons_false_blank]
    try simp only [ones_ones, ones_cons, cons_ones, tf_tf, ft_ft, cons_tf, cons_ft, tf_t, ft_f, cons_false_blank]
    repeat' (first | rfl | apply rep_congr2 | apply cons_congr)
    all_goals omega)

end H113619
