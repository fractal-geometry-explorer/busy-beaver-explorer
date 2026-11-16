import VisitL

/-! # The binary streams of 1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB---

The stream laws proved for the sibling 1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB--- (its `lean/Stream.lean`), here for
this machine, from the rows of `VisitL.lean`; streams on the left (nearest cell first) side, states of the sibling renamed (A as C, B as A, C as B, D as E, E as D).
Tokens of two cells: `z = 00`, `a = 10`, `c = 01`.

* `vb_even`, `vb_odd`, `ve_odd`, **the a/z stream**: a visit in (the sibling's) state B turns the first `z` into `a`
  and every second `a` before it into `z`; with digits `a z` = 0, `a a` = 1 the odd case is a binary increment.
* `m_inc`, `m_wrap`, **the counter M** (digits `z c` = 0, `c c` = 1): one visit in (the sibling's) state A adds one,
  and when M is all ones it wraps and the stream after it gets three visits.

All for every stream beyond, every context, every size. -/

namespace H55410

open TM

theorem vb_even (k : Nat) (x : Tape) :
    VisL .A (rep k [true, false, true, false] (cons false (cons false x))) .B
      (rep k [false, false, true, false] (cons true (cons false x))) := by
  induction k with
  | zero => exact w_A_00_none
  | succ k ih => exact w_A_10_Ac (w_A_10_Ab ih)

theorem vb_odd (k : Nat) (x : Tape) :
    VisL .A (cons true (cons false (rep k [true, false, true, false] (cons false (cons false x))))) .C
      (cons true (cons false (rep k [false, false, true, false] (cons true (cons false x))))) :=
  w_A_10_Ab (vb_even k x)

theorem ve_odd (k : Nat) (x : Tape) :
    VisL .D (cons true (cons false (rep k [true, false, true, false] (cons false (cons false x))))) .C
      (cons true (cons false (rep k [false, false, true, false] (cons true (cons false x))))) :=
  w_D_10_Ab (vb_even k x)

theorem m_carry {y y' : Tape} (hE : VisL .D y .B y) (hA : VisL .C y .E y') :
    VisL .C (cons false (cons true (cons false (cons true y)))) .E
      (cons false (cons false (cons false (cons true y')))) :=
  w_C_01_DbCd w_D_01_none (w_C_01_DbCe hE hA)

theorem m_inc (k : Nat) (y : Tape) :
    VisL .C (rep k [false, true, false, true] (cons false (cons false y))) .E
      (rep k [false, false, false, true] (cons false (cons true y))) := by
  induction k with
  | zero => exact w_C_00_none
  | succ k ih =>
    refine m_carry ?_ ih
    cases k with
    | zero => exact w_D_00_none
    | succ k => exact w_D_01_none

theorem m_wrap (k : Nat) {x x1 x2 x3 : Tape} (h1 : VisL .D x .C x1) (h2 : VisL .A x1 .C x2) (h3 : VisL .A x2 .C x3) :
    VisL .C (rep (k + 1) [false, true, false, true] (cons false (cons true x))) .E
      (rep (k + 1) [false, false, false, true] (cons false (cons true x3))) := by
  induction k with
  | zero =>
    exact w_C_01_DbCd w_D_01_none (w_C_01_DbCbCe w_D_01_none (w_C_01_DcAcAc h1 h2 h3) w_C_00_none)
  | succ k ih => exact m_carry w_D_01_none ih

end H55410
