import VisitR

/-! # The binary streams of 1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LA---

The stream laws proved for the sibling 1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB--- (its `lean/Stream.lean`), here for
this machine, from the rows of `VisitR.lean`; streams on the right side, states of the sibling renamed (the same names).
Tokens of two cells: `z = 00`, `a = 10`, `c = 01`.

* `vb_even`, `vb_odd`, `ve_odd`, **the a/z stream**: a visit in (the sibling's) state B turns the first `z` into `a`
  and every second `a` before it into `z`; with digits `a z` = 0, `a a` = 1 the odd case is a binary increment.
* `m_inc`, `m_wrap`, **the counter M** (digits `z c` = 0, `c c` = 1): one visit in (the sibling's) state A adds one,
  and when M is all ones it wraps and the stream after it gets three visits.

All for every stream beyond, every context, every size. -/

namespace H2327

open TM

theorem vb_even (k : Nat) (x : Tape) :
    Vis .B (rep k [true, false, true, false] (cons false (cons false x))) .C
      (rep k [false, false, true, false] (cons true (cons false x))) := by
  induction k with
  | zero => exact v_B_00_none
  | succ k ih => exact v_B_10_Ba (v_B_10_Bc ih)

theorem vb_odd (k : Nat) (x : Tape) :
    Vis .B (cons true (cons false (rep k [true, false, true, false] (cons false (cons false x))))) .A
      (cons true (cons false (rep k [false, false, true, false] (cons true (cons false x))))) :=
  v_B_10_Bc (vb_even k x)

theorem ve_odd (k : Nat) (x : Tape) :
    Vis .E (cons true (cons false (rep k [true, false, true, false] (cons false (cons false x))))) .A
      (cons true (cons false (rep k [false, false, true, false] (cons true (cons false x))))) :=
  v_E_10_Bc (vb_even k x)

theorem m_carry {y y' : Tape} (hE : Vis .E y .C y) (hA : Vis .A y .D y') :
    Vis .A (cons false (cons true (cons false (cons true y)))) .D
      (cons false (cons false (cons false (cons true y')))) :=
  v_A_01_EcAe v_E_01_none (v_A_01_EcAd hE hA)

theorem m_inc (k : Nat) (y : Tape) :
    Vis .A (rep k [false, true, false, true] (cons false (cons false y))) .D
      (rep k [false, false, false, true] (cons false (cons true y))) := by
  induction k with
  | zero => exact v_A_00_none
  | succ k ih =>
    refine m_carry ?_ ih
    cases k with
    | zero => exact v_E_00_none
    | succ k => exact v_E_01_none

theorem m_wrap (k : Nat) {x x1 x2 x3 : Tape} (h1 : Vis .E x .A x1) (h2 : Vis .B x1 .A x2) (h3 : Vis .B x2 .A x3) :
    Vis .A (rep (k + 1) [false, true, false, true] (cons false (cons true x))) .D
      (rep (k + 1) [false, false, false, true] (cons false (cons true x3))) := by
  induction k with
  | zero =>
    exact v_A_01_EcAe v_E_01_none (v_A_01_EcAcAd v_E_01_none (v_A_01_EaBaBa h1 h2 h3) v_A_00_none)
  | succ k ih => exact m_carry v_E_01_none ih

end H2327
