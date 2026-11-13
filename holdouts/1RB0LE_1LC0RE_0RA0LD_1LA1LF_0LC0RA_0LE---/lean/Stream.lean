import Visit

/-! # The right side of 1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LE--- as recursive visit laws

Tokens of two cells: `z = 00`, `a = 10`, `c = 01`.  From the rows of `Visit.lean`, by induction:

* **the a/z stream** (the counter R and everything after it, blank tape included: blank is `z z z ...`).
  A visit in state B turns the first `z` into `a` and every second `a` before it into `z`:
  `B> (a a)^k z x` leaves `(z a)^k a x` and comes out in C (`vb_even`);
  `B> a (a a)^k z x` leaves `a (z a)^k a x` and comes out in A (`vb_odd`), and the same for a visit in state E
  (`ve_odd`).  With digits `a z` = 0, `a a` = 1 the odd case is the binary increment `1^k 0 -> 0^k 1`; there is no
  overflow, because the stream never ends.  The even case (first `z` at an even place) comes out in C instead of A.
* **the counter M** (digits `z c` = 0, `c c` = 1): `A> (c c)^k z c y` leaves `(z c)^k c c y`, out in D (`m_inc`);
  when M is all ones, `A> (c c)^(k+1) c x` leaves `(z c)^(k+1) c x3`, out in D, where `x3` is `x` after three
  visits E, B, B that all come out in A (`m_wrap`).

All for every stream to the right, every left context, every size. -/

namespace H61234

open TM

/-- `B> (a a)^k z x`: out in C, leaving `(z a)^k a x`. -/
theorem vb_even (k : Nat) (x : Tape) :
    Vis .B (rep k [true, false, true, false] (cons false (cons false x))) .C
      (rep k [false, false, true, false] (cons true (cons false x))) := by
  induction k with
  | zero => exact v_B_00_none
  | succ k ih => exact v_B_10_Ba (v_B_10_Bc ih)

/-- `B> a (a a)^k z x`: out in A, leaving `a (z a)^k a x` (binary increment of the digits `a z`, `a a`). -/
theorem vb_odd (k : Nat) (x : Tape) :
    Vis .B (cons true (cons false (rep k [true, false, true, false] (cons false (cons false x))))) .A
      (cons true (cons false (rep k [false, false, true, false] (cons true (cons false x))))) :=
  v_B_10_Bc (vb_even k x)

/-- The same visit in state E. -/
theorem ve_odd (k : Nat) (x : Tape) :
    Vis .E (cons true (cons false (rep k [true, false, true, false] (cons false (cons false x))))) .A
      (cons true (cons false (rep k [false, false, true, false] (cons true (cons false x))))) :=
  v_E_10_Bc (vb_even k x)

/-- A carry through one digit 1 of M: `A> c c y` leaves `z c y'`, out in D, if `A> y` leaves `y'`, out in D, and
`E> y` comes straight back in C. -/
theorem m_carry {y y' : Tape} (hE : Vis .E y .C y) (hA : Vis .A y .D y') :
    Vis .A (cons false (cons true (cons false (cons true y)))) .D
      (cons false (cons false (cons false (cons true y')))) :=
  v_A_01_EcAe v_E_01_none (v_A_01_EcAd hE hA)

/-- **M + 1 without a wrap**: `A> (c c)^k z c y` leaves `(z c)^k c c y`, out in D. -/
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

/-- **M wraps**: `A> (c c)^(k+1) c x` leaves `(z c)^(k+1) c x3`, out in D, where the stream after M gets three
visits (E, B, B), each coming out in A. -/
theorem m_wrap (k : Nat) {x x1 x2 x3 : Tape} (h1 : Vis .E x .A x1) (h2 : Vis .B x1 .A x2) (h3 : Vis .B x2 .A x3) :
    Vis .A (rep (k + 1) [false, true, false, true] (cons false (cons true x))) .D
      (rep (k + 1) [false, false, false, true] (cons false (cons true x3))) := by
  induction k with
  | zero =>
    exact v_A_01_EcAe v_E_01_none (v_A_01_EcAcAd v_E_01_none (v_A_01_EaBaBa h1 h2 h3) v_A_00_none)
  | succ k ih => exact m_carry v_E_01_none ih

end H61234
