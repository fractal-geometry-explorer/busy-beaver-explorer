import Rules

/-! # The counter: one right-end excursion as a map on block lengths

At the right end of the tape the head sits in state C in front of `0 1`, with everything else to its left.  The
tape left of the head is a list of *levels*, read from the head outwards; a level is

    s_l (10)^g s_r (10)^W

(left to right on the tape) with two single separator cells `s_l`, `s_r`.  Its *digit* is 2 for seps `1 1`, 1 for
`0 1` and 0 for `0 0`.  One excursion from the right end and back subtracts one from the number these digits spell
in base 3 (last level lowest): it walks left over the levels with digit 0, turns at the first level with digit 1 or
2, and on the way back resets each digit-0 level to digit 2.  The theorems below state this for any number of
borrows and any block lengths (with the parities the run keeps), each with all four cases:

* `last2`, `last1`: the last level has digit 2 or 1 and no borrow happens;
* `borrow2`, `borrow1`: the last level and the levels in `zs` have digit 0 and the level after them has digit 2 or 1.

A level loses one pair from its `W` and gains one in its `g` each time its digit changes 2 → 1 or 0 → 2, except
the last level, whose `W` grows: every excursion adds two pairs to the tape.

Hand-written; the moves come from `Rules.lean` (`first0`, `walk0`, `turn2`, `turn1`, `sweep0`, `sweepLast`, `last2`,
`last1`), the rest is tape algebra.
-/

namespace BB6e
open TM

/-- A pair `10`, as read from the head leftwards. -/
abbrev P : List Bool := [false, true]
abbrev Q : List Bool := [false, true, false, true]
abbrev Q' : List Bool := [true, false, true, false]

/-- A level `s_l (10)^g s_r (10)^W` left of the head, in front of the tape `L` further left. -/
def lv (sl sr : Bool) (g W : Nat) (L : Tape) : Tape := rep W P (cons sr (rep g P (cons sl L)))

/-- Levels with digit 0 that are not the last one, the one nearest the head first. -/
def Zs : List (Nat × Nat) → Tape → Tape
  | [], X => X
  | (c, d) :: zs, X => lv false false (2 * c + 2) (2 * d + 4) (Zs zs X)

/-- The same levels after the borrow has passed: digit 2, one pair moved from `W` to `g`. -/
def Rs : List (Nat × Nat) → Tape → Tape
  | [], X => X
  | (c, d) :: zs, X => lv true true (2 * c + 3) (2 * d + 3) (Rs zs X)

/-- The right end: the head reads `0 1`, blank beyond. -/
abbrev R0 : Tape := cons false (cons true blank)

/-! ## Tape algebra -/

theorem rep_two_mul (n : Nat) (w : List Bool) (s : Tape) : rep (2 * n) w s = rep n (w ++ w) s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, rep_succ, rep_succ, ih, rep_succ, app_app]

theorem rq (n : Nat) (s : Tape) : rep (2 * n) P s = rep n Q s := rep_two_mul n P s

/-! Normal form: pairs `01` are pushed behind repeats of `0101`, and `(10)^n` is written with `0101`. -/

theorem rep_succ' (n : Nat) (w : List Bool) (s : Tape) : rep (n + 1) w s = rep n w (app w s) :=
  (rep_app_comm n w s).symm

theorem pq (n : Nat) (s : Tape) : cons false (cons true (rep n Q s)) = rep n Q (cons false (cons true s)) :=
  rep_rotate n P Q Q rfl s

theorem rotf (n : Nat) (s : Tape) : cons false (rep n Q' s) = rep n Q (cons false s) :=
  rep_rotate n [false] Q' Q rfl s

theorem rq1 (n : Nat) (s : Tape) : rep (2 * n + 1) P s = rep n Q (app P s) := by
  rw [rep_add, rq]; rfl

theorem rq2 (n : Nat) (s : Tape) : rep (2 * n + 2) P s = rep n Q (app Q s) := by
  rw [show 2 * n + 2 = 2 * (n + 1) by omega, rq, rep_succ']

theorem rq3 (n : Nat) (s : Tape) : rep (2 * n + 3) P s = rep n Q (app Q (app P s)) := by
  rw [show 2 * n + 3 = 2 * (n + 1) + 1 by omega, rq1, rep_succ']

theorem rq4 (n : Nat) (s : Tape) : rep (2 * n + 4) P s = rep n Q (app Q (app Q s)) := by
  rw [show 2 * n + 4 = 2 * (n + 2) by omega, rq, rep_succ', rep_succ']

/-! ## The walk left over borrowing levels -/

/-- A digit-0 level as the walk meets it: two pairs of its `W` already crossed. -/
def Zw (c d : Nat) (Y : Tape) : Tape := rep (d + 1) Q (cons false (rep (c + 1) Q (cons false Y)))

/-- The digit-0 levels `zs` in front of `app Q T`, less the first two pairs. -/
def WZ : List (Nat × Nat) → Tape → Tape
  | [], T => T
  | (c, d) :: zs, T => Zw c d (app Q (WZ zs T))

theorem zs_wz (zs : List (Nat × Nat)) (T : Tape) : Zs zs (app Q T) = app Q (WZ zs T) := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    obtain ⟨c, d⟩ := z
    simp only [Zs, WZ, Zw, lv, ih]
    rw [show 2 * d + 4 = 2 * (d + 2) by omega, show 2 * c + 2 = 2 * (c + 1) by omega, rq, rq]
    rfl

/-- A level in transit form, on the right of the head, with the next one's first two cells `0 1` after it. -/
def Jb (c d : Nat) (R : Tape) : Tape :=
  rep c Q (cons false (cons true (cons false (cons false (rep (d + 1) Q' (cons true (cons false (cons false
    (cons true (cons false (cons true R)))))))))))

/-- The last level in transit form. -/
def JbL (c d : Nat) : Tape :=
  rep c Q (cons false (cons true (cons false (cons false (rep (d + 1) Q' (cons true (cons false (cons true
    (cons false (cons true blank))))))))))

def JR : List (Nat × Nat) → Tape → Tape
  | [], Y => Y
  | (c, d) :: zs, Y => JR zs (Jb c d Y)

abbrev W5 (R : Tape) : Tape := cons true (cons true (cons false (cons false (cons true R))))

theorem walkN (zs : List (Nat × Nat)) :
    ∀ T Y, ∃ n, steps n ⟨WZ zs T, W5 (cons false (cons true Y)), .C⟩
      = some ⟨T, W5 (cons false (cons true (JR zs Y))), .C⟩ := by
  induction zs with
  | nil => intro T Y; exact ⟨0, rfl⟩
  | cons z zs ih =>
    obtain ⟨c, d⟩ := z
    intro T Y
    obtain ⟨n, hn⟩ := ih T (Jb c d Y)
    exact ⟨_, steps_seq trans (walk0 c d (WZ zs T) (cons false (cons true Y))) hn⟩

/-! ## The sweep back -/

def S0 (e f : Nat) (X : Tape) : Tape :=
  cons false (cons true (cons true (cons false (cons true (cons false (rep f Q' (cons true (cons false (cons true
    (cons true (cons false (cons true (cons false (cons true (rep e Q X)))))))))))))))

def SR : List (Nat × Nat) → Tape → Tape
  | [], X => X
  | (c, d) :: zs, X => S0 c d (SR zs X)

theorem sweepN (zs : List (Nat × Nat)) :
    ∀ X Y, ∃ n, steps n ⟨X, JR zs Y, .C⟩ = some ⟨SR zs X, Y, .C⟩ := by
  induction zs with
  | nil => intro X Y; exact ⟨0, rfl⟩
  | cons z zs ih =>
    obtain ⟨c, d⟩ := z
    intro X Y
    obtain ⟨n, hn⟩ := ih X (Jb c d Y)
    exact ⟨_, steps_seq trans hn (sweep0 c d (SR zs X) Y)⟩

abbrev F3 (X : Tape) : Tape := cons false (cons true (cons true X))

theorem s0_canon (c d : Nat) (Y : Tape) : S0 c d (F3 Y) = F3 (lv true true (2 * c + 3) (2 * d + 3) Y) := by
  simp only [S0, lv, rq3, rotf, pq, app_cons, app_nil]

theorem sr_canon (zs : List (Nat × Nat)) (Y : Tape) : SR zs (F3 Y) = F3 (Rs zs Y) := by
  induction zs with
  | nil => rfl
  | cons z zs ih => obtain ⟨c, d⟩ := z; simp only [SR, Rs, ih, s0_canon]

theorem rs_head (zs : List (Nat × Nat)) (Y : Tape) : ∃ Y', Rs zs (cons false Y) = cons false Y' := by
  cases zs with
  | nil => exact ⟨Y, rfl⟩
  | cons z zs =>
    obtain ⟨c, d⟩ := z
    exact ⟨_, by simp only [Rs, lv]; rw [show 2 * d + 3 = (2 * d + 2) + 1 by omega, rep_succ]; rfl⟩

/-! ## The ends of the walk -/

/-- What `turn2` leaves left of the head. -/
def O2 (a b : Nat) (L : Tape) : Tape :=
  cons false (cons true (cons true (cons false (cons true (cons false (rep b Q' (cons true (cons true (cons false
    (rep a Q' (cons true (cons false (cons true (cons false L))))))))))))))

/-- What `turn1` leaves left of the head. -/
def O1 (a b : Nat) (L : Tape) : Tape :=
  cons false (cons true (cons true (cons false (cons true (cons false (rep b Q' (cons true (cons false
    (rep (a + 1) Q (cons false L))))))))))

/-- What `sweepLast` leaves left of the head. -/
def OL (e f : Nat) (L : Tape) : Tape :=
  cons false (cons true (cons false (rep f Q' (cons true (cons false (cons true (cons true (cons false (cons true
    (cons false (cons true (rep e Q (cons false (cons true (cons true (cons false L))))))))))))))))

theorem o2_canon (a b : Nat) (L : Tape) : O2 a b L = F3 (lv false true (2 * a + 2) (2 * b + 2) L) := by
  simp only [O2, lv, rq2, rotf, pq, app_cons, app_nil]

theorem o1_canon (a b : Nat) (L : Tape) : O1 a b L = F3 (lv false false (2 * a + 2) (2 * b + 2) L) := by
  simp only [O1, lv, rq, rotf, pq, rep_succ', app_cons, app_nil]

theorem ol_canon (e f : Nat) (L : Tape) : OL e f L = lv true true (2 * e + 3) (2 * f + 3) (cons false L) := by
  simp only [OL, lv, rq3, rotf, pq, app_cons, app_nil]

/-- The level after the turn begins with a pair. -/
theorem lv_head (sl sr : Bool) (g b : Nat) (L : Tape) :
    lv sl sr g (2 * b + 2) L = cons false (cons true (rep (2 * b + 1) P (cons sr (rep g P (cons sl L))))) := rfl

/-! ## The counter step -/

/-- The last level has digit 2: it becomes digit 1, one pair added to `g` and one to `W`. -/
theorem counter_last2 (a b : Nat) (L : Tape) :
    ∃ n, steps n ⟨lv true true (2 * a + 1) (2 * b + 1) L, R0, .C⟩
      = some ⟨lv false true (2 * a + 2) (2 * b + 2) L, R0, .C⟩ := by
  have h := last2 a b L
  have e1 : lv true true (2 * a + 1) (2 * b + 1) L
      = rep b Q (cons false (cons true (cons true (rep a Q (cons false (cons true (cons true L))))))) := by
    simp only [lv, rq1]; rfl
  have e2 : cons false (cons true (cons false (rep b Q' (cons true (cons true (cons false (rep a Q' (cons true
      (cons false (cons true (cons false L)))))))))))
      = lv false true (2 * a + 2) (2 * b + 2) L := by
    simp only [lv, rq2, rotf, pq, app_cons, app_nil]
  rw [e1, ← e2]; exact ⟨_, h⟩

/-- The last level has digit 1: it becomes digit 0 and its `W` grows by two pairs. -/
theorem counter_last1 (a b : Nat) (L : Tape) :
    ∃ n, steps n ⟨lv false true (2 * a + 2) (2 * b + 2) L, R0, .C⟩
      = some ⟨lv false false (2 * a + 2) (2 * b + 4) L, R0, .C⟩ := by
  have h := last1 a b L
  have e1 : lv false true (2 * a + 2) (2 * b + 2) L = rep (b + 1) Q (cons true (rep (a + 1) Q (cons false L))) := by
    simp only [lv]; rw [show 2 * b + 2 = 2 * (b + 1) by omega, show 2 * a + 2 = 2 * (a + 1) by omega, rq, rq]
  have e2 : cons false (cons true (cons false (rep (b + 1) Q' (cons true (cons false (rep (a + 1) Q
      (cons false L)))))))
      = lv false false (2 * a + 2) (2 * b + 4) L := by
    simp only [lv, rq, rotf, pq, rep_succ', app_cons, app_nil]
  rw [e1, ← e2]; exact ⟨_, h⟩

/-- The walk from the right end over the last level (digit 0) and the digit-0 levels `zs`, to the turn. -/
theorem walk_all (c d : Nat) (zs : List (Nat × Nat)) (T : Tape) :
    ∃ n, steps n ⟨lv false false (2 * c + 2) (2 * d + 2) (Zs zs (app Q T)), R0, .C⟩
      = some ⟨T, W5 (cons false (cons true (JR zs (JbL c d)))), .C⟩ := by
  have e2 : lv false false (2 * c + 2) (2 * d + 2) (Zs zs (app Q T))
      = rep (d + 1) Q (cons false (rep (c + 1) Q (cons false (app Q (WZ zs T))))) := by
    simp only [lv, zs_wz]
    rw [show 2 * d + 2 = 2 * (d + 1) by omega, show 2 * c + 2 = 2 * (c + 1) by omega, rq, rq]
  rw [e2]
  obtain ⟨n1, h1⟩ := walkN zs T (JbL c d)
  exact ⟨_, steps_seq trans (first0 c d (WZ zs T)) h1⟩

/-- The sweep back from the turn: the levels `zs` and the last one reset to digit 2. -/
theorem sweep_all (c d : Nat) (zs : List (Nat × Nat)) (sl sr : Bool) (g b : Nat) (L : Tape) :
    ∃ n, steps n ⟨SR zs (F3 (lv sl sr g (2 * b + 2) L)), JbL c d, .C⟩
      = some ⟨lv true true (2 * c + 3) (2 * d + 3) (Rs zs (lv sl sr g (2 * b + 2) L)), R0, .C⟩ := by
  obtain ⟨Y, hY⟩ := rs_head zs (cons true (rep (2 * b + 1) P (cons sr (rep g P (cons sl L)))))
  rw [sr_canon, lv_head, hY]
  have h : steps (4 * c + 4 * d + 11) ⟨F3 (cons false Y), JbL c d, .C⟩ = some ⟨OL c d Y, R0, .C⟩ :=
    sweepLast c d Y
  rw [ol_canon] at h
  exact ⟨_, h⟩

/-- A borrow through the last level and the levels `zs` (all digit 0), stopped by a level with digit 2. -/
theorem counter_borrow2 (a b c d : Nat) (zs : List (Nat × Nat)) (L : Tape) :
    ∃ n, steps n ⟨lv false false (2 * c + 2) (2 * d + 2) (Zs zs (lv true true (2 * a + 1) (2 * b + 3) L)), R0, .C⟩
      = some ⟨lv true true (2 * c + 3) (2 * d + 3) (Rs zs (lv false true (2 * a + 2) (2 * b + 2) L)), R0, .C⟩ := by
  have e1 : lv true true (2 * a + 1) (2 * b + 3) L
      = app Q (rep b Q (cons false (cons true (cons true (rep a Q (cons false (cons true (cons true L)))))))) := by
    simp only [lv]; rw [show 2 * b + 3 = 2 * (b + 1) + 1 by omega, rq1, rq1, rep_succ]; rfl
  rw [e1]
  obtain ⟨n1, h1⟩ := walk_all c d zs (rep b Q (cons false (cons true (cons true (rep a Q (cons false (cons true
    (cons true L))))))))
  have h2 := turn2 a b L (JR zs (JbL c d))
  obtain ⟨n3, h3⟩ := sweepN zs (O2 a b L) (JbL c d)
  have h := steps_seq trans h1 (steps_seq trans h2 h3)
  rw [o2_canon] at h
  obtain ⟨n4, h4⟩ := sweep_all c d zs false true (2 * a + 2) b L
  exact ⟨_, steps_seq trans h h4⟩

/-- A borrow through the last level and the levels `zs` (all digit 0), stopped by a level with digit 1. -/
theorem counter_borrow1 (a b c d : Nat) (zs : List (Nat × Nat)) (L : Tape) :
    ∃ n, steps n ⟨lv false false (2 * c + 2) (2 * d + 2) (Zs zs (lv false true (2 * a + 2) (2 * b + 2) L)), R0, .C⟩
      = some ⟨lv true true (2 * c + 3) (2 * d + 3) (Rs zs (lv false false (2 * a + 2) (2 * b + 2) L)), R0, .C⟩ := by
  have e1 : lv false true (2 * a + 2) (2 * b + 2) L = app Q (rep b Q (cons true (rep (a + 1) Q (cons false L)))) := by
    simp only [lv]; rw [show 2 * b + 2 = 2 * (b + 1) by omega, show 2 * a + 2 = 2 * (a + 1) by omega, rq, rq, rep_succ]
  rw [e1]
  obtain ⟨n1, h1⟩ := walk_all c d zs (rep b Q (cons true (rep (a + 1) Q (cons false L))))
  have h2 := turn1 a b L (JR zs (JbL c d))
  obtain ⟨n3, h3⟩ := sweepN zs (O1 a b L) (JbL c d)
  have h := steps_seq trans h1 (steps_seq trans h2 h3)
  rw [o1_canon] at h
  obtain ⟨n4, h4⟩ := sweep_all c d zs false false (2 * a + 2) b L
  exact ⟨_, steps_seq trans h h4⟩

/-! ## A borrow into any turn

The walk and the sweep back do not look at the tape left of the turning level, so a borrow can end at any piece of
tape that takes the head from the walk's phase (`C> 1 1 0 0 1 0 1`) back to the sweep's (`... 0 1 1 0 C>`) without
looking to its right.  `Top.lean` uses this with the pieces it proves for the left end of the tape. -/

/-- A borrow through the last level and the levels `zs` (all digit 0) that turns on the tape `T` by any piece `h`
that ends with `0 1 1` left of the head and a `0` after it. -/
theorem counter_borrow_any (c d : Nat) (zs : List (Nat × Nat)) {T X : Tape} {m : Nat}
    (h : ∀ R : Tape, steps m ⟨T, W5 (cons false (cons true R)), .C⟩ = some ⟨F3 X, R, .C⟩)
    (hX : ∃ Y, X = cons false Y) :
    ∃ n, steps n ⟨lv false false (2 * c + 2) (2 * d + 2) (Zs zs (app Q T)), R0, .C⟩
      = some ⟨lv true true (2 * c + 3) (2 * d + 3) (Rs zs X), R0, .C⟩ := by
  obtain ⟨n1, h1⟩ := walk_all c d zs T
  have h2 := h (JR zs (JbL c d))
  obtain ⟨n3, h3⟩ := sweepN zs (F3 X) (JbL c d)
  rw [sr_canon] at h3
  obtain ⟨Y, rfl⟩ := hX
  obtain ⟨Y', hY⟩ := rs_head zs Y
  have h4 : steps (4 * c + 4 * d + 11) ⟨F3 (cons false Y'), JbL c d, .C⟩ = some ⟨OL c d Y', R0, .C⟩ :=
    sweepLast c d Y'
  rw [ol_canon, ← hY] at h4
  exact ⟨_, steps_seq trans h1 (steps_seq trans h2 (steps_seq trans h3 h4))⟩

end BB6e
