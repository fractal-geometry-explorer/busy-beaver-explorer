import CWave

/-! # The C-wave law, for 1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LE---

At a change of stage (`py/stage_change.py`) the carry leaves R, the last word, the head meets the blank tape after R
and comes back in state C: the C-wave.  `cwave` proves what the wave leaves behind, for any number of items.

An item is `11 Q 01 P 10` (Q digits `0001`/`0101`, P digits `1000`/`1010`, lowest digit first).  At the change of
stage every item is in the last unit of its chain-law step, so its words are all ones but for the lowest digits: Q is
`qIn a` (1...1, 01...1 or 101...1 for the phase a = 1, 2, 3 of the unit: the increment of Q that wraps) and P is
`pIn b` likewise.  The last item's P is R, with blank tape after it.  The wave rewrites every item as `newItem`:

- Q becomes 0 (a = 1) or 2 (a >= 2), and P 0 (b = 1) or 2 (b >= 2);
- the `11` of the item moves two cells right if a = 1 and two left if a >= 2, and its `01` two right if b = 1 and two
  left if b >= 2; the widths of the words change by these moves (`qNew`, `pNew`);
- R keeps its width (b = 1) or gains a digit (b >= 2), and its top digit is 1.

This is the rule that `stage_change.py` checks cell by cell, now proved for every phase and every width with Q at
least 2 and P at least 3 digits wide.  The proof goes item by item from the right: the visit of an item is the visit
of the next item (`hT`) inside a few rows of the visit law, and depends only on the item's own phases and on whether
the next item has a = 1 (`Kd`), whose `11` then moves into the item. -/

namespace H64715
open TM

/-! ## Reading the new tape in the grammar -/

theorem enc_q1 (n : Nat) (X : Tape) : enc qd (List.replicate n true) X = rep n [false, true, false, true] X := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, enc, ih]; rfl
theorem enc_q0 (n : Nat) (X : Tape) : enc qd (List.replicate n false) X = rep n [false, false, false, true] X := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, enc, ih]; rfl
theorem enc_p1 (n : Nat) (X : Tape) : enc pd (List.replicate n true) X = rep n [true, false, true, false] X := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, enc, ih]; rfl
theorem enc_p0 (n : Nat) (X : Tape) : enc pd (List.replicate n false) X = rep n [true, false, false, false] X := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, enc, ih]; rfl
theorem enc_append (d : Bool → List Bool) (u v : List Bool) (X : Tape) : enc d (u ++ v) X = enc d u (enc d v X) := by
  induction u with
  | nil => rfl
  | cons b u ih => simp only [List.cons_append, enc, ih]

theorem vis_out {q r : St} {x y y' : Tape} (h : Vis q x r y) (e : y = y') : Vis q x r y' := e ▸ h
theorem vis_in {q r : St} {x x' y : Tape} (h : Vis q x r y) (e : x = x') : Vis q x' r y := e ▸ h


/-! ## A normal form for the tapes of the new items

Both sides of every equation below are rewritten to cells (`cons`) and repeats with bare counts; a repeat of `0100`
behind `00` becomes a repeat of `0001` in front of `00`, a repeat of `0010` behind `10` a repeat of `1000` in front
of `10`, and copies of a repeat's word after it move in front of it.  Then the two sides are the same term. -/

theorem nf_q (n : Nat) (s : Tape) : cons false (cons false (rep n [false, true, false, false] s)) =
    rep n [false, false, false, true] (cons false (cons false s)) :=
  rep_rotate n [false, false] [false, true, false, false] [false, false, false, true] rfl s
theorem nf_p (n : Nat) (s : Tape) : cons true (cons false (rep n [false, false, true, false] s)) =
    rep n [true, false, false, false] (cons true (cons false s)) :=
  rep_rotate n [true, false] [false, false, true, false] [true, false, false, false] rfl s
theorem nf_back (n : Nat) (a b c d : Bool) (s : Tape) :
    rep n [a, b, c, d] (cons a (cons b (cons c (cons d s)))) = cons a (cons b (cons c (cons d (rep n [a, b, c, d] s)))) :=
  (rep_rotate n [a, b, c, d] [a, b, c, d] [a, b, c, d] rfl s).symm

macro "tnorm" : tactic => `(tactic| simp only [app_cons, app_nil, rep_succ, nf_q, nf_p, nf_back])

inductive Ph where
  | one | two | three

inductive Kd where
  | one | more

def kd : Ph → Kd
  | .one => .one
  | _ => .more

def nextT : Kd → Tape → Tape
  | .one, N => app [false, false, true, false] N
  | .more, N => N

def qIn : Ph → Nat → List Bool
  | .one, w => List.replicate (w + 2) true
  | .two, w => false :: List.replicate (w + 1) true
  | .three, w => true :: false :: List.replicate w true

def pIn : Ph → Nat → List Bool
  | .one, m => List.replicate (m + 3) true
  | .two, m => false :: List.replicate (m + 2) true
  | .three, m => true :: false :: List.replicate (m + 1) true

def qNew : Ph → Ph → Nat → List Bool
  | .one, .one, w => List.replicate (w + 2) false
  | .one, _, w => List.replicate (w + 1) false
  | _, .one, w => false :: true :: List.replicate (w + 1) false
  | _, _, w => false :: true :: List.replicate w false

def pNew : Ph → Kd → Nat → List Bool
  | .one, .one, m => List.replicate (m + 3) false
  | .one, .more, m => List.replicate (m + 2) false
  | _, .one, m => false :: true :: List.replicate (m + 2) false
  | _, .more, m => false :: true :: List.replicate (m + 1) false

def inItem (a b : Ph) (w m : Nat) (T : Tape) : Tape :=
  app [true, true] (enc qd (qIn a w) (app [false, true] (enc pd (pIn b m) T)))

def newItem (a b : Ph) (K : Kd) (w m : Nat) (N : Tape) : Tape :=
  app [true, true] (enc qd (qNew a b w) (app [false, true] (enc pd (pNew b K m) (app [true, false] N))))


section
variable {T T' : Tape} (hT : Vis .B (cons true (cons false T)) .A (cons true (cons false T')))
include hT

theorem qwave2' (w m : Nat) : Vis .A (rep (w + 2) [false, true, false, true] (app [false, true, true, false, false, false]
      (rep (m + 1) [true, false, true, false] T))) .E
    (rep (w + 1) [false, true, false, false] (app [false, true, false, true, true, false, false, false, true, false, true, false, true, false]
      (rep m [false, false, true, false] T'))) := by
  rw [show w + 2 = w + 1 + 1 from rfl, ← rep_app_comm]; exact qwave2 hT w m

theorem qwave3' (w m : Nat) : Vis .A (rep (w + 2) [false, true, false, true] (app [false, true, true, false, true, false, true, false, false, false]
      (rep (m + 1) [true, false, true, false] T))) .E
    (rep (w + 1) [false, true, false, false] (app [false, true, false, true, true, false, false, false, true, false, true, false, true, false]
      (rep (m + 1) [false, false, true, false] T'))) := by
  rw [show w + 2 = w + 1 + 1 from rfl, ← rep_app_comm]; exact qwave3 hT w m
end


theorem shD1 (w m : Nat) (X : Tape) :
    cons false (cons false (rep (w + 2) [false, true, false, false] (app [false, true, false, true, true, false]
      (rep (m + 2) [false, false, true, false] X))))
    = rep (w + 3) [false, false, false, true] (app [false, true, true, false] (rep (m + 2) [false, false, true, false] X)) := by
  tnorm

theorem shD2 (w m : Nat) (X : Tape) :
    cons false (cons false (rep (w + 1) [false, true, false, false]
      (app [false, true, false, true, true, false, false, false, true, false, true, false, true, false]
      (rep (m + 1) [false, false, true, false] X))))
    = rep (w + 2) [false, false, false, true] (app [false, true, true, false, false, false, true, false, true, false, true, false]
      (rep (m + 1) [false, false, true, false] X)) := by
  tnorm

section
variable {T N : Tape} (hT : Vis .B (app [true, false] T) .A (app [true, false] (nextT .one N)))
include hT

theorem it_one_one_one (w m : Nat) : Vis .B (app [true, false, true, false] (inItem .one .one w m T)) .A
    (app [true, false] (nextT (kd .one) (newItem .one .one .one w m N))) := by
  have h := nb_a1 (item_a1 (qwave1 hT (w + 1) (m + 2)))
  simp only [inItem, newItem, kd, qIn, qNew, pIn, pNew, nextT, enc_q1, enc_q0, enc_p1, enc_p0, enc, qd, pd] at h ⊢
  refine vis_out h ?_
  tnorm

theorem it_one_two_one (w m : Nat) : Vis .B (app [true, false, true, false] (inItem .one .two w m T)) .A
    (app [true, false] (nextT (kd .one) (newItem .one .two .one w m N))) := by
  have h := nb_a1 (item_a1 (qwave2' hT w (m + 1)))
  simp only [inItem, newItem, kd, qIn, qNew, pIn, pNew, nextT, enc_q1, enc_q0, enc_p1, enc_p0, enc, qd, pd] at h ⊢
  refine vis_out h ?_
  tnorm

theorem it_one_three_one (w m : Nat) : Vis .B (app [true, false, true, false] (inItem .one .three w m T)) .A
    (app [true, false] (nextT (kd .one) (newItem .one .three .one w m N))) := by
  have h := nb_a1 (item_a1 (qwave3' hT w m))
  simp only [inItem, newItem, kd, qIn, qNew, pIn, pNew, nextT, enc_q1, enc_q0, enc_p1, enc_p0, enc, qd, pd] at h ⊢
  refine vis_out h ?_
  tnorm

theorem it_two_one_one (w m : Nat) : Vis .B (app [true, false, true, false] (inItem .two .one w m T)) .A
    (app [true, false] (nextT (kd .two) (newItem .two .one .one w m N))) := by
  have hD := vis_out (item_a2 (qwave1 hT (w + 1) (m + 2))) (shD1 w m _)
  have h := nb_a2 hD (v_E_11_EcAdEcAd v_E_00_none l_q_A_0 v_E_01_none (l_q_A_1d v_E_00_none l_q_A_0))
  simp only [inItem, newItem, kd, qIn, qNew, pIn, pNew, nextT, enc_q1, enc_q0, enc_p1, enc_p0, enc, qd, pd] at h ⊢
  refine vis_out h ?_
  tnorm

theorem it_two_two_one (w m : Nat) : Vis .B (app [true, false, true, false] (inItem .two .two w m T)) .A
    (app [true, false] (nextT (kd .two) (newItem .two .two .one w m N))) := by
  have hD := vis_out (item_a2 (qwave2' hT w (m + 1))) (shD2 w m _)
  have h := nb_a2 hD (v_E_11_EcAdEcAd v_E_00_none l_q_A_0 v_E_01_none (l_q_A_1d v_E_00_none l_q_A_0))
  simp only [inItem, newItem, kd, qIn, qNew, pIn, pNew, nextT, enc_q1, enc_q0, enc_p1, enc_p0, enc, qd, pd] at h ⊢
  refine vis_out h ?_
  tnorm

theorem it_two_three_one (w m : Nat) : Vis .B (app [true, false, true, false] (inItem .two .three w m T)) .A
    (app [true, false] (nextT (kd .two) (newItem .two .three .one w m N))) := by
  have hD := vis_out (item_a2 (qwave3' hT w m)) (shD2 w m _)
  have h := nb_a2 hD (v_E_11_EcAdEcAd v_E_00_none l_q_A_0 v_E_01_none (l_q_A_1d v_E_00_none l_q_A_0))
  simp only [inItem, newItem, kd, qIn, qNew, pIn, pNew, nextT, enc_q1, enc_q0, enc_p1, enc_p0, enc, qd, pd] at h ⊢
  refine vis_out h ?_
  tnorm

theorem it_three_one_one (w m : Nat) : Vis .B (app [true, false, true, false] (inItem .three .one w m T)) .A
    (app [true, false] (nextT (kd .three) (newItem .three .one .one w m N))) := by
  have h3 := vis_out (item_a3_wave (qwave1 hT (w + 1) (m + 2))) (shD1 w m _)
  have h := nb_a3 item_a3_first v_E_01_none h3 v_E_00_none l_q_A_0 v_E_01_none (l_q_A_1d v_E_00_none l_q_A_0)
  simp only [inItem, newItem, kd, qIn, qNew, pIn, pNew, nextT, enc_q1, enc_q0, enc_p1, enc_p0, enc, qd, pd] at h ⊢
  refine vis_out h ?_
  tnorm

theorem it_three_two_one (w m : Nat) : Vis .B (app [true, false, true, false] (inItem .three .two w m T)) .A
    (app [true, false] (nextT (kd .three) (newItem .three .two .one w m N))) := by
  have h3 := vis_out (item_a3_wave (qwave2' hT w (m + 1))) (shD2 w m _)
  have h := nb_a3 item_a3_first v_E_01_none h3 v_E_00_none l_q_A_0 v_E_01_none (l_q_A_1d v_E_00_none l_q_A_0)
  simp only [inItem, newItem, kd, qIn, qNew, pIn, pNew, nextT, enc_q1, enc_q0, enc_p1, enc_p0, enc, qd, pd] at h ⊢
  refine vis_out h ?_
  tnorm

theorem it_three_three_one (w m : Nat) : Vis .B (app [true, false, true, false] (inItem .three .three w m T)) .A
    (app [true, false] (nextT (kd .three) (newItem .three .three .one w m N))) := by
  have h3 := vis_out (item_a3_wave (qwave3' hT w m)) (shD2 w m _)
  have h := nb_a3 item_a3_first v_E_01_none h3 v_E_00_none l_q_A_0 v_E_01_none (l_q_A_1d v_E_00_none l_q_A_0)
  simp only [inItem, newItem, kd, qIn, qNew, pIn, pNew, nextT, enc_q1, enc_q0, enc_p1, enc_p0, enc, qd, pd] at h ⊢
  refine vis_out h ?_
  tnorm

end

section
variable {T N : Tape} (hT : Vis .B (app [true, false] T) .A (app [true, false] (nextT .more N)))
include hT

theorem it_one_one_more (w m : Nat) : Vis .B (app [true, false, true, false] (inItem .one .one w m T)) .A
    (app [true, false] (nextT (kd .one) (newItem .one .one .more w m N))) := by
  have h := nb_a1 (item_a1 (qwave1 hT (w + 1) (m + 2)))
  simp only [inItem, newItem, kd, qIn, qNew, pIn, pNew, nextT, enc_q1, enc_q0, enc_p1, enc_p0, enc, qd, pd] at h ⊢
  refine vis_out h ?_
  tnorm

theorem it_one_two_more (w m : Nat) : Vis .B (app [true, false, true, false] (inItem .one .two w m T)) .A
    (app [true, false] (nextT (kd .one) (newItem .one .two .more w m N))) := by
  have h := nb_a1 (item_a1 (qwave2' hT w (m + 1)))
  simp only [inItem, newItem, kd, qIn, qNew, pIn, pNew, nextT, enc_q1, enc_q0, enc_p1, enc_p0, enc, qd, pd] at h ⊢
  refine vis_out h ?_
  tnorm

theorem it_one_three_more (w m : Nat) : Vis .B (app [true, false, true, false] (inItem .one .three w m T)) .A
    (app [true, false] (nextT (kd .one) (newItem .one .three .more w m N))) := by
  have h := nb_a1 (item_a1 (qwave3' hT w m))
  simp only [inItem, newItem, kd, qIn, qNew, pIn, pNew, nextT, enc_q1, enc_q0, enc_p1, enc_p0, enc, qd, pd] at h ⊢
  refine vis_out h ?_
  tnorm

theorem it_two_one_more (w m : Nat) : Vis .B (app [true, false, true, false] (inItem .two .one w m T)) .A
    (app [true, false] (nextT (kd .two) (newItem .two .one .more w m N))) := by
  have hD := vis_out (item_a2 (qwave1 hT (w + 1) (m + 2))) (shD1 w m _)
  have h := nb_a2 hD (v_E_11_EcAdEcAd v_E_00_none l_q_A_0 v_E_01_none (l_q_A_1d v_E_00_none l_q_A_0))
  simp only [inItem, newItem, kd, qIn, qNew, pIn, pNew, nextT, enc_q1, enc_q0, enc_p1, enc_p0, enc, qd, pd] at h ⊢
  refine vis_out h ?_
  tnorm

theorem it_two_two_more (w m : Nat) : Vis .B (app [true, false, true, false] (inItem .two .two w m T)) .A
    (app [true, false] (nextT (kd .two) (newItem .two .two .more w m N))) := by
  have hD := vis_out (item_a2 (qwave2' hT w (m + 1))) (shD2 w m _)
  have h := nb_a2 hD (v_E_11_EcAdEcAd v_E_00_none l_q_A_0 v_E_01_none (l_q_A_1d v_E_00_none l_q_A_0))
  simp only [inItem, newItem, kd, qIn, qNew, pIn, pNew, nextT, enc_q1, enc_q0, enc_p1, enc_p0, enc, qd, pd] at h ⊢
  refine vis_out h ?_
  tnorm

theorem it_two_three_more (w m : Nat) : Vis .B (app [true, false, true, false] (inItem .two .three w m T)) .A
    (app [true, false] (nextT (kd .two) (newItem .two .three .more w m N))) := by
  have hD := vis_out (item_a2 (qwave3' hT w m)) (shD2 w m _)
  have h := nb_a2 hD (v_E_11_EcAdEcAd v_E_00_none l_q_A_0 v_E_01_none (l_q_A_1d v_E_00_none l_q_A_0))
  simp only [inItem, newItem, kd, qIn, qNew, pIn, pNew, nextT, enc_q1, enc_q0, enc_p1, enc_p0, enc, qd, pd] at h ⊢
  refine vis_out h ?_
  tnorm

theorem it_three_one_more (w m : Nat) : Vis .B (app [true, false, true, false] (inItem .three .one w m T)) .A
    (app [true, false] (nextT (kd .three) (newItem .three .one .more w m N))) := by
  have h3 := vis_out (item_a3_wave (qwave1 hT (w + 1) (m + 2))) (shD1 w m _)
  have h := nb_a3 item_a3_first v_E_01_none h3 v_E_00_none l_q_A_0 v_E_01_none (l_q_A_1d v_E_00_none l_q_A_0)
  simp only [inItem, newItem, kd, qIn, qNew, pIn, pNew, nextT, enc_q1, enc_q0, enc_p1, enc_p0, enc, qd, pd] at h ⊢
  refine vis_out h ?_
  tnorm

theorem it_three_two_more (w m : Nat) : Vis .B (app [true, false, true, false] (inItem .three .two w m T)) .A
    (app [true, false] (nextT (kd .three) (newItem .three .two .more w m N))) := by
  have h3 := vis_out (item_a3_wave (qwave2' hT w (m + 1))) (shD2 w m _)
  have h := nb_a3 item_a3_first v_E_01_none h3 v_E_00_none l_q_A_0 v_E_01_none (l_q_A_1d v_E_00_none l_q_A_0)
  simp only [inItem, newItem, kd, qIn, qNew, pIn, pNew, nextT, enc_q1, enc_q0, enc_p1, enc_p0, enc, qd, pd] at h ⊢
  refine vis_out h ?_
  tnorm

theorem it_three_three_more (w m : Nat) : Vis .B (app [true, false, true, false] (inItem .three .three w m T)) .A
    (app [true, false] (nextT (kd .three) (newItem .three .three .more w m N))) := by
  have h3 := vis_out (item_a3_wave (qwave3' hT w m)) (shD2 w m _)
  have h := nb_a3 item_a3_first v_E_01_none h3 v_E_00_none l_q_A_0 v_E_01_none (l_q_A_1d v_E_00_none l_q_A_0)
  simp only [inItem, newItem, kd, qIn, qNew, pIn, pNew, nextT, enc_q1, enc_q0, enc_p1, enc_p0, enc, qd, pd] at h ⊢
  refine vis_out h ?_
  tnorm

end

/-! ## The whole C-wave, by induction on the items -/

/-- `it_all`: one item, whichever its phases and the kind of the item after it. -/
theorem it_all {T N : Tape} (a b : Ph) (K : Kd) (w m : Nat)
    (hT : Vis .B (app [true, false] T) .A (app [true, false] (nextT K N))) :
    Vis .B (app [true, false, true, false] (inItem a b w m T)) .A
      (app [true, false] (nextT (kd a) (newItem a b K w m N))) := by
  cases K <;> cases a <;> cases b
  · exact it_one_one_one hT w m
  · exact it_one_two_one hT w m
  · exact it_one_three_one hT w m
  · exact it_two_one_one hT w m
  · exact it_two_two_one hT w m
  · exact it_two_three_one hT w m
  · exact it_three_one_one hT w m
  · exact it_three_two_one hT w m
  · exact it_three_three_one hT w m
  · exact it_one_one_more hT w m
  · exact it_one_two_more hT w m
  · exact it_one_three_more hT w m
  · exact it_two_one_more hT w m
  · exact it_two_two_more hT w m
  · exact it_two_three_more hT w m
  · exact it_three_one_more hT w m
  · exact it_three_two_more hT w m
  · exact it_three_three_more hT w m

/-- An item: the phases `(a, b)` of its unit at the change of stage and its widths `w + 2` (Q) and `m + 3` (P). -/
structure WItem where
  a : Ph
  b : Ph
  w : Nat
  m : Nat

/-- The items before the change of stage, then blank tape (the last item's P is R). -/
def chainIn : List WItem → Tape
  | [] => blank
  | x :: xs => app [true, false] (inItem x.a x.b x.w x.m (chainIn xs))

/-- How the first of the items moves: `one` if its `11` moves right. -/
def kindOf : List WItem → Kd
  | [] => .more
  | x :: _ => kd x.a

/-- The items after the change of stage. -/
def chainOut : List WItem → Tape
  | [] => app [true, false] blank
  | x :: xs => newItem x.a x.b (kindOf xs) x.w x.m (chainOut xs)

theorem last_top : Vis .B (app [true, false] blank) .A (app [true, false] (nextT .more (app [true, false] blank))) := by
  have h : Vis .B (cons false (cons false blank)) .C (cons true (cons false blank)) := v_B_00_none
  rw [show cons false (cons false blank) = blank by rw [cons_false_blank, cons_false_blank]] at h
  exact v_B_10_Bc h

/-- **The C-wave law.**  The head enters the items in state `B`, two cells before the first one; it leaves them in
state `A`, and every item has been rewritten as `newItem` says. -/
theorem cwave (xs : List WItem) :
    Vis .B (app [true, false] (chainIn xs)) .A (app [true, false] (nextT (kindOf xs) (chainOut xs))) := by
  induction xs with
  | nil => exact last_top
  | cons x xs ih =>
    have h := it_all x.a x.b (kindOf xs) x.w x.m ih
    simp only [chainIn, chainOut, kindOf, app_app, List.cons_append, List.nil_append] at h ⊢
    exact h

end H64715
