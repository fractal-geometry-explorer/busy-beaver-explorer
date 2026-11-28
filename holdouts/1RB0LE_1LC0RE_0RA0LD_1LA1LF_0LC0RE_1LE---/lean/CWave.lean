import Stream
import Layers

/-! # The change of stage: the return in C, for 1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LE---

At the event where a carry leaves R, the last word, the visit reaches the blank tape after R and comes back in state
C instead of A (the even case of the a/z stream, `vb_even`).  From there it runs back left through every item, each
word answering with another state than in the chain law.  This file proves that return for every width, from the
rows of `Visit.lean`.

Words in the wave are all ones: the increment that wraps a word is the one that starts the wave there.  Below, a Q
word of w ones is `rep w [0,1,0,1]`, a P word of m ones `rep m [1,0,1,0]`. -/

namespace H64715

open TM

/-! ## Words -/

/-- A P word of ones, visited in E, when the stream after it comes back in A from a visit in B: out in C, every digit
`1010` left as `0010`.  (In B: `vb_odd`, `vb_even`.) -/
theorem pw_E (m : Nat) (x : Tape) :
    Vis .E (rep (m + 1) [true, false, true, false] (cons false (cons false x))) .C
      (rep (m + 1) [false, false, true, false] (cons true (cons false x))) :=
  v_E_10_Ba (vb_odd m x)

/-- A Q digit 1 visited in A, when the stream after it bounces a visit in E and answers a visit in A with E: out in
E, the digit `0101` left as `0100`. -/
theorem qdig {Y Y' : Tape} (hE : Vis .E Y .C Y) (hA : Vis .A Y .E Y') :
    Vis .A (cons false (cons true (cons false (cons true Y)))) .E
      (cons false (cons true (cons false (cons false Y')))) :=
  v_A_01_EcAd v_E_01_none (v_A_01_EcAe hE hA)

/-- A Q word of ones visited in A, under the same hypotheses: out in E, every digit `0101` left as `0100`. -/
theorem qw (w : Nat) {Y Y' : Tape} (hE : Vis .E Y .C Y) (hA : Vis .A Y .E Y') :
    Vis .A (rep (w + 1) [false, true, false, true] Y) .E (rep (w + 1) [false, true, false, false] Y') := by
  induction w with
  | zero => exact qdig hE hA
  | succ w ih => exact qdig v_E_01_none ih


/-! ## Rows the wave needs beyond `Visit.lean` (written by `py/rowgen.py`; each a run between nested visits, by `rfl`) -/

/-- `A> 0101 x`, nested visits E→C A→F E→A B→A: out in state E, leaving `0101 x'`. The top digit of Q in the wave, phase b = 2. -/
theorem w_qtop_F {x x1 x2 x3 x4 : Tape} (h1 : Vis .E x .C x1) (h2 : Vis .A x1 .F x2) (h3 : Vis .E x2 .A x3) (h4 : Vis .B x3 .A x4) :
    Vis .A (cons false (cons true (cons false (cons true x)))) .E (cons false (cons true (cons false (cons true x4)))) := by
  intro a L
  have s0 : steps 6 ⟨cons a L, cons false (cons true (cons false (cons true x))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons a L)))), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons false (cons true (cons a L))))
  have s1 : steps 1 ⟨cons true (cons false (cons true (cons a L))), cons false x1, .C⟩ = some ⟨cons false (cons true (cons false (cons true (cons a L)))), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons false (cons true (cons a L))))
  have s2 : steps 3 ⟨cons true (cons false (cons true (cons a L))), cons false x2, .F⟩ = some ⟨cons false (cons false (cons false (cons true (cons a L)))), x2, .E⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons false (cons false (cons true (cons a L))))
  have s3 : steps 1 ⟨cons false (cons false (cons true (cons a L))), cons false x3, .A⟩ = some ⟨cons true (cons false (cons false (cons true (cons a L)))), x3, .B⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 true (cons false (cons false (cons true (cons a L))))
  have s4 : steps 8 ⟨cons false (cons false (cons true (cons a L))), cons true x4, .A⟩ = some ⟨L, cons a (cons false (cons true (cons false (cons true x4)))), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (s4))))))))⟩

/-- `A> 0101 x`, nested visits E→C A→A B→A B→A: out in state E, leaving `0101 x'`. The top digit of Q in the wave, phase b = 3. -/
theorem w_qtop_A {x x1 x2 x3 x4 : Tape} (h1 : Vis .E x .C x1) (h2 : Vis .A x1 .A x2) (h3 : Vis .B x2 .A x3) (h4 : Vis .B x3 .A x4) :
    Vis .A (cons false (cons true (cons false (cons true x)))) .E (cons false (cons true (cons false (cons true x4)))) := by
  intro a L
  have s0 : steps 6 ⟨cons a L, cons false (cons true (cons false (cons true x))), .A⟩ = some ⟨cons false (cons true (cons false (cons true (cons a L)))), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons false (cons true (cons a L))))
  have s1 : steps 1 ⟨cons true (cons false (cons true (cons a L))), cons false x1, .C⟩ = some ⟨cons false (cons true (cons false (cons true (cons a L)))), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons false (cons true (cons a L))))
  have s2 : steps 1 ⟨cons true (cons false (cons true (cons a L))), cons false x2, .A⟩ = some ⟨cons true (cons true (cons false (cons true (cons a L)))), x2, .B⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 true (cons true (cons false (cons true (cons a L))))
  have s3 : steps 5 ⟨cons true (cons false (cons true (cons a L))), cons true x3, .A⟩ = some ⟨cons true (cons false (cons false (cons true (cons a L)))), x3, .B⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 true (cons false (cons false (cons true (cons a L))))
  have s4 : steps 8 ⟨cons false (cons false (cons true (cons a L))), cons true x4, .A⟩ = some ⟨L, cons a (cons false (cons true (cons false (cons true x4)))), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (s4))))))))⟩

/-- `B> 10 x`, nested visits B→E E→E B→C: out in state A, leaving `10 x'`. The last token of P in the wave when the next item has phase a = 2. -/
theorem w_B_10_BeEeBc {x x1 x2 x3 : Tape} (h1 : Vis .B x .E x1) (h2 : Vis .E x1 .E x2) (h3 : Vis .B x2 .C x3) :
    Vis .B (cons true (cons false x)) .A (cons true (cons false x3)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .B⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons true x1, .E⟩ = some ⟨cons false (cons false (cons a L)), x1, .E⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a L))
  have s2 : steps 3 ⟨cons false (cons a L), cons false x2, .E⟩ = some ⟨cons true (cons false (cons a L)), x2, .B⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 true (cons false (cons a L))
  have s3 : steps 2 ⟨cons false (cons a L), cons true x3, .C⟩ = some ⟨L, cons a (cons true (cons false x3)), .A⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (s3))))))⟩

/-- `B> 10 x`, nested visits B→E E→C A→D E→C A→D: out in state E, leaving `01 x'`. The block 10 after P in the wave when the next item has phase a = 3. -/
theorem w_B_10_BeEcAdEcAd {x x1 x2 x3 x4 x5 : Tape} (h1 : Vis .B x .E x1) (h2 : Vis .E x1 .C x2) (h3 : Vis .A x2 .D x3) (h4 : Vis .E x3 .C x4) (h5 : Vis .A x4 .D x5) :
    Vis .B (cons true (cons false x)) .E (cons false (cons true x5)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .B⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons true x1, .E⟩ = some ⟨cons false (cons false (cons a L)), x1, .E⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a L))
  have s2 : steps 1 ⟨cons false (cons a L), cons false x2, .C⟩ = some ⟨cons false (cons false (cons a L)), x2, .A⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons false (cons a L))
  have s3 : steps 3 ⟨cons false (cons a L), cons false x3, .D⟩ = some ⟨cons false (cons true (cons a L)), x3, .E⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons true (cons a L))
  have s4 : steps 1 ⟨cons true (cons a L), cons false x4, .C⟩ = some ⟨cons false (cons true (cons a L)), x4, .A⟩ := rfl
  obtain ⟨t5, c5⟩ := h5 false (cons true (cons a L))
  have s5 : steps 2 ⟨cons true (cons a L), cons false x5, .D⟩ = some ⟨L, cons a (cons false (cons true x5)), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (steps_seq trans s4 (steps_seq trans c5 (s5))))))))))⟩


/-! ## One item in the wave, whatever follows it

`T` is the tape after the last token of P; the only thing used about it is `hT`: a visit in B of that last token
`10` comes back in A, leaving `10` (in the chain law it would come back in A too, with a unit sent on). -/

/-- After the wave in P (phases b = 2, 3): two visits from the top digit of Q, in E or B and then in B, turn P back
into `0010 1010 (0010)^m`. -/
theorem after_E {T' : Tape} (m : Nat) : Vis .E (app [true, false] (rep (m + 2) [false, false, true, false] T')) .A
    (app [true, false, true, false, true, false] (rep (m + 1) [false, false, true, false] T')) :=
  v_E_10_Bc v_B_00_none

theorem after_B1 {T' : Tape} (m : Nat) : Vis .B (app [true, false] (rep (m + 2) [false, false, true, false] T')) .A
    (app [true, false, true, false, true, false] (rep (m + 1) [false, false, true, false] T')) :=
  v_B_10_Bc v_B_00_none

theorem after_B2 {T' : Tape} (m : Nat) : Vis .B (app [true, false, true, false, true, false] (rep (m + 1) [false, false, true, false] T')) .A
    (app [true, false, false, false, true, false, true, false, true, false] (rep m [false, false, true, false] T')) :=
  v_B_10_Bc (v_B_10_Ba (v_B_10_Bc v_B_00_none))

section
variable {T T' : Tape} (hT : Vis .B (cons true (cons false T)) .A (cons true (cons false T')))
include hT

/-- A P word of ones visited in B: out in C, every digit `1010` left as `0010`. -/
theorem pwave_B (m : Nat) : Vis .B (rep (m + 1) [true, false, true, false] T) .C (rep (m + 1) [false, false, true, false] T') := by
  induction m with
  | zero => exact v_B_10_Ba hT
  | succ m ih => exact v_B_10_Ba (v_B_10_Bc ih)

/-- The same visited in E. -/
theorem pwave_E (m : Nat) : Vis .E (rep (m + 1) [true, false, true, false] T) .C (rep (m + 1) [false, false, true, false] T') := by
  cases m with
  | zero => exact v_E_10_Ba hT
  | succ m => exact v_E_10_Ba (v_B_10_Bc (pwave_B hT m))

/-- The block `01` and P = 1^(m+1) (phase b = 1), visited in A: out in E. -/
theorem cw1 (m : Nat) : Vis .A (app [false, true] (rep (m + 1) [true, false, true, false] T)) .E
    (app [false, true, false, true, true, false] (rep m [false, false, true, false] T')) :=
  v_A_01_EcAd (pwave_E hT m) v_A_00_none

/-- The block `01` and P = 0 1^(m+1) (phase b = 2), visited in A: out in F. -/
theorem cw2 (m : Nat) : Vis .A (app [false, true, true, false, false, false] (rep (m + 1) [true, false, true, false] T)) .F
    (app [true, false] (rep (m + 2) [false, false, true, false] T')) :=
  v_A_01_EaBc l_p_E_0 (pwave_B hT (m + 1))

/-- The block `01` and P = 1 0 1^(m+1) (phase b = 3), visited in A: out in A. -/
theorem cw3 (m : Nat) : Vis .A (app [false, true, true, false, true, false, true, false, false, false]
      (rep (m + 1) [true, false, true, false] T)) .A
    (app [true, false] (rep (m + 3) [false, false, true, false] T')) :=
  v_A_01_EaBaBc (l_p_E_1 l_p_B_0) l_p_B_0 (pwave_B hT (m + 2))

/-- The top digit of Q (a 1) and the rest of the item, phase b = 2: out in E, the digit left as it was. -/
theorem top2 (m : Nat) : Vis .A (app [false, true, false, true, false, true, true, false, false, false]
      (rep (m + 1) [true, false, true, false] T)) .E
    (app [false, true, false, true, true, false, false, false, true, false, true, false, true, false]
      (rep m [false, false, true, false] T')) :=
  w_qtop_F v_E_01_none (cw2 hT m) (after_E m) (after_B2 m)

/-- The same, phase b = 3. -/
theorem top3 (m : Nat) : Vis .A (app [false, true, false, true, false, true, true, false, true, false, true, false, false, false]
      (rep (m + 1) [true, false, true, false] T)) .E
    (app [false, true, false, true, true, false, false, false, true, false, true, false, true, false]
      (rep (m + 1) [false, false, true, false] T')) :=
  w_qtop_A v_E_01_none (cw3 hT m) (after_B1 (m + 1)) (after_B2 (m + 1))


/-! ### Q in the wave: the increment of Q that wraps it

Q = 1^(w+1) (lowest digits first), then the block `01`, then P.  Phase b = 1: P = 1^(m+1); b = 2: P = 0 1^(m+1);
b = 3: P = 1 0 1^(m+1).  For b = 2, 3 the top digit of Q is written apart (Q has w + 2 digits). -/

theorem qwave1 (w m : Nat) : Vis .A (rep (w + 1) [false, true, false, true] (app [false, true] (rep (m + 1) [true, false, true, false] T))) .E
    (rep (w + 1) [false, true, false, false] (app [false, true, false, true, true, false] (rep m [false, false, true, false] T'))) :=
  qw w v_E_01_none (cw1 hT m)

theorem qwave2 (w m : Nat) : Vis .A (rep (w + 1) [false, true, false, true] (app [false, true, false, true, false, true, true, false, false, false]
      (rep (m + 1) [true, false, true, false] T))) .E
    (rep (w + 1) [false, true, false, false] (app [false, true, false, true, true, false, false, false, true, false, true, false, true, false]
      (rep m [false, false, true, false] T'))) :=
  qw w v_E_01_none (top2 hT m)

theorem qwave3 (w m : Nat) : Vis .A (rep (w + 1) [false, true, false, true] (app [false, true, false, true, false, true, true, false, true, false, true, false, false, false]
      (rep (m + 1) [true, false, true, false] T))) .E
    (rep (w + 1) [false, true, false, false] (app [false, true, false, true, true, false, false, false, true, false, true, false, true, false]
      (rep (m + 1) [false, false, true, false] T'))) :=
  qw w v_E_01_none (top3 hT m)

end


/-! ## The block `11` of an item in the wave, by its phase a

`hQ` is the wave in Q (the increment of Q that wraps it, out in E instead of D): `qwave1`, `qwave2` or `qwave3`. -/

/-- Phase a = 1 (Q all ones): one visit in B, out in A (in the chain law: E), leaving `10 11 …`. -/
theorem item_a1 {Y Y' : Tape} (hQ : Vis .A (cons false (cons true Y)) .E (cons false (cons true Y'))) :
    Vis .B (app [true, true, false, true] Y) .A (app [true, false, true, true] Y') :=
  v_B_11_EcAeBc v_E_01_none hQ v_B_01_none

/-- Phase a = 2 (Q = 0 1 1 …): one visit in B, out in D, leaving `00 …`; the first increment is the ordinary one. -/
theorem item_a2 {Y Y' : Tape} (hQ : Vis .A (app [false, true, false, true] Y) .E Y') :
    Vis .B (app [true, true, false, false, false, true] Y) .D (cons false (cons false Y')) :=
  v_B_11_EcAdEcAe v_E_00_none v_A_00_none v_E_01_none hQ

/-- Phase a = 3 (Q = 1 0 1 1 …): the first visit of the unit is the ordinary one (two increments)... -/
theorem item_a3_first {Y : Tape} :
    Vis .B (app [true, true, false, true, false, true, false, false, false, true] Y) .E
      (app [false, true, false, true, false, true, false, true, false, true] Y) :=
  l_d_B_dd v_E_01_none (l_q_A_1d v_E_00_none l_q_A_0) v_E_00_none l_q_A_0

/-- ... and the second (after a bounce in E) is the wave: out in D (in the chain law: E), leaving `00 …`. -/
theorem item_a3_wave {Y Y' : Tape} (hQ : Vis .A (app [false, true, false, true, false, true, false, true] Y) .E Y') :
    Vis .A (app [false, true, false, true, false, true, false, true, false, true] Y) .D (cons false (cons false Y')) :=
  v_A_01_EcAe v_E_01_none hQ

/-! ## How the item before sees it: the last token of its P

In each case the visit in B of the last token `10` of the P before (then the block `10`, then this item) comes back
in A, leaving `10`: that is `hT` for the item before.  The block `10` between them is left as `00` (a = 1) or `11`
(a = 2, 3): the `11` of this item has moved two cells right or left.  For a = 2, 3 the item gets two more increments
of its new first word on the way (`hE2`, `h4` … `h7`, ordinary increments of the new tape). -/

theorem nb_a1 {D D' : Tape} (hD : Vis .B D .A D') :
    Vis .B (app [true, false, true, false] D) .A (app [true, false, false, false] D') :=
  v_B_10_Bc (v_B_10_Ba hD)

theorem nb_a2 {D D' D'' : Tape} (hD : Vis .B D .D D') (hE2 : Vis .E (cons true (cons true D')) .E (cons false (cons true D''))) :
    Vis .B (app [true, false, true, false] D) .A (app [true, false, true, true] D'') :=
  w_B_10_BeEeBc (v_B_10_Bd hD) hE2 v_B_01_none

theorem nb_a3 {D D1 D2 D3 D3' D4 : Tape} (h1 : Vis .B D .E D1) (h2 : Vis .E D1 .C D1) (h3 : Vis .A D1 .D D2)
    (h4 : Vis .E D2 .C D2) (h5 : Vis .A D2 .D D3) (h6 : Vis .E D3 .C D3') (h7 : Vis .A D3' .D D4) :
    Vis .B (app [true, false, true, false] D) .A (app [true, false, true, true] D4) :=
  v_B_10_BeEcAeBc (w_B_10_BeEcAdEcAd h1 h2 h3 h4 h5) v_E_01_none (v_A_01_EcAd h6 h7) v_B_01_none

/-! ## The last item -/

/-- **The last item, phases (1, 1)**: Q and R all ones, R followed by blank tape.  The unit's first increment of Q
wraps it, the first increment of R wraps R, and the visit of the block `11` comes back in A (not in E), leaving
`10 11 00 (0100)^w 01 01 10 (0010)^m 10` and blank tape: the `11` has moved two cells right. -/
theorem last_11 (w m : Nat) :
    Vis .B (app [true, true] (rep (w + 1) [false, true, false, true]
        (app [false, true] (rep (m + 1) [true, false, true, false] blank)))) .A
      (app [true, false, true, true, false, false] (rep w [false, true, false, false]
        (app [false, true, false, true, true, false] (rep m [false, false, true, false] (app [true, false] blank))))) := by
  have hR : Vis .E (rep (m + 1) [true, false, true, false] blank) .C
      (rep (m + 1) [false, false, true, false] (cons true (cons false blank))) := by
    have h := pw_E m blank
    rwa [show cons false (cons false blank) = blank by rw [cons_false_blank, cons_false_blank]] at h
  have hc : Vis .A (cons false (cons true (rep (m + 1) [true, false, true, false] blank))) .E
      (cons false (cons true (cons false (cons true (cons true (cons false
        (rep m [false, false, true, false] (cons true (cons false blank))))))))) :=
    v_A_01_EcAd hR v_A_00_none
  exact v_B_11_EcAeBc v_E_01_none (qw w v_E_01_none hc) v_B_01_none

end H64715
