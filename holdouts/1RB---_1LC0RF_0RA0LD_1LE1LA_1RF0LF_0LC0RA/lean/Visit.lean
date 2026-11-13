import Machine

/-! # Visit laws of 1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA

`Vis q x r x'`: the head enters the stream `x` from the left in state `q` (on its first cell) and the first time it
leaves `x` to the left it is in state `r` and the stream is `x'`; the cell it lands on and everything left of it are
untouched.  Every theorem below is one row of the token-level law (tokens of 2 cells, mined from the run by
`py/laws.py`, written by `py/gen_visit.py`): what one visit does to a stream that starts with the token, given what
the nested visits of the rest of the stream do.  The rows are exact for every stream (the hypotheses are about the
rest of the stream only), so they can be composed by induction into laws for whole counters. -/

namespace H22247

open TM

/-- One visit of the stream `x` in state `q`: back out on the left in state `r`, leaving `x'`. -/
def Vis (q : St) (x : Tape) (r : St) (x' : Tape) : Prop :=
  ∀ (a : Bool) (L : Tape), ∃ t, steps t ⟨cons a L, x, q⟩ = some ⟨L, cons a x', r⟩

/-- `A> 00 x`, no nested visit: out in state D, leaving `01 x'`.  (In the run: 37732 times in 3·10^7 steps, first at step 29.) -/
theorem v_A_00_none {x : Tape}  :
    Vis .A (cons false (cons false x)) .D (cons false (cons true x)) := by
  intro a L
  have s0 : steps 3 ⟨cons a L, cons false (cons false x), .A⟩ = some ⟨L, cons a (cons false (cons true x)), .D⟩ := rfl
  exact ⟨_, s0⟩

/-- `A> 01 x`, nested visits F→C A→A B→E B→E: out in state C, leaving `00 x'`.  (In the run: 3 times in 3·10^7 steps, first at step 157.) -/
theorem v_A_01_FcAaBeBe {x x1 x2 x3 x4 : Tape} (h1 : Vis .F x .C x1) (h2 : Vis .A x1 .A x2) (h3 : Vis .B x2 .E x3) (h4 : Vis .B x3 .E x4) :
    Vis .A (cons false (cons true x)) .C (cons false (cons false x4)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .F⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons true (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons a L))
  have s2 : steps 1 ⟨cons true (cons a L), cons false x2, .A⟩ = some ⟨cons true (cons true (cons a L)), x2, .B⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 true (cons true (cons a L))
  have s3 : steps 3 ⟨cons true (cons a L), cons true x3, .E⟩ = some ⟨cons true (cons false (cons a L)), x3, .B⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 true (cons false (cons a L))
  have s4 : steps 2 ⟨cons false (cons a L), cons true x4, .E⟩ = some ⟨L, cons a (cons false (cons false x4)), .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (s4))))))))⟩

/-- `A> 01 x`, nested visits F→C A→C A→D: out in state F, leaving `01 x'`.  (In the run: 9540 times in 3·10^7 steps, first at step 163.) -/
theorem v_A_01_FcAcAd {x x1 x2 x3 : Tape} (h1 : Vis .F x .C x1) (h2 : Vis .A x1 .C x2) (h3 : Vis .A x2 .D x3) :
    Vis .A (cons false (cons true x)) .F (cons false (cons true x3)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .F⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons true (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons a L))
  have s2 : steps 1 ⟨cons true (cons a L), cons false x2, .C⟩ = some ⟨cons false (cons true (cons a L)), x2, .A⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons true (cons a L))
  have s3 : steps 2 ⟨cons true (cons a L), cons false x3, .D⟩ = some ⟨L, cons a (cons false (cons true x3)), .F⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (s3))))))⟩

/-- `A> 01 x`, nested visits F→C A→D: out in state F, leaving `01 x'`.  (In the run: 28177 times in 3·10^7 steps, first at step 63.) -/
theorem v_A_01_FcAd {x x1 x2 : Tape} (h1 : Vis .F x .C x1) (h2 : Vis .A x1 .D x2) :
    Vis .A (cons false (cons true x)) .F (cons false (cons true x2)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .F⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons true (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons a L))
  have s2 : steps 2 ⟨cons true (cons a L), cons false x2, .D⟩ = some ⟨L, cons a (cons false (cons true x2)), .F⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `A> 01 x`, nested visits F→C A→E F→E B→E: out in state C, leaving `00 x'`.  (In the run: 2 times in 3·10^7 steps, first at step 3399.) -/
theorem v_A_01_FcAeFeBe {x x1 x2 x3 x4 : Tape} (h1 : Vis .F x .C x1) (h2 : Vis .A x1 .E x2) (h3 : Vis .F x2 .E x3) (h4 : Vis .B x3 .E x4) :
    Vis .A (cons false (cons true x)) .C (cons false (cons false x4)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .F⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons true (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons a L))
  have s2 : steps 1 ⟨cons true (cons a L), cons false x2, .E⟩ = some ⟨cons true (cons true (cons a L)), x2, .F⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 true (cons true (cons a L))
  have s3 : steps 3 ⟨cons true (cons a L), cons true x3, .E⟩ = some ⟨cons true (cons false (cons a L)), x3, .B⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 true (cons false (cons a L))
  have s4 : steps 2 ⟨cons false (cons a L), cons true x4, .E⟩ = some ⟨L, cons a (cons false (cons false x4)), .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (s4))))))))⟩

/-- `A> 01 x`, nested visits F→C A→F: out in state D, leaving `00 x'`.  (In the run: 27011 times in 3·10^7 steps, first at step 1205.) -/
theorem v_A_01_FcAf {x x1 x2 : Tape} (h1 : Vis .F x .C x1) (h2 : Vis .A x1 .F x2) :
    Vis .A (cons false (cons true x)) .D (cons false (cons false x2)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .F⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons true (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons a L))
  have s2 : steps 2 ⟨cons true (cons a L), cons false x2, .F⟩ = some ⟨L, cons a (cons false (cons false x2)), .D⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `A> 01 x`, nested visits F→E F→C: out in state A, leaving `10 x'`.  (In the run: 6 times in 3·10^7 steps, first at step 125.) -/
theorem v_A_01_FeFc {x x1 x2 : Tape} (h1 : Vis .F x .E x1) (h2 : Vis .F x1 .C x2) :
    Vis .A (cons false (cons true x)) .A (cons true (cons false x2)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .F⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .E⟩ = some ⟨cons true (cons true (cons a L)), x1, .F⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 true (cons true (cons a L))
  have s2 : steps 2 ⟨cons true (cons a L), cons true x2, .C⟩ = some ⟨L, cons a (cons true (cons false x2)), .A⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `A> 01 x`, nested visits F→E F→E B→C: out in state E, leaving `10 x'`.  (In the run: 1 times in 3·10^7 steps, first at step 7213.) -/
theorem v_A_01_FeFeBc {x x1 x2 x3 : Tape} (h1 : Vis .F x .E x1) (h2 : Vis .F x1 .E x2) (h3 : Vis .B x2 .C x3) :
    Vis .A (cons false (cons true x)) .E (cons true (cons false x3)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .F⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .E⟩ = some ⟨cons true (cons true (cons a L)), x1, .F⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 true (cons true (cons a L))
  have s2 : steps 3 ⟨cons true (cons a L), cons true x2, .E⟩ = some ⟨cons true (cons false (cons a L)), x2, .B⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 true (cons false (cons a L))
  have s3 : steps 2 ⟨cons false (cons a L), cons true x3, .C⟩ = some ⟨L, cons a (cons true (cons false x3)), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (s3))))))⟩

/-- `A> 01 x`, nested visits F→E F→E B→E: out in state C, leaving `00 x'`.  (In the run: 10699 times in 3·10^7 steps, first at step 293.) -/
theorem v_A_01_FeFeBe {x x1 x2 x3 : Tape} (h1 : Vis .F x .E x1) (h2 : Vis .F x1 .E x2) (h3 : Vis .B x2 .E x3) :
    Vis .A (cons false (cons true x)) .C (cons false (cons false x3)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .F⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .E⟩ = some ⟨cons true (cons true (cons a L)), x1, .F⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 true (cons true (cons a L))
  have s2 : steps 3 ⟨cons true (cons a L), cons true x2, .E⟩ = some ⟨cons true (cons false (cons a L)), x2, .B⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 true (cons false (cons a L))
  have s3 : steps 2 ⟨cons false (cons a L), cons true x3, .E⟩ = some ⟨L, cons a (cons false (cons false x3)), .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (s3))))))⟩

/-- `A> 01 x`, nested visits F→E F→E B→F A→F B→C: out in state E, leaving `10 x'`.  (In the run: 1 times in 3·10^7 steps, first at step 3119.) -/
theorem v_A_01_FeFeBfAfBc {x x1 x2 x3 x4 x5 : Tape} (h1 : Vis .F x .E x1) (h2 : Vis .F x1 .E x2) (h3 : Vis .B x2 .F x3) (h4 : Vis .A x3 .F x4) (h5 : Vis .B x4 .C x5) :
    Vis .A (cons false (cons true x)) .E (cons true (cons false x5)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .F⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .E⟩ = some ⟨cons true (cons true (cons a L)), x1, .F⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 true (cons true (cons a L))
  have s2 : steps 3 ⟨cons true (cons a L), cons true x2, .E⟩ = some ⟨cons true (cons false (cons a L)), x2, .B⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 true (cons false (cons a L))
  have s3 : steps 1 ⟨cons false (cons a L), cons true x3, .F⟩ = some ⟨cons false (cons false (cons a L)), x3, .A⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons false (cons a L))
  have s4 : steps 3 ⟨cons false (cons a L), cons false x4, .F⟩ = some ⟨cons true (cons false (cons a L)), x4, .B⟩ := rfl
  obtain ⟨t5, c5⟩ := h5 true (cons false (cons a L))
  have s5 : steps 2 ⟨cons false (cons a L), cons true x5, .C⟩ = some ⟨L, cons a (cons true (cons false x5)), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (steps_seq trans s4 (steps_seq trans c5 (s5))))))))))⟩

/-- `A> 01 x`, nested visits F→E F→F A→F: out in state D, leaving `00 x'`.  (In the run: 1 times in 3·10^7 steps, first at step 1133.) -/
theorem v_A_01_FeFfAf {x x1 x2 x3 : Tape} (h1 : Vis .F x .E x1) (h2 : Vis .F x1 .F x2) (h3 : Vis .A x2 .F x3) :
    Vis .A (cons false (cons true x)) .D (cons false (cons false x3)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .F⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .E⟩ = some ⟨cons true (cons true (cons a L)), x1, .F⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 true (cons true (cons a L))
  have s2 : steps 1 ⟨cons true (cons a L), cons true x2, .F⟩ = some ⟨cons false (cons true (cons a L)), x2, .A⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons true (cons a L))
  have s3 : steps 2 ⟨cons true (cons a L), cons false x3, .F⟩ = some ⟨L, cons a (cons false (cons false x3)), .D⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (s3))))))⟩

/-- `A> 01 x`, nested visits F→F: out in state D, leaving `00 x'`.  (In the run: 1 times in 3·10^7 steps, first at step 117995.) -/
theorem v_A_01_Ff {x x1 : Tape} (h1 : Vis .F x .F x1) :
    Vis .A (cons false (cons true x)) .D (cons false (cons false x1)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .F⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 2 ⟨cons true (cons a L), cons false x1, .F⟩ = some ⟨L, cons a (cons false (cons false x1)), .D⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `B> 00 x`, no nested visit: out in state C, leaving `10 x'`.  (In the run: 43866 times in 3·10^7 steps, first at step 1.) -/
theorem v_B_00_none {x : Tape}  :
    Vis .B (cons false (cons false x)) .C (cons true (cons false x)) := by
  intro a L
  have s0 : steps 1 ⟨cons a L, cons false (cons false x), .B⟩ = some ⟨L, cons a (cons true (cons false x)), .C⟩ := rfl
  exact ⟨_, s0⟩

/-- `B> 01 x`, no nested visit: out in state C, leaving `11 x'`.  (In the run: 10708 times in 3·10^7 steps, first at step 77.) -/
theorem v_B_01_none {x : Tape}  :
    Vis .B (cons false (cons true x)) .C (cons true (cons true x)) := by
  intro a L
  have s0 : steps 1 ⟨cons a L, cons false (cons true x), .B⟩ = some ⟨L, cons a (cons true (cons true x)), .C⟩ := rfl
  exact ⟨_, s0⟩

/-- `B> 10 x`, nested visits B→C: out in state E, leaving `10 x'`.  (In the run: 55707 times in 3·10^7 steps, first at step 13.) -/
theorem v_B_10_Bc {x x1 : Tape} (h1 : Vis .B x .C x1) :
    Vis .B (cons true (cons false x)) .E (cons true (cons false x1)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .B⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 2 ⟨cons false (cons a L), cons true x1, .C⟩ = some ⟨L, cons a (cons true (cons false x1)), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `B> 10 x`, nested visits B→D F→C A→D: out in state F, leaving `01 x'`.  (In the run: 1 times in 3·10^7 steps, first at step 3041.) -/
theorem v_B_10_BdFcAd {x x1 x2 x3 : Tape} (h1 : Vis .B x .D x1) (h2 : Vis .F x1 .C x2) (h3 : Vis .A x2 .D x3) :
    Vis .B (cons true (cons false x)) .F (cons false (cons true x3)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .B⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 3 ⟨cons false (cons a L), cons true x1, .D⟩ = some ⟨cons false (cons true (cons a L)), x1, .F⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons a L))
  have s2 : steps 1 ⟨cons true (cons a L), cons false x2, .C⟩ = some ⟨cons false (cons true (cons a L)), x2, .A⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons true (cons a L))
  have s3 : steps 2 ⟨cons true (cons a L), cons false x3, .D⟩ = some ⟨L, cons a (cons false (cons true x3)), .F⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (s3))))))⟩

/-- `B> 10 x`, nested visits B→E: out in state C, leaving `00 x'`.  (In the run: 43847 times in 3·10^7 steps, first at step 53.) -/
theorem v_B_10_Be {x x1 : Tape} (h1 : Vis .B x .E x1) :
    Vis .B (cons true (cons false x)) .C (cons false (cons false x1)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .B⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 2 ⟨cons false (cons a L), cons true x1, .E⟩ = some ⟨L, cons a (cons false (cons false x1)), .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `B> 10 x`, nested visits B→F A→F B→C: out in state E, leaving `10 x'`.  (In the run: 8530 times in 3·10^7 steps, first at step 1703.) -/
theorem v_B_10_BfAfBc {x x1 x2 x3 : Tape} (h1 : Vis .B x .F x1) (h2 : Vis .A x1 .F x2) (h3 : Vis .B x2 .C x3) :
    Vis .B (cons true (cons false x)) .E (cons true (cons false x3)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .B⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons true x1, .F⟩ = some ⟨cons false (cons false (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a L))
  have s2 : steps 3 ⟨cons false (cons a L), cons false x2, .F⟩ = some ⟨cons true (cons false (cons a L)), x2, .B⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 true (cons false (cons a L))
  have s3 : steps 2 ⟨cons false (cons a L), cons true x3, .C⟩ = some ⟨L, cons a (cons true (cons false x3)), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (s3))))))⟩

/-- `B> 11 x`, nested visits A→A B→E: out in state C, leaving `00 x'`.  (In the run: 3 times in 3·10^7 steps, first at step 257.) -/
theorem v_B_11_AaBe {x x1 x2 : Tape} (h1 : Vis .A x .A x1) (h2 : Vis .B x1 .E x2) :
    Vis .B (cons true (cons true x)) .C (cons false (cons false x2)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons true x), .B⟩ = some ⟨cons false (cons false (cons a L)), x, .A⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons false x1, .A⟩ = some ⟨cons true (cons false (cons a L)), x1, .B⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 true (cons false (cons a L))
  have s2 : steps 2 ⟨cons false (cons a L), cons true x2, .E⟩ = some ⟨L, cons a (cons false (cons false x2)), .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `B> 11 x`, nested visits A→C A→D A→C A→D: out in state F, leaving `01 x'`.  (In the run: 501 times in 3·10^7 steps, first at step 445.) -/
theorem v_B_11_AcAdAcAd {x x1 x2 x3 x4 : Tape} (h1 : Vis .A x .C x1) (h2 : Vis .A x1 .D x2) (h3 : Vis .A x2 .C x3) (h4 : Vis .A x3 .D x4) :
    Vis .B (cons true (cons true x)) .F (cons false (cons true x4)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons true x), .B⟩ = some ⟨cons false (cons false (cons a L)), x, .A⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons false (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a L))
  have s2 : steps 3 ⟨cons false (cons a L), cons false x2, .D⟩ = some ⟨cons false (cons true (cons a L)), x2, .A⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons true (cons a L))
  have s3 : steps 1 ⟨cons true (cons a L), cons false x3, .C⟩ = some ⟨cons false (cons true (cons a L)), x3, .A⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons true (cons a L))
  have s4 : steps 2 ⟨cons true (cons a L), cons false x4, .D⟩ = some ⟨L, cons a (cons false (cons true x4)), .F⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (s4))))))))⟩

/-- `B> 11 x`, nested visits A→D A→D: out in state F, leaving `01 x'`.  (In the run: 10195 times in 3·10^7 steps, first at step 1207.) -/
theorem v_B_11_AdAd {x x1 x2 : Tape} (h1 : Vis .A x .D x1) (h2 : Vis .A x1 .D x2) :
    Vis .B (cons true (cons true x)) .F (cons false (cons true x2)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons true x), .B⟩ = some ⟨cons false (cons false (cons a L)), x, .A⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons a L))
  have s1 : steps 3 ⟨cons false (cons a L), cons false x1, .D⟩ = some ⟨cons false (cons true (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons a L))
  have s2 : steps 2 ⟨cons true (cons a L), cons false x2, .D⟩ = some ⟨L, cons a (cons false (cons true x2)), .F⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `B> 11 x`, nested visits A→D A→F: out in state D, leaving `00 x'`.  (In the run: 1 times in 3·10^7 steps, first at step 3031.) -/
theorem v_B_11_AdAf {x x1 x2 : Tape} (h1 : Vis .A x .D x1) (h2 : Vis .A x1 .F x2) :
    Vis .B (cons true (cons true x)) .D (cons false (cons false x2)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons true x), .B⟩ = some ⟨cons false (cons false (cons a L)), x, .A⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons a L))
  have s1 : steps 3 ⟨cons false (cons a L), cons false x1, .D⟩ = some ⟨cons false (cons true (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons a L))
  have s2 : steps 2 ⟨cons true (cons a L), cons false x2, .F⟩ = some ⟨L, cons a (cons false (cons false x2)), .D⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `B> 11 x`, nested visits A→F B→C: out in state E, leaving `10 x'`.  (In the run: 7 times in 3·10^7 steps, first at step 169.) -/
theorem v_B_11_AfBc {x x1 x2 : Tape} (h1 : Vis .A x .F x1) (h2 : Vis .B x1 .C x2) :
    Vis .B (cons true (cons true x)) .E (cons true (cons false x2)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons true x), .B⟩ = some ⟨cons false (cons false (cons a L)), x, .A⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons a L))
  have s1 : steps 3 ⟨cons false (cons a L), cons false x1, .F⟩ = some ⟨cons true (cons false (cons a L)), x1, .B⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 true (cons false (cons a L))
  have s2 : steps 2 ⟨cons false (cons a L), cons true x2, .C⟩ = some ⟨L, cons a (cons true (cons false x2)), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `F> 00 x`, no nested visit: out in state C, leaving `00 x'`.  (In the run: 14996 times in 3·10^7 steps, first at step 1211.) -/
theorem v_F_00_none {x : Tape}  :
    Vis .F (cons false (cons false x)) .C (cons false (cons false x)) := by
  intro a L
  have s0 : steps 1 ⟨cons a L, cons false (cons false x), .F⟩ = some ⟨L, cons a (cons false (cons false x)), .C⟩ := rfl
  exact ⟨_, s0⟩

/-- `F> 01 x`, no nested visit: out in state C, leaving `01 x'`.  (In the run: 51602 times in 3·10^7 steps, first at step 87.) -/
theorem v_F_01_none {x : Tape}  :
    Vis .F (cons false (cons true x)) .C (cons false (cons true x)) := by
  intro a L
  have s0 : steps 1 ⟨cons a L, cons false (cons true x), .F⟩ = some ⟨L, cons a (cons false (cons true x)), .C⟩ := rfl
  exact ⟨_, s0⟩

/-- `F> 10 x`, nested visits B→C: out in state E, leaving `10 x'`.  (In the run: 21075 times in 3·10^7 steps, first at step 23.) -/
theorem v_F_10_Bc {x x1 : Tape} (h1 : Vis .B x .C x1) :
    Vis .F (cons true (cons false x)) .E (cons true (cons false x1)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons false x), .F⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 2 ⟨cons false (cons a L), cons true x1, .C⟩ = some ⟨L, cons a (cons true (cons false x1)), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `F> 10 x`, nested visits B→E: out in state C, leaving `00 x'`.  (In the run: 16 times in 3·10^7 steps, first at step 15.) -/
theorem v_F_10_Be {x x1 : Tape} (h1 : Vis .B x .E x1) :
    Vis .F (cons true (cons false x)) .C (cons false (cons false x1)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons false x), .F⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 2 ⟨cons false (cons a L), cons true x1, .E⟩ = some ⟨L, cons a (cons false (cons false x1)), .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `F> 10 x`, nested visits B→F A→C A→D A→C A→D: out in state F, leaving `01 x'`.  (In the run: 2 times in 3·10^7 steps, first at step 1047.) -/
theorem v_F_10_BfAcAdAcAd {x x1 x2 x3 x4 x5 : Tape} (h1 : Vis .B x .F x1) (h2 : Vis .A x1 .C x2) (h3 : Vis .A x2 .D x3) (h4 : Vis .A x3 .C x4) (h5 : Vis .A x4 .D x5) :
    Vis .F (cons true (cons false x)) .F (cons false (cons true x5)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons false x), .F⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons true x1, .F⟩ = some ⟨cons false (cons false (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a L))
  have s2 : steps 1 ⟨cons false (cons a L), cons false x2, .C⟩ = some ⟨cons false (cons false (cons a L)), x2, .A⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons false (cons a L))
  have s3 : steps 3 ⟨cons false (cons a L), cons false x3, .D⟩ = some ⟨cons false (cons true (cons a L)), x3, .A⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons true (cons a L))
  have s4 : steps 1 ⟨cons true (cons a L), cons false x4, .C⟩ = some ⟨cons false (cons true (cons a L)), x4, .A⟩ := rfl
  obtain ⟨t5, c5⟩ := h5 false (cons true (cons a L))
  have s5 : steps 2 ⟨cons true (cons a L), cons false x5, .D⟩ = some ⟨L, cons a (cons false (cons true x5)), .F⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (steps_seq trans s4 (steps_seq trans c5 (s5))))))))))⟩

/-- `F> 10 x`, nested visits B→F A→D A→D: out in state F, leaving `01 x'`.  (In the run: 1 times in 3·10^7 steps, first at step 117993.) -/
theorem v_F_10_BfAdAd {x x1 x2 x3 : Tape} (h1 : Vis .B x .F x1) (h2 : Vis .A x1 .D x2) (h3 : Vis .A x2 .D x3) :
    Vis .F (cons true (cons false x)) .F (cons false (cons true x3)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons false x), .F⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons true x1, .F⟩ = some ⟨cons false (cons false (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a L))
  have s2 : steps 3 ⟨cons false (cons a L), cons false x2, .D⟩ = some ⟨cons false (cons true (cons a L)), x2, .A⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons true (cons a L))
  have s3 : steps 2 ⟨cons true (cons a L), cons false x3, .D⟩ = some ⟨L, cons a (cons false (cons true x3)), .F⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (s3))))))⟩

/-- `F> 10 x`, nested visits B→F A→F B→C: out in state E, leaving `10 x'`.  (In the run: 342 times in 3·10^7 steps, first at step 499.) -/
theorem v_F_10_BfAfBc {x x1 x2 x3 : Tape} (h1 : Vis .B x .F x1) (h2 : Vis .A x1 .F x2) (h3 : Vis .B x2 .C x3) :
    Vis .F (cons true (cons false x)) .E (cons true (cons false x3)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons false x), .F⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons true x1, .F⟩ = some ⟨cons false (cons false (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a L))
  have s2 : steps 3 ⟨cons false (cons a L), cons false x2, .F⟩ = some ⟨cons true (cons false (cons a L)), x2, .B⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 true (cons false (cons a L))
  have s3 : steps 2 ⟨cons false (cons a L), cons true x3, .C⟩ = some ⟨L, cons a (cons true (cons false x3)), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (s3))))))⟩

end H22247
