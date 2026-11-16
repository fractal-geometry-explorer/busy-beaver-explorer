import Machine

/-! # Visit laws of 1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB--- (left side)

Every theorem below is one row of a token-level visit law (mined from the run by `py/vislaws.c`, written by
`py/gen_visit2.py`): what one visit does to a stream that starts with the token, given what the nested visits of the
rest of the stream do.  Rows are exact for every stream (the hypotheses are about the rest only). -/

namespace H55410

open TM

/-- One visit of the stream `x` (left of the head's cell, nearest cell first) in state `q`: the head steps onto `x 0`
and the first time it comes back out on the right it is in state `r`, the stream is `x'`, and the cell it lands on
and everything right of it are untouched. -/
def VisL (q : St) (x : Tape) (r : St) (x' : Tape) : Prop :=
  ∀ (a : Bool) (R : Tape), ∃ t, steps t ⟨tail x, cons (x 0) (cons a R), q⟩ = some ⟨x', cons a R, r⟩

/-- `A` entering `00 x`, no nested visit: out in state B, leaving `10 x'`.  (In the run: 2034 times in the first 30,000,000 steps, first at step 6.) -/
theorem w_A_00_none {x : Tape}  :
    VisL .A (cons false (cons false x)) .B (cons true (cons false x)) := by
  intro a R
  have s0 : steps 1 ⟨cons false x, cons false (cons a R), .A⟩ = some ⟨cons true (cons false x), cons a R, .B⟩ := rfl
  exact ⟨_, s0⟩

/-- `A` entering `01 x`, no nested visit: out in state B, leaving `11 x'`.  (In the run: 411 times in the first 30,000,000 steps, first at step 92.) -/
theorem w_A_01_none {x : Tape}  :
    VisL .A (cons false (cons true x)) .B (cons true (cons true x)) := by
  intro a R
  have s0 : steps 1 ⟨cons true x, cons false (cons a R), .A⟩ = some ⟨cons true (cons true x), cons a R, .B⟩ := rfl
  exact ⟨_, s0⟩

/-- `A` entering `10 x`, nested visits A→B: out in state C, leaving `10 x'`.  (In the run: 2818 times in the first 30,000,000 steps, first at step 20.) -/
theorem w_A_10_Ab {x x1 : Tape} (h1 : VisL .A x .B x1) :
    VisL .A (cons true (cons false x)) .C (cons true (cons false x1)) := by
  intro a R
  have s0 : steps 4 ⟨cons false x, cons true (cons a R), .A⟩ = some ⟨tail x, cons (x 0) (cons true (cons false (cons a R))), .A⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a R))
  have s1 : steps 2 ⟨x1, cons true (cons false (cons a R)), .B⟩ = some ⟨cons true (cons false x1), cons a R, .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `A` entering `10 x`, nested visits A→C: out in state B, leaving `00 x'`.  (In the run: 2045 times in the first 30,000,000 steps, first at step 22.) -/
theorem w_A_10_Ac {x x1 : Tape} (h1 : VisL .A x .C x1) :
    VisL .A (cons true (cons false x)) .B (cons false (cons false x1)) := by
  intro a R
  have s0 : steps 4 ⟨cons false x, cons true (cons a R), .A⟩ = some ⟨tail x, cons (x 0) (cons true (cons false (cons a R))), .A⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a R))
  have s1 : steps 2 ⟨x1, cons true (cons false (cons a R)), .C⟩ = some ⟨cons false (cons false x1), cons a R, .B⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `A` entering `10 x`, nested visits A→D F→B C→D A→B: out in state C, leaving `10 x'`.  (In the run: 368 times in the first 30,000,000 steps, first at step 334.) -/
theorem w_A_10_AdFbCdAb {x x1 x2 x3 x4 : Tape} (h1 : VisL .A x .D x1) (h2 : VisL .F x1 .B x2) (h3 : VisL .C x2 .D x3) (h4 : VisL .A x3 .B x4) :
    VisL .A (cons true (cons false x)) .C (cons true (cons false x4)) := by
  intro a R
  have s0 : steps 4 ⟨cons false x, cons true (cons a R), .A⟩ = some ⟨tail x, cons (x 0) (cons true (cons false (cons a R))), .A⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a R))
  have s1 : steps 1 ⟨x1, cons true (cons false (cons a R)), .D⟩ = some ⟨tail x1, cons (x1 0) (cons false (cons false (cons a R))), .F⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a R))
  have s2 : steps 1 ⟨x2, cons false (cons false (cons a R)), .B⟩ = some ⟨tail x2, cons (x2 0) (cons false (cons false (cons a R))), .C⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons false (cons a R))
  have s3 : steps 3 ⟨x3, cons false (cons false (cons a R)), .D⟩ = some ⟨tail x3, cons (x3 0) (cons true (cons false (cons a R))), .A⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 true (cons false (cons a R))
  have s4 : steps 2 ⟨x4, cons true (cons false (cons a R)), .B⟩ = some ⟨cons true (cons false x4), cons a R, .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (s4))))))))⟩

/-- `A` entering `10 x`, nested visits A→D F→B C→E D→B C→E: out in state D, leaving `01 x'`.  (In the run: 2 times in the first 30,000,000 steps, first at step 204.) -/
theorem w_A_10_AdFbCeDbCe {x x1 x2 x3 x4 x5 : Tape} (h1 : VisL .A x .D x1) (h2 : VisL .F x1 .B x2) (h3 : VisL .C x2 .E x3) (h4 : VisL .D x3 .B x4) (h5 : VisL .C x4 .E x5) :
    VisL .A (cons true (cons false x)) .D (cons false (cons true x5)) := by
  intro a R
  have s0 : steps 4 ⟨cons false x, cons true (cons a R), .A⟩ = some ⟨tail x, cons (x 0) (cons true (cons false (cons a R))), .A⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a R))
  have s1 : steps 1 ⟨x1, cons true (cons false (cons a R)), .D⟩ = some ⟨tail x1, cons (x1 0) (cons false (cons false (cons a R))), .F⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a R))
  have s2 : steps 1 ⟨x2, cons false (cons false (cons a R)), .B⟩ = some ⟨tail x2, cons (x2 0) (cons false (cons false (cons a R))), .C⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons false (cons a R))
  have s3 : steps 3 ⟨x3, cons false (cons false (cons a R)), .E⟩ = some ⟨tail x3, cons (x3 0) (cons false (cons true (cons a R))), .D⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons true (cons a R))
  have s4 : steps 1 ⟨x4, cons false (cons true (cons a R)), .B⟩ = some ⟨tail x4, cons (x4 0) (cons false (cons true (cons a R))), .C⟩ := rfl
  obtain ⟨t5, c5⟩ := h5 false (cons true (cons a R))
  have s5 : steps 2 ⟨x5, cons false (cons true (cons a R)), .E⟩ = some ⟨cons false (cons true x5), cons a R, .D⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (steps_seq trans s4 (steps_seq trans c5 (s5))))))))))⟩

/-- `A` entering `10 x`, nested visits A→E A→B: out in state C, leaving `10 x'`.  (In the run: 1 times in the first 30,000,000 steps, first at step 3594.) -/
theorem w_A_10_AeAb {x x1 x2 : Tape} (h1 : VisL .A x .E x1) (h2 : VisL .A x1 .B x2) :
    VisL .A (cons true (cons false x)) .C (cons true (cons false x2)) := by
  intro a R
  have s0 : steps 4 ⟨cons false x, cons true (cons a R), .A⟩ = some ⟨tail x, cons (x 0) (cons true (cons false (cons a R))), .A⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a R))
  have s1 : steps 1 ⟨x1, cons true (cons false (cons a R)), .E⟩ = some ⟨tail x1, cons (x1 0) (cons true (cons false (cons a R))), .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 true (cons false (cons a R))
  have s2 : steps 2 ⟨x2, cons true (cons false (cons a R)), .B⟩ = some ⟨cons true (cons false x2), cons a R, .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `A` entering `11 x`, nested visits F→B C→B C→E D→B C→B C→E: out in state D, leaving `01 x'`.  (In the run: 70 times in the first 30,000,000 steps, first at step 1934.) -/
theorem w_A_11_FbCbCeDbCbCe {x x1 x2 x3 x4 x5 x6 : Tape} (h1 : VisL .F x .B x1) (h2 : VisL .C x1 .B x2) (h3 : VisL .C x2 .E x3) (h4 : VisL .D x3 .B x4) (h5 : VisL .C x4 .B x5) (h6 : VisL .C x5 .E x6) :
    VisL .A (cons true (cons true x)) .D (cons false (cons true x6)) := by
  intro a R
  have s0 : steps 2 ⟨cons true x, cons true (cons a R), .A⟩ = some ⟨tail x, cons (x 0) (cons false (cons false (cons a R))), .F⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons a R))
  have s1 : steps 1 ⟨x1, cons false (cons false (cons a R)), .B⟩ = some ⟨tail x1, cons (x1 0) (cons false (cons false (cons a R))), .C⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a R))
  have s2 : steps 1 ⟨x2, cons false (cons false (cons a R)), .B⟩ = some ⟨tail x2, cons (x2 0) (cons false (cons false (cons a R))), .C⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons false (cons a R))
  have s3 : steps 3 ⟨x3, cons false (cons false (cons a R)), .E⟩ = some ⟨tail x3, cons (x3 0) (cons false (cons true (cons a R))), .D⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons true (cons a R))
  have s4 : steps 1 ⟨x4, cons false (cons true (cons a R)), .B⟩ = some ⟨tail x4, cons (x4 0) (cons false (cons true (cons a R))), .C⟩ := rfl
  obtain ⟨t5, c5⟩ := h5 false (cons true (cons a R))
  have s5 : steps 1 ⟨x5, cons false (cons true (cons a R)), .B⟩ = some ⟨tail x5, cons (x5 0) (cons false (cons true (cons a R))), .C⟩ := rfl
  obtain ⟨t6, c6⟩ := h6 false (cons true (cons a R))
  have s6 : steps 2 ⟨x6, cons false (cons true (cons a R)), .E⟩ = some ⟨cons false (cons true x6), cons a R, .D⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (steps_seq trans s4 (steps_seq trans c5 (steps_seq trans s5 (steps_seq trans c6 (s6))))))))))))⟩

/-- `A` entering `11 x`, nested visits F→B C→B C→E D→B C→C A→C A→C: out in state B, leaving `00 x'`.  (In the run: 1 times in the first 30,000,000 steps, first at step 1484.) -/
theorem w_A_11_FbCbCeDbCcAcAc {x x1 x2 x3 x4 x5 x6 x7 : Tape} (h1 : VisL .F x .B x1) (h2 : VisL .C x1 .B x2) (h3 : VisL .C x2 .E x3) (h4 : VisL .D x3 .B x4) (h5 : VisL .C x4 .C x5) (h6 : VisL .A x5 .C x6) (h7 : VisL .A x6 .C x7) :
    VisL .A (cons true (cons true x)) .B (cons false (cons false x7)) := by
  intro a R
  have s0 : steps 2 ⟨cons true x, cons true (cons a R), .A⟩ = some ⟨tail x, cons (x 0) (cons false (cons false (cons a R))), .F⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons a R))
  have s1 : steps 1 ⟨x1, cons false (cons false (cons a R)), .B⟩ = some ⟨tail x1, cons (x1 0) (cons false (cons false (cons a R))), .C⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a R))
  have s2 : steps 1 ⟨x2, cons false (cons false (cons a R)), .B⟩ = some ⟨tail x2, cons (x2 0) (cons false (cons false (cons a R))), .C⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons false (cons a R))
  have s3 : steps 3 ⟨x3, cons false (cons false (cons a R)), .E⟩ = some ⟨tail x3, cons (x3 0) (cons false (cons true (cons a R))), .D⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons true (cons a R))
  have s4 : steps 1 ⟨x4, cons false (cons true (cons a R)), .B⟩ = some ⟨tail x4, cons (x4 0) (cons false (cons true (cons a R))), .C⟩ := rfl
  obtain ⟨t5, c5⟩ := h5 false (cons true (cons a R))
  have s5 : steps 1 ⟨x5, cons false (cons true (cons a R)), .C⟩ = some ⟨tail x5, cons (x5 0) (cons true (cons true (cons a R))), .A⟩ := rfl
  obtain ⟨t6, c6⟩ := h6 true (cons true (cons a R))
  have s6 : steps 5 ⟨x6, cons true (cons true (cons a R)), .C⟩ = some ⟨tail x6, cons (x6 0) (cons true (cons false (cons a R))), .A⟩ := rfl
  obtain ⟨t7, c7⟩ := h7 true (cons false (cons a R))
  have s7 : steps 2 ⟨x7, cons true (cons false (cons a R)), .C⟩ = some ⟨cons false (cons false x7), cons a R, .B⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (steps_seq trans s4 (steps_seq trans c5 (steps_seq trans s5 (steps_seq trans c6 (steps_seq trans s6 (steps_seq trans c7 (s7))))))))))))))⟩

/-- `A` entering `11 x`, nested visits F→B C→D A→B: out in state C, leaving `10 x'`.  (In the run: 27 times in the first 30,000,000 steps, first at step 3696.) -/
theorem w_A_11_FbCdAb {x x1 x2 x3 : Tape} (h1 : VisL .F x .B x1) (h2 : VisL .C x1 .D x2) (h3 : VisL .A x2 .B x3) :
    VisL .A (cons true (cons true x)) .C (cons true (cons false x3)) := by
  intro a R
  have s0 : steps 2 ⟨cons true x, cons true (cons a R), .A⟩ = some ⟨tail x, cons (x 0) (cons false (cons false (cons a R))), .F⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons a R))
  have s1 : steps 1 ⟨x1, cons false (cons false (cons a R)), .B⟩ = some ⟨tail x1, cons (x1 0) (cons false (cons false (cons a R))), .C⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a R))
  have s2 : steps 3 ⟨x2, cons false (cons false (cons a R)), .D⟩ = some ⟨tail x2, cons (x2 0) (cons true (cons false (cons a R))), .A⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 true (cons false (cons a R))
  have s3 : steps 2 ⟨x3, cons true (cons false (cons a R)), .B⟩ = some ⟨cons true (cons false x3), cons a R, .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (s3))))))⟩

/-- `A` entering `11 x`, nested visits F→B C→E D→B C→D: out in state E, leaving `00 x'`.  (In the run: 1 times in the first 30,000,000 steps, first at step 3590.) -/
theorem w_A_11_FbCeDbCd {x x1 x2 x3 x4 : Tape} (h1 : VisL .F x .B x1) (h2 : VisL .C x1 .E x2) (h3 : VisL .D x2 .B x3) (h4 : VisL .C x3 .D x4) :
    VisL .A (cons true (cons true x)) .E (cons false (cons false x4)) := by
  intro a R
  have s0 : steps 2 ⟨cons true x, cons true (cons a R), .A⟩ = some ⟨tail x, cons (x 0) (cons false (cons false (cons a R))), .F⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons a R))
  have s1 : steps 1 ⟨x1, cons false (cons false (cons a R)), .B⟩ = some ⟨tail x1, cons (x1 0) (cons false (cons false (cons a R))), .C⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a R))
  have s2 : steps 3 ⟨x2, cons false (cons false (cons a R)), .E⟩ = some ⟨tail x2, cons (x2 0) (cons false (cons true (cons a R))), .D⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons true (cons a R))
  have s3 : steps 1 ⟨x3, cons false (cons true (cons a R)), .B⟩ = some ⟨tail x3, cons (x3 0) (cons false (cons true (cons a R))), .C⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons true (cons a R))
  have s4 : steps 2 ⟨x4, cons false (cons true (cons a R)), .D⟩ = some ⟨cons false (cons false x4), cons a R, .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (s4))))))))⟩

/-- `A` entering `11 x`, nested visits F→B C→E D→B C→E: out in state D, leaving `01 x'`.  (In the run: 310 times in the first 30,000,000 steps, first at step 164.) -/
theorem w_A_11_FbCeDbCe {x x1 x2 x3 x4 : Tape} (h1 : VisL .F x .B x1) (h2 : VisL .C x1 .E x2) (h3 : VisL .D x2 .B x3) (h4 : VisL .C x3 .E x4) :
    VisL .A (cons true (cons true x)) .D (cons false (cons true x4)) := by
  intro a R
  have s0 : steps 2 ⟨cons true x, cons true (cons a R), .A⟩ = some ⟨tail x, cons (x 0) (cons false (cons false (cons a R))), .F⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons a R))
  have s1 : steps 1 ⟨x1, cons false (cons false (cons a R)), .B⟩ = some ⟨tail x1, cons (x1 0) (cons false (cons false (cons a R))), .C⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a R))
  have s2 : steps 3 ⟨x2, cons false (cons false (cons a R)), .E⟩ = some ⟨tail x2, cons (x2 0) (cons false (cons true (cons a R))), .D⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons true (cons a R))
  have s3 : steps 1 ⟨x3, cons false (cons true (cons a R)), .B⟩ = some ⟨tail x3, cons (x3 0) (cons false (cons true (cons a R))), .C⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons true (cons a R))
  have s4 : steps 2 ⟨x4, cons false (cons true (cons a R)), .E⟩ = some ⟨cons false (cons true x4), cons a R, .D⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (s4))))))))⟩

/-- `C` entering `00 x`, no nested visit: out in state E, leaving `01 x'`.  (In the run: 1153 times in the first 30,000,000 steps, first at step 38.) -/
theorem w_C_00_none {x : Tape}  :
    VisL .C (cons false (cons false x)) .E (cons false (cons true x)) := by
  intro a R
  have s0 : steps 3 ⟨cons false x, cons false (cons a R), .C⟩ = some ⟨cons false (cons true x), cons a R, .E⟩ := rfl
  exact ⟨_, s0⟩

/-- `C` entering `01 x`, nested visits D→B C→B C→E: out in state D, leaving `01 x'`.  (In the run: 57 times in the first 30,000,000 steps, first at step 2126.) -/
theorem w_C_01_DbCbCe {x x1 x2 x3 : Tape} (h1 : VisL .D x .B x1) (h2 : VisL .C x1 .B x2) (h3 : VisL .C x2 .E x3) :
    VisL .C (cons false (cons true x)) .D (cons false (cons true x3)) := by
  intro a R
  have s0 : steps 2 ⟨cons true x, cons false (cons a R), .C⟩ = some ⟨tail x, cons (x 0) (cons false (cons true (cons a R))), .D⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a R))
  have s1 : steps 1 ⟨x1, cons false (cons true (cons a R)), .B⟩ = some ⟨tail x1, cons (x1 0) (cons false (cons true (cons a R))), .C⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons a R))
  have s2 : steps 1 ⟨x2, cons false (cons true (cons a R)), .B⟩ = some ⟨tail x2, cons (x2 0) (cons false (cons true (cons a R))), .C⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons true (cons a R))
  have s3 : steps 2 ⟨x3, cons false (cons true (cons a R)), .E⟩ = some ⟨cons false (cons true x3), cons a R, .D⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (s3))))))⟩

/-- `C` entering `01 x`, nested visits D→B C→D: out in state E, leaving `00 x'`.  (In the run: 918 times in the first 30,000,000 steps, first at step 154.) -/
theorem w_C_01_DbCd {x x1 x2 : Tape} (h1 : VisL .D x .B x1) (h2 : VisL .C x1 .D x2) :
    VisL .C (cons false (cons true x)) .E (cons false (cons false x2)) := by
  intro a R
  have s0 : steps 2 ⟨cons true x, cons false (cons a R), .C⟩ = some ⟨tail x, cons (x 0) (cons false (cons true (cons a R))), .D⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a R))
  have s1 : steps 1 ⟨x1, cons false (cons true (cons a R)), .B⟩ = some ⟨tail x1, cons (x1 0) (cons false (cons true (cons a R))), .C⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons a R))
  have s2 : steps 2 ⟨x2, cons false (cons true (cons a R)), .D⟩ = some ⟨cons false (cons false x2), cons a R, .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `C` entering `01 x`, nested visits D→B C→E: out in state D, leaving `01 x'`.  (In the run: 1269 times in the first 30,000,000 steps, first at step 76.) -/
theorem w_C_01_DbCe {x x1 x2 : Tape} (h1 : VisL .D x .B x1) (h2 : VisL .C x1 .E x2) :
    VisL .C (cons false (cons true x)) .D (cons false (cons true x2)) := by
  intro a R
  have s0 : steps 2 ⟨cons true x, cons false (cons a R), .C⟩ = some ⟨tail x, cons (x 0) (cons false (cons true (cons a R))), .D⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a R))
  have s1 : steps 1 ⟨x1, cons false (cons true (cons a R)), .B⟩ = some ⟨tail x1, cons (x1 0) (cons false (cons true (cons a R))), .C⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons a R))
  have s2 : steps 2 ⟨x2, cons false (cons true (cons a R)), .E⟩ = some ⟨cons false (cons true x2), cons a R, .D⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `C` entering `01 x`, nested visits D→C A→B: out in state E, leaving `01 x'`.  (In the run: 30 times in the first 30,000,000 steps, first at step 150.) -/
theorem w_C_01_DcAb {x x1 x2 : Tape} (h1 : VisL .D x .C x1) (h2 : VisL .A x1 .B x2) :
    VisL .C (cons false (cons true x)) .E (cons false (cons true x2)) := by
  intro a R
  have s0 : steps 2 ⟨cons true x, cons false (cons a R), .C⟩ = some ⟨tail x, cons (x 0) (cons false (cons true (cons a R))), .D⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a R))
  have s1 : steps 1 ⟨x1, cons false (cons true (cons a R)), .C⟩ = some ⟨tail x1, cons (x1 0) (cons true (cons true (cons a R))), .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 true (cons true (cons a R))
  have s2 : steps 4 ⟨x2, cons true (cons true (cons a R)), .B⟩ = some ⟨cons false (cons true x2), cons a R, .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `C` entering `01 x`, nested visits D→C A→C A→C: out in state B, leaving `00 x'`.  (In the run: 200 times in the first 30,000,000 steps, first at step 740.) -/
theorem w_C_01_DcAcAc {x x1 x2 x3 : Tape} (h1 : VisL .D x .C x1) (h2 : VisL .A x1 .C x2) (h3 : VisL .A x2 .C x3) :
    VisL .C (cons false (cons true x)) .B (cons false (cons false x3)) := by
  intro a R
  have s0 : steps 2 ⟨cons true x, cons false (cons a R), .C⟩ = some ⟨tail x, cons (x 0) (cons false (cons true (cons a R))), .D⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a R))
  have s1 : steps 1 ⟨x1, cons false (cons true (cons a R)), .C⟩ = some ⟨tail x1, cons (x1 0) (cons true (cons true (cons a R))), .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 true (cons true (cons a R))
  have s2 : steps 5 ⟨x2, cons true (cons true (cons a R)), .C⟩ = some ⟨tail x2, cons (x2 0) (cons true (cons false (cons a R))), .A⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 true (cons false (cons a R))
  have s3 : steps 2 ⟨x3, cons true (cons false (cons a R)), .C⟩ = some ⟨cons false (cons false x3), cons a R, .B⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (s3))))))⟩

/-- `C` entering `01 x`, nested visits D→C A→C A→D F→B C→D A→B: out in state C, leaving `10 x'`.  (In the run: 1 times in the first 30,000,000 steps, first at step 1326.) -/
theorem w_C_01_DcAcAdFbCdAb {x x1 x2 x3 x4 x5 x6 : Tape} (h1 : VisL .D x .C x1) (h2 : VisL .A x1 .C x2) (h3 : VisL .A x2 .D x3) (h4 : VisL .F x3 .B x4) (h5 : VisL .C x4 .D x5) (h6 : VisL .A x5 .B x6) :
    VisL .C (cons false (cons true x)) .C (cons true (cons false x6)) := by
  intro a R
  have s0 : steps 2 ⟨cons true x, cons false (cons a R), .C⟩ = some ⟨tail x, cons (x 0) (cons false (cons true (cons a R))), .D⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a R))
  have s1 : steps 1 ⟨x1, cons false (cons true (cons a R)), .C⟩ = some ⟨tail x1, cons (x1 0) (cons true (cons true (cons a R))), .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 true (cons true (cons a R))
  have s2 : steps 5 ⟨x2, cons true (cons true (cons a R)), .C⟩ = some ⟨tail x2, cons (x2 0) (cons true (cons false (cons a R))), .A⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 true (cons false (cons a R))
  have s3 : steps 1 ⟨x3, cons true (cons false (cons a R)), .D⟩ = some ⟨tail x3, cons (x3 0) (cons false (cons false (cons a R))), .F⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons false (cons a R))
  have s4 : steps 1 ⟨x4, cons false (cons false (cons a R)), .B⟩ = some ⟨tail x4, cons (x4 0) (cons false (cons false (cons a R))), .C⟩ := rfl
  obtain ⟨t5, c5⟩ := h5 false (cons false (cons a R))
  have s5 : steps 3 ⟨x5, cons false (cons false (cons a R)), .D⟩ = some ⟨tail x5, cons (x5 0) (cons true (cons false (cons a R))), .A⟩ := rfl
  obtain ⟨t6, c6⟩ := h6 true (cons false (cons a R))
  have s6 : steps 2 ⟨x6, cons true (cons false (cons a R)), .B⟩ = some ⟨cons true (cons false x6), cons a R, .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (steps_seq trans s4 (steps_seq trans c5 (steps_seq trans s5 (steps_seq trans c6 (s6))))))))))))⟩

/-- `C` entering `01 x`, nested visits D→D: out in state E, leaving `00 x'`.  (In the run: 1 times in the first 30,000,000 steps, first at step 434.) -/
theorem w_C_01_Dd {x x1 : Tape} (h1 : VisL .D x .D x1) :
    VisL .C (cons false (cons true x)) .E (cons false (cons false x1)) := by
  intro a R
  have s0 : steps 2 ⟨cons true x, cons false (cons a R), .C⟩ = some ⟨tail x, cons (x 0) (cons false (cons true (cons a R))), .D⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a R))
  have s1 : steps 2 ⟨x1, cons false (cons true (cons a R)), .D⟩ = some ⟨cons false (cons false x1), cons a R, .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `C` entering `10 x`, no nested visit: out in state D, leaving `00 x'`.  (In the run: 1 times in the first 30,000,000 steps, first at step 2.) -/
theorem w_C_10_none {x : Tape}  :
    VisL .C (cons true (cons false x)) .D (cons false (cons false x)) := by
  intro a R
  have s0 : steps 1 ⟨cons false x, cons true (cons a R), .C⟩ = some ⟨cons false (cons false x), cons a R, .D⟩ := rfl
  exact ⟨_, s0⟩

/-- `D` entering `00 x`, no nested visit: out in state B, leaving `00 x'`.  (In the run: 785 times in the first 30,000,000 steps, first at step 82.) -/
theorem w_D_00_none {x : Tape}  :
    VisL .D (cons false (cons false x)) .B (cons false (cons false x)) := by
  intro a R
  have s0 : steps 1 ⟨cons false x, cons false (cons a R), .D⟩ = some ⟨cons false (cons false x), cons a R, .B⟩ := rfl
  exact ⟨_, s0⟩

/-- `D` entering `01 x`, no nested visit: out in state B, leaving `01 x'`.  (In the run: 1847 times in the first 30,000,000 steps, first at step 42.) -/
theorem w_D_01_none {x : Tape}  :
    VisL .D (cons false (cons true x)) .B (cons false (cons true x)) := by
  intro a R
  have s0 : steps 1 ⟨cons true x, cons false (cons a R), .D⟩ = some ⟨cons false (cons true x), cons a R, .B⟩ := rfl
  exact ⟨_, s0⟩

/-- `D` entering `10 x`, nested visits A→B: out in state C, leaving `10 x'`.  (In the run: 228 times in the first 30,000,000 steps, first at step 120.) -/
theorem w_D_10_Ab {x x1 : Tape} (h1 : VisL .A x .B x1) :
    VisL .D (cons true (cons false x)) .C (cons true (cons false x1)) := by
  intro a R
  have s0 : steps 4 ⟨cons false x, cons true (cons a R), .D⟩ = some ⟨tail x, cons (x 0) (cons true (cons false (cons a R))), .A⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a R))
  have s1 : steps 2 ⟨x1, cons true (cons false (cons a R)), .B⟩ = some ⟨cons true (cons false x1), cons a R, .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `D` entering `10 x`, nested visits A→C: out in state B, leaving `00 x'`.  (In the run: 2 times in the first 30,000,000 steps, first at step 70.) -/
theorem w_D_10_Ac {x x1 : Tape} (h1 : VisL .A x .C x1) :
    VisL .D (cons true (cons false x)) .B (cons false (cons false x1)) := by
  intro a R
  have s0 : steps 4 ⟨cons false x, cons true (cons a R), .D⟩ = some ⟨tail x, cons (x 0) (cons true (cons false (cons a R))), .A⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a R))
  have s1 : steps 2 ⟨x1, cons true (cons false (cons a R)), .C⟩ = some ⟨cons false (cons false x1), cons a R, .B⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `D` entering `10 x`, nested visits A→D F→B C→D A→B: out in state C, leaving `10 x'`.  (In the run: 5 times in the first 30,000,000 steps, first at step 606.) -/
theorem w_D_10_AdFbCdAb {x x1 x2 x3 x4 : Tape} (h1 : VisL .A x .D x1) (h2 : VisL .F x1 .B x2) (h3 : VisL .C x2 .D x3) (h4 : VisL .A x3 .B x4) :
    VisL .D (cons true (cons false x)) .C (cons true (cons false x4)) := by
  intro a R
  have s0 : steps 4 ⟨cons false x, cons true (cons a R), .D⟩ = some ⟨tail x, cons (x 0) (cons true (cons false (cons a R))), .A⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a R))
  have s1 : steps 1 ⟨x1, cons true (cons false (cons a R)), .D⟩ = some ⟨tail x1, cons (x1 0) (cons false (cons false (cons a R))), .F⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a R))
  have s2 : steps 1 ⟨x2, cons false (cons false (cons a R)), .B⟩ = some ⟨tail x2, cons (x2 0) (cons false (cons false (cons a R))), .C⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons false (cons a R))
  have s3 : steps 3 ⟨x3, cons false (cons false (cons a R)), .D⟩ = some ⟨tail x3, cons (x3 0) (cons true (cons false (cons a R))), .A⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 true (cons false (cons a R))
  have s4 : steps 2 ⟨x4, cons true (cons false (cons a R)), .B⟩ = some ⟨cons true (cons false x4), cons a R, .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (s4))))))))⟩

/-- `D` entering `10 x`, nested visits A→D F→B C→E D→B C→E: out in state D, leaving `01 x'`.  (In the run: 1 times in the first 30,000,000 steps, first at step 432.) -/
theorem w_D_10_AdFbCeDbCe {x x1 x2 x3 x4 x5 : Tape} (h1 : VisL .A x .D x1) (h2 : VisL .F x1 .B x2) (h3 : VisL .C x2 .E x3) (h4 : VisL .D x3 .B x4) (h5 : VisL .C x4 .E x5) :
    VisL .D (cons true (cons false x)) .D (cons false (cons true x5)) := by
  intro a R
  have s0 : steps 4 ⟨cons false x, cons true (cons a R), .D⟩ = some ⟨tail x, cons (x 0) (cons true (cons false (cons a R))), .A⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a R))
  have s1 : steps 1 ⟨x1, cons true (cons false (cons a R)), .D⟩ = some ⟨tail x1, cons (x1 0) (cons false (cons false (cons a R))), .F⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a R))
  have s2 : steps 1 ⟨x2, cons false (cons false (cons a R)), .B⟩ = some ⟨tail x2, cons (x2 0) (cons false (cons false (cons a R))), .C⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons false (cons a R))
  have s3 : steps 3 ⟨x3, cons false (cons false (cons a R)), .E⟩ = some ⟨tail x3, cons (x3 0) (cons false (cons true (cons a R))), .D⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons true (cons a R))
  have s4 : steps 1 ⟨x4, cons false (cons true (cons a R)), .B⟩ = some ⟨tail x4, cons (x4 0) (cons false (cons true (cons a R))), .C⟩ := rfl
  obtain ⟨t5, c5⟩ := h5 false (cons true (cons a R))
  have s5 : steps 2 ⟨x5, cons false (cons true (cons a R)), .E⟩ = some ⟨cons false (cons true x5), cons a R, .D⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (steps_seq trans s4 (steps_seq trans c5 (s5))))))))))⟩

/-- `F` entering `00 x`, no nested visit: out in state B, leaving `00 x'`.  (In the run: 162 times in the first 30,000,000 steps, first at step 242.) -/
theorem w_F_00_none {x : Tape}  :
    VisL .F (cons false (cons false x)) .B (cons false (cons false x)) := by
  intro a R
  have s0 : steps 1 ⟨cons false x, cons false (cons a R), .F⟩ = some ⟨cons false (cons false x), cons a R, .B⟩ := rfl
  exact ⟨_, s0⟩

/-- `F` entering `01 x`, no nested visit: out in state B, leaving `01 x'`.  (In the run: 629 times in the first 30,000,000 steps, first at step 102.) -/
theorem w_F_01_none {x : Tape}  :
    VisL .F (cons false (cons true x)) .B (cons false (cons true x)) := by
  intro a R
  have s0 : steps 1 ⟨cons true x, cons false (cons a R), .F⟩ = some ⟨cons false (cons true x), cons a R, .B⟩ := rfl
  exact ⟨_, s0⟩

end H55410
