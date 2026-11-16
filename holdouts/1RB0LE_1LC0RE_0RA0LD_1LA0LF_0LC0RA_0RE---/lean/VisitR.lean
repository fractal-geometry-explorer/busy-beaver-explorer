import Machine

/-! # Visit laws of 1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE--- (right side)

Every theorem below is one row of a token-level visit law (mined from the run by `py/vislaws.c`, written by
`py/gen_visit2.py`): what one visit does to a stream that starts with the token, given what the nested visits of the
rest of the stream do.  Rows are exact for every stream (the hypotheses are about the rest only). -/

namespace H43701

open TM

/-- One visit of the stream `x` (right of the head's cell) in state `q`: back out on the left in state `r`, leaving
`x'`; the cell it lands on and everything left of it are untouched. -/
def Vis (q : St) (x : Tape) (r : St) (x' : Tape) : Prop :=
  ∀ (a : Bool) (L : Tape), ∃ t, steps t ⟨cons a L, x, q⟩ = some ⟨L, cons a x', r⟩

/-- `A` entering `00 x`, no nested visit: out in state D, leaving `01 x'`.  (In the run: 11045 times in the first 30,000,000 steps, first at step 14.) -/
theorem v_A_00_none {x : Tape}  :
    Vis .A (cons false (cons false x)) .D (cons false (cons true x)) := by
  intro a L
  have s0 : steps 3 ⟨cons a L, cons false (cons false x), .A⟩ = some ⟨L, cons a (cons false (cons true x)), .D⟩ := rfl
  exact ⟨_, s0⟩

/-- `A` entering `01 x`, nested visits E→A B→A B→A: out in state C, leaving `00 x'`.  (In the run: 383 times in the first 30,000,000 steps, first at step 316.) -/
theorem v_A_01_EaBaBa {x x1 x2 x3 : Tape} (h1 : Vis .E x .A x1) (h2 : Vis .B x1 .A x2) (h3 : Vis .B x2 .A x3) :
    Vis .A (cons false (cons true x)) .C (cons false (cons false x3)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .A⟩ = some ⟨cons true (cons true (cons a L)), x1, .B⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 true (cons true (cons a L))
  have s2 : steps 3 ⟨cons true (cons a L), cons true x2, .A⟩ = some ⟨cons true (cons false (cons a L)), x2, .B⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 true (cons false (cons a L))
  have s3 : steps 2 ⟨cons false (cons a L), cons true x3, .A⟩ = some ⟨L, cons a (cons false (cons false x3)), .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (s3))))))⟩

/-- `A` entering `01 x`, nested visits E→A B→A B→C: out in state A, leaving `10 x'`.  (In the run: 3 times in the first 30,000,000 steps, first at step 186.) -/
theorem v_A_01_EaBaBc {x x1 x2 x3 : Tape} (h1 : Vis .E x .A x1) (h2 : Vis .B x1 .A x2) (h3 : Vis .B x2 .C x3) :
    Vis .A (cons false (cons true x)) .A (cons true (cons false x3)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .A⟩ = some ⟨cons true (cons true (cons a L)), x1, .B⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 true (cons true (cons a L))
  have s2 : steps 3 ⟨cons true (cons a L), cons true x2, .A⟩ = some ⟨cons true (cons false (cons a L)), x2, .B⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 true (cons false (cons a L))
  have s3 : steps 2 ⟨cons false (cons a L), cons true x3, .C⟩ = some ⟨L, cons a (cons true (cons false x3)), .A⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (s3))))))⟩

/-- `A` entering `01 x`, nested visits E→A B→C: out in state F, leaving `00 x'`.  (In the run: 1 times in the first 30,000,000 steps, first at step 3366.) -/
theorem v_A_01_EaBc {x x1 x2 : Tape} (h1 : Vis .E x .A x1) (h2 : Vis .B x1 .C x2) :
    Vis .A (cons false (cons true x)) .F (cons false (cons false x2)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .A⟩ = some ⟨cons true (cons true (cons a L)), x1, .B⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 true (cons true (cons a L))
  have s2 : steps 2 ⟨cons true (cons a L), cons true x2, .C⟩ = some ⟨L, cons a (cons false (cons false x2)), .F⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `A` entering `01 x`, nested visits E→A B→E A→E: out in state D, leaving `00 x'`.  (In the run: 2 times in the first 30,000,000 steps, first at step 1402.) -/
theorem v_A_01_EaBeAe {x x1 x2 x3 : Tape} (h1 : Vis .E x .A x1) (h2 : Vis .B x1 .E x2) (h3 : Vis .A x2 .E x3) :
    Vis .A (cons false (cons true x)) .D (cons false (cons false x3)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .A⟩ = some ⟨cons true (cons true (cons a L)), x1, .B⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 true (cons true (cons a L))
  have s2 : steps 1 ⟨cons true (cons a L), cons true x2, .E⟩ = some ⟨cons false (cons true (cons a L)), x2, .A⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons true (cons a L))
  have s3 : steps 2 ⟨cons true (cons a L), cons false x3, .E⟩ = some ⟨L, cons a (cons false (cons false x3)), .D⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (s3))))))⟩

/-- `A` entering `01 x`, nested visits E→C A→A B→A B→A: out in state C, leaving `00 x'`.  (In the run: 1 times in the first 30,000,000 steps, first at step 1248.) -/
theorem v_A_01_EcAaBaBa {x x1 x2 x3 x4 : Tape} (h1 : Vis .E x .C x1) (h2 : Vis .A x1 .A x2) (h3 : Vis .B x2 .A x3) (h4 : Vis .B x3 .A x4) :
    Vis .A (cons false (cons true x)) .C (cons false (cons false x4)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons true (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons a L))
  have s2 : steps 1 ⟨cons true (cons a L), cons false x2, .A⟩ = some ⟨cons true (cons true (cons a L)), x2, .B⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 true (cons true (cons a L))
  have s3 : steps 3 ⟨cons true (cons a L), cons true x3, .A⟩ = some ⟨cons true (cons false (cons a L)), x3, .B⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 true (cons false (cons a L))
  have s4 : steps 2 ⟨cons false (cons a L), cons true x4, .A⟩ = some ⟨L, cons a (cons false (cons false x4)), .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (s4))))))))⟩

/-- `A` entering `01 x`, nested visits E→C A→C A→D: out in state E, leaving `01 x'`.  (In the run: 367 times in the first 30,000,000 steps, first at step 700.) -/
theorem v_A_01_EcAcAd {x x1 x2 x3 : Tape} (h1 : Vis .E x .C x1) (h2 : Vis .A x1 .C x2) (h3 : Vis .A x2 .D x3) :
    Vis .A (cons false (cons true x)) .E (cons false (cons true x3)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons true (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons a L))
  have s2 : steps 1 ⟨cons true (cons a L), cons false x2, .C⟩ = some ⟨cons false (cons true (cons a L)), x2, .A⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons true (cons a L))
  have s3 : steps 2 ⟨cons true (cons a L), cons false x3, .D⟩ = some ⟨L, cons a (cons false (cons true x3)), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (s3))))))⟩

/-- `A` entering `01 x`, nested visits E→C A→D: out in state E, leaving `01 x'`.  (In the run: 14816 times in the first 30,000,000 steps, first at step 16.) -/
theorem v_A_01_EcAd {x x1 x2 : Tape} (h1 : Vis .E x .C x1) (h2 : Vis .A x1 .D x2) :
    Vis .A (cons false (cons true x)) .E (cons false (cons true x2)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons true (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons a L))
  have s2 : steps 2 ⟨cons true (cons a L), cons false x2, .D⟩ = some ⟨L, cons a (cons false (cons true x2)), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `A` entering `01 x`, nested visits E→C A→E: out in state D, leaving `00 x'`.  (In the run: 10610 times in the first 30,000,000 steps, first at step 60.) -/
theorem v_A_01_EcAe {x x1 x2 : Tape} (h1 : Vis .E x .C x1) (h2 : Vis .A x1 .E x2) :
    Vis .A (cons false (cons true x)) .D (cons false (cons false x2)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons true (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons a L))
  have s2 : steps 2 ⟨cons true (cons a L), cons false x2, .E⟩ = some ⟨L, cons a (cons false (cons false x2)), .D⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `A` entering `01 x`, nested visits E→C A→F E→C A→D: out in state E, leaving `01 x'`.  (In the run: 1 times in the first 30,000,000 steps, first at step 3374.) -/
theorem v_A_01_EcAfEcAd {x x1 x2 x3 x4 : Tape} (h1 : Vis .E x .C x1) (h2 : Vis .A x1 .F x2) (h3 : Vis .E x2 .C x3) (h4 : Vis .A x3 .D x4) :
    Vis .A (cons false (cons true x)) .E (cons false (cons true x4)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons true (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons a L))
  have s2 : steps 1 ⟨cons true (cons a L), cons false x2, .F⟩ = some ⟨cons false (cons true (cons a L)), x2, .E⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons true (cons a L))
  have s3 : steps 1 ⟨cons true (cons a L), cons false x3, .C⟩ = some ⟨cons false (cons true (cons a L)), x3, .A⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons true (cons a L))
  have s4 : steps 2 ⟨cons true (cons a L), cons false x4, .D⟩ = some ⟨L, cons a (cons false (cons true x4)), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (s4))))))))⟩

/-- `B` entering `00 x`, no nested visit: out in state C, leaving `10 x'`.  (In the run: 963 times in the first 30,000,000 steps, first at step 78.) -/
theorem v_B_00_none {x : Tape}  :
    Vis .B (cons false (cons false x)) .C (cons true (cons false x)) := by
  intro a L
  have s0 : steps 1 ⟨cons a L, cons false (cons false x), .B⟩ = some ⟨L, cons a (cons true (cons false x)), .C⟩ := rfl
  exact ⟨_, s0⟩

/-- `B` entering `01 x`, no nested visit: out in state C, leaving `11 x'`.  (In the run: 273 times in the first 30,000,000 steps, first at step 32.) -/
theorem v_B_01_none {x : Tape}  :
    Vis .B (cons false (cons true x)) .C (cons true (cons true x)) := by
  intro a L
  have s0 : steps 1 ⟨cons a L, cons false (cons true x), .B⟩ = some ⟨L, cons a (cons true (cons true x)), .C⟩ := rfl
  exact ⟨_, s0⟩

/-- `B` entering `10 x`, nested visits B→A: out in state C, leaving `00 x'`.  (In the run: 933 times in the first 30,000,000 steps, first at step 70.) -/
theorem v_B_10_Ba {x x1 : Tape} (h1 : Vis .B x .A x1) :
    Vis .B (cons true (cons false x)) .C (cons false (cons false x1)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .B⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 2 ⟨cons false (cons a L), cons true x1, .A⟩ = some ⟨L, cons a (cons false (cons false x1)), .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `B` entering `10 x`, nested visits B→C: out in state A, leaving `10 x'`.  (In the run: 1576 times in the first 30,000,000 steps, first at step 80.) -/
theorem v_B_10_Bc {x x1 : Tape} (h1 : Vis .B x .C x1) :
    Vis .B (cons true (cons false x)) .A (cons true (cons false x1)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .B⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 2 ⟨cons false (cons a L), cons true x1, .C⟩ = some ⟨L, cons a (cons true (cons false x1)), .A⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `B` entering `10 x`, nested visits B→D B→C: out in state A, leaving `10 x'`.  (In the run: 30 times in the first 30,000,000 steps, first at step 144.) -/
theorem v_B_10_BdBc {x x1 x2 : Tape} (h1 : Vis .B x .D x1) (h2 : Vis .B x1 .C x2) :
    Vis .B (cons true (cons false x)) .A (cons true (cons false x2)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .B⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 5 ⟨cons false (cons a L), cons true x1, .D⟩ = some ⟨cons true (cons false (cons a L)), x1, .B⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 true (cons false (cons a L))
  have s2 : steps 2 ⟨cons false (cons a L), cons true x2, .C⟩ = some ⟨L, cons a (cons true (cons false x2)), .A⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `B` entering `10 x`, nested visits B→E A→C A→D E→C A→C A→D: out in state E, leaving `01 x'`.  (In the run: 1 times in the first 30,000,000 steps, first at step 1314.) -/
theorem v_B_10_BeAcAdEcAcAd {x x1 x2 x3 x4 x5 x6 : Tape} (h1 : Vis .B x .E x1) (h2 : Vis .A x1 .C x2) (h3 : Vis .A x2 .D x3) (h4 : Vis .E x3 .C x4) (h5 : Vis .A x4 .C x5) (h6 : Vis .A x5 .D x6) :
    Vis .B (cons true (cons false x)) .E (cons false (cons true x6)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .B⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons true x1, .E⟩ = some ⟨cons false (cons false (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a L))
  have s2 : steps 1 ⟨cons false (cons a L), cons false x2, .C⟩ = some ⟨cons false (cons false (cons a L)), x2, .A⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons false (cons a L))
  have s3 : steps 3 ⟨cons false (cons a L), cons false x3, .D⟩ = some ⟨cons false (cons true (cons a L)), x3, .E⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons true (cons a L))
  have s4 : steps 1 ⟨cons true (cons a L), cons false x4, .C⟩ = some ⟨cons false (cons true (cons a L)), x4, .A⟩ := rfl
  obtain ⟨t5, c5⟩ := h5 false (cons true (cons a L))
  have s5 : steps 1 ⟨cons true (cons a L), cons false x5, .C⟩ = some ⟨cons false (cons true (cons a L)), x5, .A⟩ := rfl
  obtain ⟨t6, c6⟩ := h6 false (cons true (cons a L))
  have s6 : steps 2 ⟨cons true (cons a L), cons false x6, .D⟩ = some ⟨L, cons a (cons false (cons true x6)), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (steps_seq trans s4 (steps_seq trans c5 (steps_seq trans s5 (steps_seq trans c6 (s6))))))))))))⟩

/-- `B` entering `10 x`, nested visits B→E A→D E→C A→D: out in state E, leaving `01 x'`.  (In the run: 1 times in the first 30,000,000 steps, first at step 5806.) -/
theorem v_B_10_BeAdEcAd {x x1 x2 x3 x4 : Tape} (h1 : Vis .B x .E x1) (h2 : Vis .A x1 .D x2) (h3 : Vis .E x2 .C x3) (h4 : Vis .A x3 .D x4) :
    Vis .B (cons true (cons false x)) .E (cons false (cons true x4)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .B⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons true x1, .E⟩ = some ⟨cons false (cons false (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a L))
  have s2 : steps 3 ⟨cons false (cons a L), cons false x2, .D⟩ = some ⟨cons false (cons true (cons a L)), x2, .E⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons true (cons a L))
  have s3 : steps 1 ⟨cons true (cons a L), cons false x3, .C⟩ = some ⟨cons false (cons true (cons a L)), x3, .A⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons true (cons a L))
  have s4 : steps 2 ⟨cons true (cons a L), cons false x4, .D⟩ = some ⟨L, cons a (cons false (cons true x4)), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (s4))))))))⟩

/-- `B` entering `10 x`, nested visits B→E A→E B→C: out in state A, leaving `10 x'`.  (In the run: 142 times in the first 30,000,000 steps, first at step 706.) -/
theorem v_B_10_BeAeBc {x x1 x2 x3 : Tape} (h1 : Vis .B x .E x1) (h2 : Vis .A x1 .E x2) (h3 : Vis .B x2 .C x3) :
    Vis .B (cons true (cons false x)) .A (cons true (cons false x3)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .B⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons true x1, .E⟩ = some ⟨cons false (cons false (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a L))
  have s2 : steps 3 ⟨cons false (cons a L), cons false x2, .E⟩ = some ⟨cons true (cons false (cons a L)), x2, .B⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 true (cons false (cons a L))
  have s3 : steps 2 ⟨cons false (cons a L), cons true x3, .C⟩ = some ⟨L, cons a (cons true (cons false x3)), .A⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (s3))))))⟩

/-- `B` entering `11 x`, nested visits A→A B→A: out in state C, leaving `00 x'`.  (In the run: 1 times in the first 30,000,000 steps, first at step 414.) -/
theorem v_B_11_AaBa {x x1 x2 : Tape} (h1 : Vis .A x .A x1) (h2 : Vis .B x1 .A x2) :
    Vis .B (cons true (cons true x)) .C (cons false (cons false x2)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons true x), .B⟩ = some ⟨cons false (cons false (cons a L)), x, .A⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons false x1, .A⟩ = some ⟨cons true (cons false (cons a L)), x1, .B⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 true (cons false (cons a L))
  have s2 : steps 2 ⟨cons false (cons a L), cons true x2, .A⟩ = some ⟨L, cons a (cons false (cons false x2)), .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `B` entering `11 x`, nested visits A→C A→D E→C A→C A→D: out in state E, leaving `01 x'`.  (In the run: 6 times in the first 30,000,000 steps, first at step 626.) -/
theorem v_B_11_AcAdEcAcAd {x x1 x2 x3 x4 x5 : Tape} (h1 : Vis .A x .C x1) (h2 : Vis .A x1 .D x2) (h3 : Vis .E x2 .C x3) (h4 : Vis .A x3 .C x4) (h5 : Vis .A x4 .D x5) :
    Vis .B (cons true (cons true x)) .E (cons false (cons true x5)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons true x), .B⟩ = some ⟨cons false (cons false (cons a L)), x, .A⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons false (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a L))
  have s2 : steps 3 ⟨cons false (cons a L), cons false x2, .D⟩ = some ⟨cons false (cons true (cons a L)), x2, .E⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons true (cons a L))
  have s3 : steps 1 ⟨cons true (cons a L), cons false x3, .C⟩ = some ⟨cons false (cons true (cons a L)), x3, .A⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons true (cons a L))
  have s4 : steps 1 ⟨cons true (cons a L), cons false x4, .C⟩ = some ⟨cons false (cons true (cons a L)), x4, .A⟩ := rfl
  obtain ⟨t5, c5⟩ := h5 false (cons true (cons a L))
  have s5 : steps 2 ⟨cons true (cons a L), cons false x5, .D⟩ = some ⟨L, cons a (cons false (cons true x5)), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (steps_seq trans s4 (steps_seq trans c5 (s5))))))))))⟩

/-- `B` entering `11 x`, nested visits A→D E→C A→D: out in state E, leaving `01 x'`.  (In the run: 230 times in the first 30,000,000 steps, first at step 1482.) -/
theorem v_B_11_AdEcAd {x x1 x2 x3 : Tape} (h1 : Vis .A x .D x1) (h2 : Vis .E x1 .C x2) (h3 : Vis .A x2 .D x3) :
    Vis .B (cons true (cons true x)) .E (cons false (cons true x3)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons true x), .B⟩ = some ⟨cons false (cons false (cons a L)), x, .A⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons a L))
  have s1 : steps 3 ⟨cons false (cons a L), cons false x1, .D⟩ = some ⟨cons false (cons true (cons a L)), x1, .E⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons a L))
  have s2 : steps 1 ⟨cons true (cons a L), cons false x2, .C⟩ = some ⟨cons false (cons true (cons a L)), x2, .A⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons true (cons a L))
  have s3 : steps 2 ⟨cons true (cons a L), cons false x3, .D⟩ = some ⟨L, cons a (cons false (cons true x3)), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (s3))))))⟩

/-- `B` entering `11 x`, nested visits A→D E→C A→E: out in state D, leaving `00 x'`.  (In the run: 31 times in the first 30,000,000 steps, first at step 136.) -/
theorem v_B_11_AdEcAe {x x1 x2 x3 : Tape} (h1 : Vis .A x .D x1) (h2 : Vis .E x1 .C x2) (h3 : Vis .A x2 .E x3) :
    Vis .B (cons true (cons true x)) .D (cons false (cons false x3)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons true x), .B⟩ = some ⟨cons false (cons false (cons a L)), x, .A⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons a L))
  have s1 : steps 3 ⟨cons false (cons a L), cons false x1, .D⟩ = some ⟨cons false (cons true (cons a L)), x1, .E⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons a L))
  have s2 : steps 1 ⟨cons true (cons a L), cons false x2, .C⟩ = some ⟨cons false (cons true (cons a L)), x2, .A⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons true (cons a L))
  have s3 : steps 2 ⟨cons true (cons a L), cons false x3, .E⟩ = some ⟨L, cons a (cons false (cons false x3)), .D⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (s3))))))⟩

/-- `B` entering `11 x`, nested visits A→E B→C: out in state A, leaving `10 x'`.  (In the run: 3 times in the first 30,000,000 steps, first at step 68.) -/
theorem v_B_11_AeBc {x x1 x2 : Tape} (h1 : Vis .A x .E x1) (h2 : Vis .B x1 .C x2) :
    Vis .B (cons true (cons true x)) .A (cons true (cons false x2)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons true x), .B⟩ = some ⟨cons false (cons false (cons a L)), x, .A⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons a L))
  have s1 : steps 3 ⟨cons false (cons a L), cons false x1, .E⟩ = some ⟨cons true (cons false (cons a L)), x1, .B⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 true (cons false (cons a L))
  have s2 : steps 2 ⟨cons false (cons a L), cons true x2, .C⟩ = some ⟨L, cons a (cons true (cons false x2)), .A⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `E` entering `00 x`, no nested visit: out in state C, leaving `00 x'`.  (In the run: 10001 times in the first 30,000,000 steps, first at step 10.) -/
theorem v_E_00_none {x : Tape}  :
    Vis .E (cons false (cons false x)) .C (cons false (cons false x)) := by
  intro a L
  have s0 : steps 1 ⟨cons a L, cons false (cons false x), .E⟩ = some ⟨L, cons a (cons false (cons false x)), .C⟩ := rfl
  exact ⟨_, s0⟩

/-- `E` entering `01 x`, no nested visit: out in state C, leaving `01 x'`.  (In the run: 25341 times in the first 30,000,000 steps, first at step 6.) -/
theorem v_E_01_none {x : Tape}  :
    Vis .E (cons false (cons true x)) .C (cons false (cons true x)) := by
  intro a L
  have s0 : steps 1 ⟨cons a L, cons false (cons true x), .E⟩ = some ⟨L, cons a (cons false (cons true x)), .C⟩ := rfl
  exact ⟨_, s0⟩

/-- `E` entering `10 x`, nested visits B→A: out in state C, leaving `00 x'`.  (In the run: 28 times in the first 30,000,000 steps, first at step 3460.) -/
theorem v_E_10_Ba {x x1 : Tape} (h1 : Vis .B x .A x1) :
    Vis .E (cons true (cons false x)) .C (cons false (cons false x1)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons false x), .E⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 2 ⟨cons false (cons a L), cons true x1, .A⟩ = some ⟨L, cons a (cons false (cons false x1)), .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `E` entering `10 x`, nested visits B→C: out in state A, leaving `10 x'`.  (In the run: 316 times in the first 30,000,000 steps, first at step 148.) -/
theorem v_E_10_Bc {x x1 : Tape} (h1 : Vis .B x .C x1) :
    Vis .E (cons true (cons false x)) .A (cons true (cons false x1)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons false x), .E⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 2 ⟨cons false (cons a L), cons true x1, .C⟩ = some ⟨L, cons a (cons true (cons false x1)), .A⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `E` entering `10 x`, nested visits B→E A→D E→C A→D: out in state E, leaving `01 x'`.  (In the run: 1 times in the first 30,000,000 steps, first at step 12564.) -/
theorem v_E_10_BeAdEcAd {x x1 x2 x3 x4 : Tape} (h1 : Vis .B x .E x1) (h2 : Vis .A x1 .D x2) (h3 : Vis .E x2 .C x3) (h4 : Vis .A x3 .D x4) :
    Vis .E (cons true (cons false x)) .E (cons false (cons true x4)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons false x), .E⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons true x1, .E⟩ = some ⟨cons false (cons false (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a L))
  have s2 : steps 3 ⟨cons false (cons a L), cons false x2, .D⟩ = some ⟨cons false (cons true (cons a L)), x2, .E⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons true (cons a L))
  have s3 : steps 1 ⟨cons true (cons a L), cons false x3, .C⟩ = some ⟨cons false (cons true (cons a L)), x3, .A⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons true (cons a L))
  have s4 : steps 2 ⟨cons true (cons a L), cons false x4, .D⟩ = some ⟨L, cons a (cons false (cons true x4)), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (s4))))))))⟩

/-- `E` entering `10 x`, nested visits B→E A→E B→C: out in state A, leaving `10 x'`.  (In the run: 78 times in the first 30,000,000 steps, first at step 970.) -/
theorem v_E_10_BeAeBc {x x1 x2 x3 : Tape} (h1 : Vis .B x .E x1) (h2 : Vis .A x1 .E x2) (h3 : Vis .B x2 .C x3) :
    Vis .E (cons true (cons false x)) .A (cons true (cons false x3)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons false x), .E⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons true x1, .E⟩ = some ⟨cons false (cons false (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a L))
  have s2 : steps 3 ⟨cons false (cons a L), cons false x2, .E⟩ = some ⟨cons true (cons false (cons a L)), x2, .B⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 true (cons false (cons a L))
  have s3 : steps 2 ⟨cons false (cons a L), cons true x3, .C⟩ = some ⟨L, cons a (cons true (cons false x3)), .A⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (s3))))))⟩

end H43701
