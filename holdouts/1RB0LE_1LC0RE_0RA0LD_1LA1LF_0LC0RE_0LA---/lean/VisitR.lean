import Machine

/-! # Visit laws of 1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LA--- (right side)

Every theorem below is one row of a token-level visit law (mined from the run by `py/vislaws.c`, written by
`py/gen_visit2.py`): what one visit does to a stream that starts with the token, given what the nested visits of the
rest of the stream do.  Rows are exact for every stream (the hypotheses are about the rest only). -/

namespace H2327

open TM

/-- One visit of the stream `x` (right of the head's cell) in state `q`: back out on the left in state `r`, leaving
`x'`; the cell it lands on and everything left of it are untouched. -/
def Vis (q : St) (x : Tape) (r : St) (x' : Tape) : Prop :=
  ∀ (a : Bool) (L : Tape), ∃ t, steps t ⟨cons a L, x, q⟩ = some ⟨L, cons a x', r⟩

/-- `A` entering `00 x`, no nested visit: out in state D, leaving `01 x'`.  (In the run: 866 times in the first 30,000,000 steps, first at step 14.) -/
theorem v_A_00_none {x : Tape}  :
    Vis .A (cons false (cons false x)) .D (cons false (cons true x)) := by
  intro a L
  have s0 : steps 3 ⟨cons a L, cons false (cons false x), .A⟩ = some ⟨L, cons a (cons false (cons true x)), .D⟩ := rfl
  exact ⟨_, s0⟩

/-- `A` entering `01 x`, nested visits E→A B→A B→A: out in state C, leaving `00 x'`.  (In the run: 229 times in the first 30,000,000 steps, first at step 430.) -/
theorem v_A_01_EaBaBa {x x1 x2 x3 : Tape} (h1 : Vis .E x .A x1) (h2 : Vis .B x1 .A x2) (h3 : Vis .B x2 .A x3) :
    Vis .A (cons false (cons true x)) .C (cons false (cons false x3)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .A⟩ = some ⟨cons true (cons true (cons a L)), x1, .B⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 true (cons true (cons a L))
  have s2 : steps 5 ⟨cons true (cons a L), cons true x2, .A⟩ = some ⟨cons true (cons false (cons a L)), x2, .B⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 true (cons false (cons a L))
  have s3 : steps 2 ⟨cons false (cons a L), cons true x3, .A⟩ = some ⟨L, cons a (cons false (cons false x3)), .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (s3))))))⟩

/-- `A` entering `01 x`, nested visits E→A B→A B→C: out in state A, leaving `10 x'`.  (In the run: 2 times in the first 30,000,000 steps, first at step 176.) -/
theorem v_A_01_EaBaBc {x x1 x2 x3 : Tape} (h1 : Vis .E x .A x1) (h2 : Vis .B x1 .A x2) (h3 : Vis .B x2 .C x3) :
    Vis .A (cons false (cons true x)) .A (cons true (cons false x3)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .A⟩ = some ⟨cons true (cons true (cons a L)), x1, .B⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 true (cons true (cons a L))
  have s2 : steps 5 ⟨cons true (cons a L), cons true x2, .A⟩ = some ⟨cons true (cons false (cons a L)), x2, .B⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 true (cons false (cons a L))
  have s3 : steps 2 ⟨cons false (cons a L), cons true x3, .C⟩ = some ⟨L, cons a (cons true (cons false x3)), .A⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (s3))))))⟩

/-- `A` entering `01 x`, nested visits E→A B→C: out in state F, leaving `10 x'`.  (In the run: 4 times in the first 30,000,000 steps, first at step 336.) -/
theorem v_A_01_EaBc {x x1 x2 : Tape} (h1 : Vis .E x .A x1) (h2 : Vis .B x1 .C x2) :
    Vis .A (cons false (cons true x)) .F (cons true (cons false x2)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .A⟩ = some ⟨cons true (cons true (cons a L)), x1, .B⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 true (cons true (cons a L))
  have s2 : steps 2 ⟨cons true (cons a L), cons true x2, .C⟩ = some ⟨L, cons a (cons true (cons false x2)), .F⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `A` entering `01 x`, nested visits E→C A→C A→D: out in state E, leaving `01 x'`.  (In the run: 204 times in the first 30,000,000 steps, first at step 712.) -/
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

/-- `A` entering `01 x`, nested visits E→C A→D: out in state E, leaving `01 x'`.  (In the run: 702 times in the first 30,000,000 steps, first at step 16.) -/
theorem v_A_01_EcAd {x x1 x2 : Tape} (h1 : Vis .E x .C x1) (h2 : Vis .A x1 .D x2) :
    Vis .A (cons false (cons true x)) .E (cons false (cons true x2)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons true (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons a L))
  have s2 : steps 2 ⟨cons true (cons a L), cons false x2, .D⟩ = some ⟨L, cons a (cons false (cons true x2)), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `A` entering `01 x`, nested visits E→C A→E: out in state D, leaving `00 x'`.  (In the run: 604 times in the first 30,000,000 steps, first at step 62.) -/
theorem v_A_01_EcAe {x x1 x2 : Tape} (h1 : Vis .E x .C x1) (h2 : Vis .A x1 .E x2) :
    Vis .A (cons false (cons true x)) .D (cons false (cons false x2)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons true (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons a L))
  have s2 : steps 2 ⟨cons true (cons a L), cons false x2, .E⟩ = some ⟨L, cons a (cons false (cons false x2)), .D⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `B` entering `00 x`, no nested visit: out in state C, leaving `10 x'`.  (In the run: 1918 times in the first 30,000,000 steps, first at step 80.) -/
theorem v_B_00_none {x : Tape}  :
    Vis .B (cons false (cons false x)) .C (cons true (cons false x)) := by
  intro a L
  have s0 : steps 1 ⟨cons a L, cons false (cons false x), .B⟩ = some ⟨L, cons a (cons true (cons false x)), .C⟩ := rfl
  exact ⟨_, s0⟩

/-- `B` entering `01 x`, no nested visit: out in state C, leaving `11 x'`.  (In the run: 304 times in the first 30,000,000 steps, first at step 32.) -/
theorem v_B_01_none {x : Tape}  :
    Vis .B (cons false (cons true x)) .C (cons true (cons true x)) := by
  intro a L
  have s0 : steps 1 ⟨cons a L, cons false (cons true x), .B⟩ = some ⟨L, cons a (cons true (cons true x)), .C⟩ := rfl
  exact ⟨_, s0⟩

/-- `B` entering `10 x`, nested visits B→A: out in state C, leaving `00 x'`.  (In the run: 1921 times in the first 30,000,000 steps, first at step 72.) -/
theorem v_B_10_Ba {x x1 : Tape} (h1 : Vis .B x .A x1) :
    Vis .B (cons true (cons false x)) .C (cons false (cons false x1)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .B⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 2 ⟨cons false (cons a L), cons true x1, .A⟩ = some ⟨L, cons a (cons false (cons false x1)), .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `B` entering `10 x`, nested visits B→C: out in state A, leaving `10 x'`.  (In the run: 2668 times in the first 30,000,000 steps, first at step 82.) -/
theorem v_B_10_Bc {x x1 : Tape} (h1 : Vis .B x .C x1) :
    Vis .B (cons true (cons false x)) .A (cons true (cons false x1)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .B⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 2 ⟨cons false (cons a L), cons true x1, .C⟩ = some ⟨L, cons a (cons true (cons false x1)), .A⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `B` entering `10 x`, nested visits B→D: out in state A, leaving `01 x'`.  (In the run: 3 times in the first 30,000,000 steps, first at step 144.) -/
theorem v_B_10_Bd {x x1 : Tape} (h1 : Vis .B x .D x1) :
    Vis .B (cons true (cons false x)) .A (cons false (cons true x1)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .B⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 2 ⟨cons false (cons a L), cons true x1, .D⟩ = some ⟨L, cons a (cons false (cons true x1)), .A⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `B` entering `10 x`, nested visits B→E E→C A→D E→C A→C A→D: out in state E, leaving `01 x'`.  (In the run: 1 times in the first 30,000,000 steps, first at step 1950.) -/
theorem v_B_10_BeEcAdEcAcAd {x x1 x2 x3 x4 x5 x6 : Tape} (h1 : Vis .B x .E x1) (h2 : Vis .E x1 .C x2) (h3 : Vis .A x2 .D x3) (h4 : Vis .E x3 .C x4) (h5 : Vis .A x4 .C x5) (h6 : Vis .A x5 .D x6) :
    Vis .B (cons true (cons false x)) .E (cons false (cons true x6)) := by
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
  have s5 : steps 1 ⟨cons true (cons a L), cons false x5, .C⟩ = some ⟨cons false (cons true (cons a L)), x5, .A⟩ := rfl
  obtain ⟨t6, c6⟩ := h6 false (cons true (cons a L))
  have s6 : steps 2 ⟨cons true (cons a L), cons false x6, .D⟩ = some ⟨L, cons a (cons false (cons true x6)), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (steps_seq trans s4 (steps_seq trans c5 (steps_seq trans s5 (steps_seq trans c6 (s6))))))))))))⟩

/-- `B` entering `10 x`, nested visits B→E E→C A→E B→C: out in state A, leaving `10 x'`.  (In the run: 276 times in the first 30,000,000 steps, first at step 248.) -/
theorem v_B_10_BeEcAeBc {x x1 x2 x3 x4 : Tape} (h1 : Vis .B x .E x1) (h2 : Vis .E x1 .C x2) (h3 : Vis .A x2 .E x3) (h4 : Vis .B x3 .C x4) :
    Vis .B (cons true (cons false x)) .A (cons true (cons false x4)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .B⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons true x1, .E⟩ = some ⟨cons false (cons false (cons a L)), x1, .E⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a L))
  have s2 : steps 1 ⟨cons false (cons a L), cons false x2, .C⟩ = some ⟨cons false (cons false (cons a L)), x2, .A⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons false (cons a L))
  have s3 : steps 3 ⟨cons false (cons a L), cons false x3, .E⟩ = some ⟨cons true (cons false (cons a L)), x3, .B⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 true (cons false (cons a L))
  have s4 : steps 2 ⟨cons false (cons a L), cons true x4, .C⟩ = some ⟨L, cons a (cons true (cons false x4)), .A⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (s4))))))))⟩

/-- `B` entering `11 x`, nested visits E→C A→C A→D E→C A→C A→D: out in state E, leaving `01 x'`.  (In the run: 10 times in the first 30,000,000 steps, first at step 632.) -/
theorem v_B_11_EcAcAdEcAcAd {x x1 x2 x3 x4 x5 x6 : Tape} (h1 : Vis .E x .C x1) (h2 : Vis .A x1 .C x2) (h3 : Vis .A x2 .D x3) (h4 : Vis .E x3 .C x4) (h5 : Vis .A x4 .C x5) (h6 : Vis .A x5 .D x6) :
    Vis .B (cons true (cons true x)) .E (cons false (cons true x6)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons true x), .B⟩ = some ⟨cons false (cons false (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons false (cons a L)), x1, .A⟩ := rfl
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

/-- `B` entering `11 x`, nested visits E→C A→C A→D E→C A→E: out in state D, leaving `00 x'`.  (In the run: 1 times in the first 30,000,000 steps, first at step 4296.) -/
theorem v_B_11_EcAcAdEcAe {x x1 x2 x3 x4 x5 : Tape} (h1 : Vis .E x .C x1) (h2 : Vis .A x1 .C x2) (h3 : Vis .A x2 .D x3) (h4 : Vis .E x3 .C x4) (h5 : Vis .A x4 .E x5) :
    Vis .B (cons true (cons true x)) .D (cons false (cons false x5)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons true x), .B⟩ = some ⟨cons false (cons false (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons false (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a L))
  have s2 : steps 1 ⟨cons false (cons a L), cons false x2, .C⟩ = some ⟨cons false (cons false (cons a L)), x2, .A⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons false (cons a L))
  have s3 : steps 3 ⟨cons false (cons a L), cons false x3, .D⟩ = some ⟨cons false (cons true (cons a L)), x3, .E⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons true (cons a L))
  have s4 : steps 1 ⟨cons true (cons a L), cons false x4, .C⟩ = some ⟨cons false (cons true (cons a L)), x4, .A⟩ := rfl
  obtain ⟨t5, c5⟩ := h5 false (cons true (cons a L))
  have s5 : steps 2 ⟨cons true (cons a L), cons false x5, .E⟩ = some ⟨L, cons a (cons false (cons false x5)), .D⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (steps_seq trans s4 (steps_seq trans c5 (s5))))))))))⟩

/-- `B` entering `11 x`, nested visits E→C A→C A→D E→C A→F: out in state E, leaving `00 x'`.  (In the run: 1 times in the first 30,000,000 steps, first at step 1890.) -/
theorem v_B_11_EcAcAdEcAf {x x1 x2 x3 x4 x5 : Tape} (h1 : Vis .E x .C x1) (h2 : Vis .A x1 .C x2) (h3 : Vis .A x2 .D x3) (h4 : Vis .E x3 .C x4) (h5 : Vis .A x4 .F x5) :
    Vis .B (cons true (cons true x)) .E (cons false (cons false x5)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons true x), .B⟩ = some ⟨cons false (cons false (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons false (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a L))
  have s2 : steps 1 ⟨cons false (cons a L), cons false x2, .C⟩ = some ⟨cons false (cons false (cons a L)), x2, .A⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons false (cons a L))
  have s3 : steps 3 ⟨cons false (cons a L), cons false x3, .D⟩ = some ⟨cons false (cons true (cons a L)), x3, .E⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons true (cons a L))
  have s4 : steps 1 ⟨cons true (cons a L), cons false x4, .C⟩ = some ⟨cons false (cons true (cons a L)), x4, .A⟩ := rfl
  obtain ⟨t5, c5⟩ := h5 false (cons true (cons a L))
  have s5 : steps 2 ⟨cons true (cons a L), cons false x5, .F⟩ = some ⟨L, cons a (cons false (cons false x5)), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (steps_seq trans s4 (steps_seq trans c5 (s5))))))))))⟩

/-- `B` entering `11 x`, nested visits E→C A→D E→C A→D: out in state E, leaving `01 x'`.  (In the run: 265 times in the first 30,000,000 steps, first at step 230.) -/
theorem v_B_11_EcAdEcAd {x x1 x2 x3 x4 : Tape} (h1 : Vis .E x .C x1) (h2 : Vis .A x1 .D x2) (h3 : Vis .E x2 .C x3) (h4 : Vis .A x3 .D x4) :
    Vis .B (cons true (cons true x)) .E (cons false (cons true x4)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons true x), .B⟩ = some ⟨cons false (cons false (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons false (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a L))
  have s2 : steps 3 ⟨cons false (cons a L), cons false x2, .D⟩ = some ⟨cons false (cons true (cons a L)), x2, .E⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons true (cons a L))
  have s3 : steps 1 ⟨cons true (cons a L), cons false x3, .C⟩ = some ⟨cons false (cons true (cons a L)), x3, .A⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons true (cons a L))
  have s4 : steps 2 ⟨cons true (cons a L), cons false x4, .D⟩ = some ⟨L, cons a (cons false (cons true x4)), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (s4))))))))⟩

/-- `B` entering `11 x`, nested visits E→C A→D E→C A→E: out in state D, leaving `00 x'`.  (In the run: 2 times in the first 30,000,000 steps, first at step 142.) -/
theorem v_B_11_EcAdEcAe {x x1 x2 x3 x4 : Tape} (h1 : Vis .E x .C x1) (h2 : Vis .A x1 .D x2) (h3 : Vis .E x2 .C x3) (h4 : Vis .A x3 .E x4) :
    Vis .B (cons true (cons true x)) .D (cons false (cons false x4)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons true x), .B⟩ = some ⟨cons false (cons false (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons false (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a L))
  have s2 : steps 3 ⟨cons false (cons a L), cons false x2, .D⟩ = some ⟨cons false (cons true (cons a L)), x2, .E⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons true (cons a L))
  have s3 : steps 1 ⟨cons true (cons a L), cons false x3, .C⟩ = some ⟨cons false (cons true (cons a L)), x3, .A⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons true (cons a L))
  have s4 : steps 2 ⟨cons true (cons a L), cons false x4, .E⟩ = some ⟨L, cons a (cons false (cons false x4)), .D⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (s4))))))))⟩

/-- `B` entering `11 x`, nested visits E→C A→E B→C: out in state A, leaving `10 x'`.  (In the run: 22 times in the first 30,000,000 steps, first at step 70.) -/
theorem v_B_11_EcAeBc {x x1 x2 x3 : Tape} (h1 : Vis .E x .C x1) (h2 : Vis .A x1 .E x2) (h3 : Vis .B x2 .C x3) :
    Vis .B (cons true (cons true x)) .A (cons true (cons false x3)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons true x), .B⟩ = some ⟨cons false (cons false (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons false (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a L))
  have s2 : steps 3 ⟨cons false (cons a L), cons false x2, .E⟩ = some ⟨cons true (cons false (cons a L)), x2, .B⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 true (cons false (cons a L))
  have s3 : steps 2 ⟨cons false (cons a L), cons true x3, .C⟩ = some ⟨L, cons a (cons true (cons false x3)), .A⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (s3))))))⟩

/-- `B` entering `11 x`, nested visits E→C A→F: out in state D, leaving `01 x'`.  (In the run: 1 times in the first 30,000,000 steps, first at step 840.) -/
theorem v_B_11_EcAf {x x1 x2 : Tape} (h1 : Vis .E x .C x1) (h2 : Vis .A x1 .F x2) :
    Vis .B (cons true (cons true x)) .D (cons false (cons true x2)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons true x), .B⟩ = some ⟨cons false (cons false (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons false (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a L))
  have s2 : steps 4 ⟨cons false (cons a L), cons false x2, .F⟩ = some ⟨L, cons a (cons false (cons true x2)), .D⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `E` entering `00 x`, no nested visit: out in state C, leaving `00 x'`.  (In the run: 622 times in the first 30,000,000 steps, first at step 10.) -/
theorem v_E_00_none {x : Tape}  :
    Vis .E (cons false (cons false x)) .C (cons false (cons false x)) := by
  intro a L
  have s0 : steps 1 ⟨cons a L, cons false (cons false x), .E⟩ = some ⟨L, cons a (cons false (cons false x)), .C⟩ := rfl
  exact ⟨_, s0⟩

/-- `E` entering `01 x`, no nested visit: out in state C, leaving `01 x'`.  (In the run: 1745 times in the first 30,000,000 steps, first at step 6.) -/
theorem v_E_01_none {x : Tape}  :
    Vis .E (cons false (cons true x)) .C (cons false (cons true x)) := by
  intro a L
  have s0 : steps 1 ⟨cons a L, cons false (cons true x), .E⟩ = some ⟨L, cons a (cons false (cons true x)), .C⟩ := rfl
  exact ⟨_, s0⟩

/-- `E` entering `10 x`, nested visits B→A: out in state C, leaving `00 x'`.  (In the run: 10 times in the first 30,000,000 steps, first at step 4288.) -/
theorem v_E_10_Ba {x x1 : Tape} (h1 : Vis .B x .A x1) :
    Vis .E (cons true (cons false x)) .C (cons false (cons false x1)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .E⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 2 ⟨cons false (cons a L), cons true x1, .A⟩ = some ⟨L, cons a (cons false (cons false x1)), .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `E` entering `10 x`, nested visits B→C: out in state A, leaving `10 x'`.  (In the run: 234 times in the first 30,000,000 steps, first at step 148.) -/
theorem v_E_10_Bc {x x1 : Tape} (h1 : Vis .B x .C x1) :
    Vis .E (cons true (cons false x)) .A (cons true (cons false x1)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .E⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 2 ⟨cons false (cons a L), cons true x1, .C⟩ = some ⟨L, cons a (cons true (cons false x1)), .A⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `E` entering `10 x`, nested visits B→D: out in state A, leaving `01 x'`.  (In the run: 1 times in the first 30,000,000 steps, first at step 842.) -/
theorem v_E_10_Bd {x x1 : Tape} (h1 : Vis .B x .D x1) :
    Vis .E (cons true (cons false x)) .A (cons false (cons true x1)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .E⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 2 ⟨cons false (cons a L), cons true x1, .D⟩ = some ⟨L, cons a (cons false (cons true x1)), .A⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

end H2327
