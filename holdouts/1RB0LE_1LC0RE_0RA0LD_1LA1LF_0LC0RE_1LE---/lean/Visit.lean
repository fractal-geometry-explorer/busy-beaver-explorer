import Machine

/-! # Visit laws of 1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_1LE---

`Vis q x r x'`: the head enters the stream `x` from the left in state `q` (on its first cell) and the first time it
leaves `x` to the left it is in state `r` and the stream is `x'`; the cell it lands on and everything left of it are
untouched.  Every theorem below is one row of the token-level law (tokens of 2 cells, mined from the run by
`py/laws.py`, written by `py/gen_visit.py`): what one visit does to a stream that starts with the token, given what
the nested visits of the rest of the stream do.  The rows are exact for every stream (the hypotheses are about the
rest of the stream only), so they can be composed by induction into laws for whole counters. -/

namespace H64715

open TM

/-- One visit of the stream `x` in state `q`: back out on the left in state `r`, leaving `x'`. -/
def Vis (q : St) (x : Tape) (r : St) (x' : Tape) : Prop :=
  ∀ (a : Bool) (L : Tape), ∃ t, steps t ⟨cons a L, x, q⟩ = some ⟨L, cons a x', r⟩

/-- `A> 00 x`, no nested visit: out in state D, leaving `01 x'`.  (In the run: 36871 times in 3·10^7 steps, first at step 33.) -/
theorem v_A_00_none {x : Tape}  :
    Vis .A (cons false (cons false x)) .D (cons false (cons true x)) := by
  intro a L
  have s0 : steps 3 ⟨cons a L, cons false (cons false x), .A⟩ = some ⟨L, cons a (cons false (cons true x)), .D⟩ := rfl
  exact ⟨_, s0⟩

/-- `A> 01 x`, nested visits E→A B→A B→A: out in state C, leaving `00 x'`.  (In the run: 10484 times in 3·10^7 steps, first at step 319.) -/
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

/-- `A> 01 x`, nested visits E→A B→A B→C: out in state A, leaving `10 x'`.  (In the run: 1 times in 3·10^7 steps, first at step 8061.) -/
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

/-- `A> 01 x`, nested visits E→A B→A B→E E→E B→C: out in state A, leaving `10 x'`.  (In the run: 1 times in 3·10^7 steps, first at step 3475.) -/
theorem v_A_01_EaBaBeEeBc {x x1 x2 x3 x4 x5 : Tape} (h1 : Vis .E x .A x1) (h2 : Vis .B x1 .A x2) (h3 : Vis .B x2 .E x3) (h4 : Vis .E x3 .E x4) (h5 : Vis .B x4 .C x5) :
    Vis .A (cons false (cons true x)) .A (cons true (cons false x5)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .A⟩ = some ⟨cons true (cons true (cons a L)), x1, .B⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 true (cons true (cons a L))
  have s2 : steps 5 ⟨cons true (cons a L), cons true x2, .A⟩ = some ⟨cons true (cons false (cons a L)), x2, .B⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 true (cons false (cons a L))
  have s3 : steps 1 ⟨cons false (cons a L), cons true x3, .E⟩ = some ⟨cons false (cons false (cons a L)), x3, .E⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons false (cons a L))
  have s4 : steps 3 ⟨cons false (cons a L), cons false x4, .E⟩ = some ⟨cons true (cons false (cons a L)), x4, .B⟩ := rfl
  obtain ⟨t5, c5⟩ := h5 true (cons false (cons a L))
  have s5 : steps 2 ⟨cons false (cons a L), cons true x5, .C⟩ = some ⟨L, cons a (cons true (cons false x5)), .A⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (steps_seq trans s4 (steps_seq trans c5 (s5))))))))))⟩

/-- `A> 01 x`, nested visits E→A B→C: out in state F, leaving `10 x'`.  (In the run: 6 times in 3·10^7 steps, first at step 143.) -/
theorem v_A_01_EaBc {x x1 x2 : Tape} (h1 : Vis .E x .A x1) (h2 : Vis .B x1 .C x2) :
    Vis .A (cons false (cons true x)) .F (cons true (cons false x2)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .A⟩ = some ⟨cons true (cons true (cons a L)), x1, .B⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 true (cons true (cons a L))
  have s2 : steps 2 ⟨cons true (cons a L), cons true x2, .C⟩ = some ⟨L, cons a (cons true (cons false x2)), .F⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `A> 01 x`, nested visits E→A B→E E→C A→E: out in state D, leaving `00 x'`.  (In the run: 1 times in 3·10^7 steps, first at step 1259.) -/
theorem v_A_01_EaBeEcAe {x x1 x2 x3 x4 : Tape} (h1 : Vis .E x .A x1) (h2 : Vis .B x1 .E x2) (h3 : Vis .E x2 .C x3) (h4 : Vis .A x3 .E x4) :
    Vis .A (cons false (cons true x)) .D (cons false (cons false x4)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .A⟩ = some ⟨cons true (cons true (cons a L)), x1, .B⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 true (cons true (cons a L))
  have s2 : steps 1 ⟨cons true (cons a L), cons true x2, .E⟩ = some ⟨cons false (cons true (cons a L)), x2, .E⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons true (cons a L))
  have s3 : steps 1 ⟨cons true (cons a L), cons false x3, .C⟩ = some ⟨cons false (cons true (cons a L)), x3, .A⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons true (cons a L))
  have s4 : steps 2 ⟨cons true (cons a L), cons false x4, .E⟩ = some ⟨L, cons a (cons false (cons false x4)), .D⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (s4))))))))⟩

/-- `A> 01 x`, nested visits E→C A→A B→A B→A: out in state C, leaving `00 x'`.  (In the run: 2 times in 3·10^7 steps, first at step 3789.) -/
theorem v_A_01_EcAaBaBa {x x1 x2 x3 x4 : Tape} (h1 : Vis .E x .C x1) (h2 : Vis .A x1 .A x2) (h3 : Vis .B x2 .A x3) (h4 : Vis .B x3 .A x4) :
    Vis .A (cons false (cons true x)) .C (cons false (cons false x4)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons true (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons a L))
  have s2 : steps 1 ⟨cons true (cons a L), cons false x2, .A⟩ = some ⟨cons true (cons true (cons a L)), x2, .B⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 true (cons true (cons a L))
  have s3 : steps 5 ⟨cons true (cons a L), cons true x3, .A⟩ = some ⟨cons true (cons false (cons a L)), x3, .B⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 true (cons false (cons a L))
  have s4 : steps 2 ⟨cons false (cons a L), cons true x4, .A⟩ = some ⟨L, cons a (cons false (cons false x4)), .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (s4))))))))⟩

/-- `A> 01 x`, nested visits E→C A→C A→D: out in state E, leaving `01 x'`.  (In the run: 9325 times in 3·10^7 steps, first at step 181.) -/
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

/-- `A> 01 x`, nested visits E→C A→D: out in state E, leaving `01 x'`.  (In the run: 27459 times in 3·10^7 steps, first at step 71.) -/
theorem v_A_01_EcAd {x x1 x2 : Tape} (h1 : Vis .E x .C x1) (h2 : Vis .A x1 .D x2) :
    Vis .A (cons false (cons true x)) .E (cons false (cons true x2)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons true (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons a L))
  have s2 : steps 2 ⟨cons true (cons a L), cons false x2, .D⟩ = some ⟨L, cons a (cons false (cons true x2)), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `A> 01 x`, nested visits E→C A→E: out in state D, leaving `00 x'`.  (In the run: 26366 times in 3·10^7 steps, first at step 1343.) -/
theorem v_A_01_EcAe {x x1 x2 : Tape} (h1 : Vis .E x .C x1) (h2 : Vis .A x1 .E x2) :
    Vis .A (cons false (cons true x)) .D (cons false (cons false x2)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons true (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons a L))
  have s2 : steps 2 ⟨cons true (cons a L), cons false x2, .E⟩ = some ⟨L, cons a (cons false (cons false x2)), .D⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `A> 01 x`, nested visits E→C A→F E→A B→A: out in state C, leaving `00 x'`.  (In the run: 3 times in 3·10^7 steps, first at step 175.) -/
theorem v_A_01_EcAfEaBa {x x1 x2 x3 x4 : Tape} (h1 : Vis .E x .C x1) (h2 : Vis .A x1 .F x2) (h3 : Vis .E x2 .A x3) (h4 : Vis .B x3 .A x4) :
    Vis .A (cons false (cons true x)) .C (cons false (cons false x4)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 1 ⟨cons true (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons true (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons true (cons a L))
  have s2 : steps 3 ⟨cons true (cons a L), cons false x2, .F⟩ = some ⟨cons false (cons false (cons a L)), x2, .E⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons false (cons a L))
  have s3 : steps 1 ⟨cons false (cons a L), cons false x3, .A⟩ = some ⟨cons true (cons false (cons a L)), x3, .B⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 true (cons false (cons a L))
  have s4 : steps 2 ⟨cons false (cons a L), cons true x4, .A⟩ = some ⟨L, cons a (cons false (cons false x4)), .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (s4))))))))⟩

/-- `A> 01 x`, nested visits E→E: out in state D, leaving `00 x'`.  (In the run: 1 times in 3·10^7 steps, first at step 132131.) -/
theorem v_A_01_Ee {x x1 : Tape} (h1 : Vis .E x .E x1) :
    Vis .A (cons false (cons true x)) .D (cons false (cons false x1)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons false (cons true x), .A⟩ = some ⟨cons false (cons true (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons true (cons a L))
  have s1 : steps 2 ⟨cons true (cons a L), cons false x1, .E⟩ = some ⟨L, cons a (cons false (cons false x1)), .D⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `B> 00 x`, no nested visit: out in state C, leaving `10 x'`.  (In the run: 42360 times in 3·10^7 steps, first at step 1.) -/
theorem v_B_00_none {x : Tape}  :
    Vis .B (cons false (cons false x)) .C (cons true (cons false x)) := by
  intro a L
  have s0 : steps 1 ⟨cons a L, cons false (cons false x), .B⟩ = some ⟨L, cons a (cons true (cons false x)), .C⟩ := rfl
  exact ⟨_, s0⟩

/-- `B> 01 x`, no nested visit: out in state C, leaving `11 x'`.  (In the run: 10424 times in 3·10^7 steps, first at step 87.) -/
theorem v_B_01_none {x : Tape}  :
    Vis .B (cons false (cons true x)) .C (cons true (cons true x)) := by
  intro a L
  have s0 : steps 1 ⟨cons a L, cons false (cons true x), .B⟩ = some ⟨L, cons a (cons true (cons true x)), .C⟩ := rfl
  exact ⟨_, s0⟩

/-- `B> 10 x`, nested visits B→A: out in state C, leaving `00 x'`.  (In the run: 42345 times in 3·10^7 steps, first at step 17.) -/
theorem v_B_10_Ba {x x1 : Tape} (h1 : Vis .B x .A x1) :
    Vis .B (cons true (cons false x)) .C (cons false (cons false x1)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .B⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 2 ⟨cons false (cons a L), cons true x1, .A⟩ = some ⟨L, cons a (cons false (cons false x1)), .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `B> 10 x`, nested visits B→C: out in state A, leaving `10 x'`.  (In the run: 63443 times in 3·10^7 steps, first at step 15.) -/
theorem v_B_10_Bc {x x1 : Tape} (h1 : Vis .B x .C x1) :
    Vis .B (cons true (cons false x)) .A (cons true (cons false x1)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .B⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 2 ⟨cons false (cons a L), cons true x1, .C⟩ = some ⟨L, cons a (cons true (cons false x1)), .A⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `B> 10 x`, nested visits B→D: out in state E, leaving `11 x'`.  (In the run: 1 times in 3·10^7 steps, first at step 3383.) -/
theorem v_B_10_Bd {x x1 : Tape} (h1 : Vis .B x .D x1) :
    Vis .B (cons true (cons false x)) .E (cons true (cons true x1)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .B⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 2 ⟨cons false (cons a L), cons true x1, .D⟩ = some ⟨L, cons a (cons true (cons true x1)), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `B> 10 x`, nested visits B→E E→C A→C A→D E→C A→C A→D: out in state E, leaving `01 x'`.  (In the run: 2 times in 3·10^7 steps, first at step 1165.) -/
theorem v_B_10_BeEcAcAdEcAcAd {x x1 x2 x3 x4 x5 x6 x7 : Tape} (h1 : Vis .B x .E x1) (h2 : Vis .E x1 .C x2) (h3 : Vis .A x2 .C x3) (h4 : Vis .A x3 .D x4) (h5 : Vis .E x4 .C x5) (h6 : Vis .A x5 .C x6) (h7 : Vis .A x6 .D x7) :
    Vis .B (cons true (cons false x)) .E (cons false (cons true x7)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .B⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons true x1, .E⟩ = some ⟨cons false (cons false (cons a L)), x1, .E⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a L))
  have s2 : steps 1 ⟨cons false (cons a L), cons false x2, .C⟩ = some ⟨cons false (cons false (cons a L)), x2, .A⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons false (cons a L))
  have s3 : steps 1 ⟨cons false (cons a L), cons false x3, .C⟩ = some ⟨cons false (cons false (cons a L)), x3, .A⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons false (cons a L))
  have s4 : steps 3 ⟨cons false (cons a L), cons false x4, .D⟩ = some ⟨cons false (cons true (cons a L)), x4, .E⟩ := rfl
  obtain ⟨t5, c5⟩ := h5 false (cons true (cons a L))
  have s5 : steps 1 ⟨cons true (cons a L), cons false x5, .C⟩ = some ⟨cons false (cons true (cons a L)), x5, .A⟩ := rfl
  obtain ⟨t6, c6⟩ := h6 false (cons true (cons a L))
  have s6 : steps 1 ⟨cons true (cons a L), cons false x6, .C⟩ = some ⟨cons false (cons true (cons a L)), x6, .A⟩ := rfl
  obtain ⟨t7, c7⟩ := h7 false (cons true (cons a L))
  have s7 : steps 2 ⟨cons true (cons a L), cons false x7, .D⟩ = some ⟨L, cons a (cons false (cons true x7)), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (steps_seq trans s4 (steps_seq trans c5 (steps_seq trans s5 (steps_seq trans c6 (steps_seq trans s6 (steps_seq trans c7 (s7))))))))))))))⟩

/-- `B> 10 x`, nested visits B→E E→C A→E B→C: out in state A, leaving `10 x'`.  (In the run: 8415 times in 3·10^7 steps, first at step 557.) -/
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

/-- `B> 11 x`, nested visits E→A B→A: out in state C, leaving `00 x'`.  (In the run: 3 times in 3·10^7 steps, first at step 393.) -/
theorem v_B_11_EaBa {x x1 x2 : Tape} (h1 : Vis .E x .A x1) (h2 : Vis .B x1 .A x2) :
    Vis .B (cons true (cons true x)) .C (cons false (cons false x2)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons true x), .B⟩ = some ⟨cons false (cons false (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons false x1, .A⟩ = some ⟨cons true (cons false (cons a L)), x1, .B⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 true (cons false (cons a L))
  have s2 : steps 2 ⟨cons false (cons a L), cons true x2, .A⟩ = some ⟨L, cons a (cons false (cons false x2)), .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `B> 11 x`, nested visits E→C A→C A→D E→C A→C A→D: out in state E, leaving `01 x'`.  (In the run: 501 times in 3·10^7 steps, first at step 495.) -/
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

/-- `B> 11 x`, nested visits E→C A→D E→C A→D: out in state E, leaving `01 x'`.  (In the run: 9908 times in 3·10^7 steps, first at step 1345.) -/
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

/-- `B> 11 x`, nested visits E→C A→D E→C A→E: out in state D, leaving `00 x'`.  (In the run: 1 times in 3·10^7 steps, first at step 3381.) -/
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

/-- `B> 11 x`, nested visits E→C A→E B→C: out in state A, leaving `10 x'`.  (In the run: 7 times in 3·10^7 steps, first at step 187.) -/
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

/-- `B> 11 x`, nested visits E→C A→F: out in state C, leaving `01 x'`.  (In the run: 3 times in 3·10^7 steps, first at step 279.) -/
theorem v_B_11_EcAf {x x1 x2 : Tape} (h1 : Vis .E x .C x1) (h2 : Vis .A x1 .F x2) :
    Vis .B (cons true (cons true x)) .C (cons false (cons true x2)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons true x), .B⟩ = some ⟨cons false (cons false (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons false (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a L))
  have s2 : steps 2 ⟨cons false (cons a L), cons false x2, .F⟩ = some ⟨L, cons a (cons false (cons true x2)), .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (s2))))⟩

/-- `E> 00 x`, no nested visit: out in state C, leaving `00 x'`.  (In the run: 26368 times in 3·10^7 steps, first at step 77.) -/
theorem v_E_00_none {x : Tape}  :
    Vis .E (cons false (cons false x)) .C (cons false (cons false x)) := by
  intro a L
  have s0 : steps 1 ⟨cons a L, cons false (cons false x), .E⟩ = some ⟨L, cons a (cons false (cons false x)), .C⟩ := rfl
  exact ⟨_, s0⟩

/-- `E> 01 x`, no nested visit: out in state C, leaving `01 x'`.  (In the run: 73649 times in 3·10^7 steps, first at step 37.) -/
theorem v_E_01_none {x : Tape}  :
    Vis .E (cons false (cons true x)) .C (cons false (cons true x)) := by
  intro a L
  have s0 : steps 1 ⟨cons a L, cons false (cons true x), .E⟩ = some ⟨L, cons a (cons false (cons true x)), .C⟩ := rfl
  exact ⟨_, s0⟩

/-- `E> 10 x`, nested visits B→A: out in state C, leaving `00 x'`.  (In the run: 8 times in 3·10^7 steps, first at step 65.) -/
theorem v_E_10_Ba {x x1 : Tape} (h1 : Vis .B x .A x1) :
    Vis .E (cons true (cons false x)) .C (cons false (cons false x1)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .E⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 2 ⟨cons false (cons a L), cons true x1, .A⟩ = some ⟨L, cons a (cons false (cons false x1)), .C⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `E> 10 x`, nested visits B→C: out in state A, leaving `10 x'`.  (In the run: 10329 times in 3·10^7 steps, first at step 115.) -/
theorem v_E_10_Bc {x x1 : Tape} (h1 : Vis .B x .C x1) :
    Vis .E (cons true (cons false x)) .A (cons true (cons false x1)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .E⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 2 ⟨cons false (cons a L), cons true x1, .C⟩ = some ⟨L, cons a (cons true (cons false x1)), .A⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (s1))⟩

/-- `E> 10 x`, nested visits B→E E→C A→D E→C A→D: out in state E, leaving `01 x'`.  (In the run: 1 times in 3·10^7 steps, first at step 132129.) -/
theorem v_E_10_BeEcAdEcAd {x x1 x2 x3 x4 x5 : Tape} (h1 : Vis .B x .E x1) (h2 : Vis .E x1 .C x2) (h3 : Vis .A x2 .D x3) (h4 : Vis .E x3 .C x4) (h5 : Vis .A x4 .D x5) :
    Vis .E (cons true (cons false x)) .E (cons false (cons true x5)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .E⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
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

/-- `E> 10 x`, nested visits B→E E→C A→E B→C: out in state A, leaving `10 x'`.  (In the run: 170 times in 3·10^7 steps, first at step 837.) -/
theorem v_E_10_BeEcAeBc {x x1 x2 x3 x4 : Tape} (h1 : Vis .B x .E x1) (h2 : Vis .E x1 .C x2) (h3 : Vis .A x2 .E x3) (h4 : Vis .B x3 .C x4) :
    Vis .E (cons true (cons false x)) .A (cons true (cons false x4)) := by
  intro a L
  have s0 : steps 4 ⟨cons a L, cons true (cons false x), .E⟩ = some ⟨cons true (cons false (cons a L)), x, .B⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 true (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons true x1, .E⟩ = some ⟨cons false (cons false (cons a L)), x1, .E⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a L))
  have s2 : steps 1 ⟨cons false (cons a L), cons false x2, .C⟩ = some ⟨cons false (cons false (cons a L)), x2, .A⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons false (cons a L))
  have s3 : steps 3 ⟨cons false (cons a L), cons false x3, .E⟩ = some ⟨cons true (cons false (cons a L)), x3, .B⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 true (cons false (cons a L))
  have s4 : steps 2 ⟨cons false (cons a L), cons true x4, .C⟩ = some ⟨L, cons a (cons true (cons false x4)), .A⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (s4))))))))⟩

/-- `E> 11 x`, nested visits E→C A→D E→C A→D: out in state E, leaving `01 x'`.  (In the run: 1 times in 3·10^7 steps, first at step 3469.) -/
theorem v_E_11_EcAdEcAd {x x1 x2 x3 x4 : Tape} (h1 : Vis .E x .C x1) (h2 : Vis .A x1 .D x2) (h3 : Vis .E x2 .C x3) (h4 : Vis .A x3 .D x4) :
    Vis .E (cons true (cons true x)) .E (cons false (cons true x4)) := by
  intro a L
  have s0 : steps 2 ⟨cons a L, cons true (cons true x), .E⟩ = some ⟨cons false (cons false (cons a L)), x, .E⟩ := rfl
  obtain ⟨t1, c1⟩ := h1 false (cons false (cons a L))
  have s1 : steps 1 ⟨cons false (cons a L), cons false x1, .C⟩ = some ⟨cons false (cons false (cons a L)), x1, .A⟩ := rfl
  obtain ⟨t2, c2⟩ := h2 false (cons false (cons a L))
  have s2 : steps 3 ⟨cons false (cons a L), cons false x2, .D⟩ = some ⟨cons false (cons true (cons a L)), x2, .E⟩ := rfl
  obtain ⟨t3, c3⟩ := h3 false (cons true (cons a L))
  have s3 : steps 1 ⟨cons true (cons a L), cons false x3, .C⟩ = some ⟨cons false (cons true (cons a L)), x3, .A⟩ := rfl
  obtain ⟨t4, c4⟩ := h4 false (cons true (cons a L))
  have s4 : steps 2 ⟨cons true (cons a L), cons false x4, .D⟩ = some ⟨L, cons a (cons false (cons true x4)), .E⟩ := rfl
  exact ⟨_, steps_seq trans s0 (steps_seq trans c1 (steps_seq trans s1 (steps_seq trans c2 (steps_seq trans s2 (steps_seq trans c3 (steps_seq trans s3 (steps_seq trans c4 (s4))))))))⟩

end H64715
