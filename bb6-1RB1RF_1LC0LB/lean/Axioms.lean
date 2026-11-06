import Blank
import Rules
import Counter
import Wall
import Top
import TopFam

/-! What each theorem rests on: `lean Axioms.lean` prints the axioms. `propext` and `Quot.sound` are the standard ones;
a `native_decide` axiom means the theorem also trusts Lean's compiler. -/

-- Blank.lean: the halting shape (kernel only)
#print axioms BB6e.step_none_iff
#print axioms BB6e.halt_shape
#print axioms BB6e.d_right_zero
#print axioms BB6e.a_entry
#print axioms BB6e.f_entry
#print axioms BB6e.halt_from_e011
#print axioms BB6e.halts_imp_e011

-- Blank.lean: bounded runs
#print axioms BB6e.blank_at_18
#print axioms BB6e.blank_runs_20000
#print axioms BB6e.blank_runs_10M

-- Rules.lean: the sweep rules (kernel only)
#print axioms BB6e.e_run
#print axioms BB6e.e_mark
#print axioms BB6e.b_run
#print axioms BB6e.first0
#print axioms BB6e.walk0
#print axioms BB6e.turn2
#print axioms BB6e.turn1
#print axioms BB6e.sweep0
#print axioms BB6e.sweepLast
#print axioms BB6e.last2
#print axioms BB6e.last1
#print axioms BB6e.wall_start
#print axioms BB6e.wall_right
#print axioms BB6e.wall_turn
#print axioms BB6e.wall_left
#print axioms BB6e.wall_end

-- Counter.lean: one right-end excursion as a base-3 decrement (kernel only)
#print axioms BB6e.counter_last2
#print axioms BB6e.counter_last1
#print axioms BB6e.counter_borrow2
#print axioms BB6e.counter_borrow1
#print axioms BB6e.counter_borrow_any

-- Wall.lean: the copy loop that builds a wall (kernel only)
#print axioms BB6e.wall_round
#print axioms BB6e.wall_loop
#print axioms BB6e.wall_jump
#print axioms BB6e.counter_borrow_ex

-- Top.lean: the top pieces (kernel only; generated, one pair of theorems per shape in top_shapes.txt)
#print axioms BB6e.top_0
#print axioms BB6e.top_1
#print axioms BB6e.top_10

-- Seq.lean: crossing a list of blocks of any length (kernel only)
#print axioms BB6e.seqL
#print axioms BB6e.seqL'
#print axioms BB6e.seqR
#print axioms BB6e.seqR'

-- TopFam.lean: the families of top shapes, by induction on the list (kernel only; generated, one per line of
-- top_families.txt)
#print axioms BB6e.fam_0
#print axioms BB6e.fam_1
#print axioms BB6e.fam_2
#print axioms BB6e.fam_3
#print axioms BB6e.fam_4
#print axioms BB6e.fam_5
#print axioms BB6e.fam_6
