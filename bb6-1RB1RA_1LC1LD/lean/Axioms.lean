import Blank
import Macro
import Edge
import Recur
import Blocks
import Formula

/-! What each theorem rests on: `lean Axioms.lean` prints the axioms. `propext` and `Quot.sound` are the standard ones;
a `native_decide` axiom means the theorem also trusts Lean's compiler. -/

#print axioms BB6c.step_none_iff
#print axioms BB6c.halt_shape
#print axioms BB6c.blank_at_46
#print axioms BB6c.blank_runs_20000
#print axioms BB6c.blank_runs_10M

-- Macro.lean: the pass from one right-end configuration to the next (kernel only)
#print axioms BB6c.next_sound
#print axioms BB6c.K_zero_halts
#print axioms BB6c.halts_of_reaches
#print axioms BB6c.blank_passes
#print axioms BB6c.d_one_right
#print axioms BB6c.d_left_end
#print axioms BB6c.reach_inv
#print axioms BB6c.right_no_double_zero
#print axioms BB6c.halt_at_edge
#print axioms BB6c.d_zero_zero
#print axioms BB6c.halts_iff_edge

-- Blocks.lean: the covered passes keep every block at least 2 and the last block off 1 and 4 (kernel only)
#print axioms BB6c.next_good
#print axioms BB6c.next_isSome
#print axioms BB6c.next_shrink
#print axioms BB6c.nextIter_good
#print axioms BB6c.nextIter_sound

-- Recur.lean: the block machine for a last block that is a multiple of 3, and the whole pass map (kernel only)
#print axioms BB6c.astep_sound
#print axioms BB6c.arun_sound
#print axioms BB6c.pass_sound
#print axioms BB6c.passes_sound
#print axioms BB6c.blank_passes_104

-- Formula.lean: the last block after a recursive pass, 2j + c (kernel only)
#print axioms BB6c.tail_end
#print axioms BB6c.astep_app
#print axioms BB6c.pre_sound
#print axioms BB6c.recur_sound
#print axioms BB6c.recur_two
#print axioms BB6c.recur_two_three_halts
#print axioms BB6c.recur_two_good
#print axioms BB6c.recur_small
