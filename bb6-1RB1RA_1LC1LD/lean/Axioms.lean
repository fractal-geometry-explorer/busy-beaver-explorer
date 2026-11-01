import Blank
import Macro
import Edge
import Recur
import Finish
import Blocks
import Formula
import OffsetData
import Stops
import Count
import Chain
import Tokens

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

-- Finish.lean: every step of the block machine lowers `key`; bounded, the recursive pass finishes (kernel only)
#print axioms BB6c.astep_key
#print axioms BB6c.arun_finishes
#print axioms BB6c.pass_finishes
-- Formula.lean: the last block after a recursive pass, 2j + c (kernel only)
#print axioms BB6c.tail_end
#print axioms BB6c.astep_app
#print axioms BB6c.pre_sound
#print axioms BB6c.recur_sound
#print axioms BB6c.recur_two
#print axioms BB6c.recur_two_three_halts
#print axioms BB6c.recur_two_good
#print axioms BB6c.recur_small
-- Offset.lean, OffsetData.lean: c ≥ -1 for every list of blocks ≥ 2, if pre stops (kernel only)
#print axioms BB6c.absAstep_sound
#print axioms BB6c.absNext_sound
#print axioms BB6c.pre_abs
#print axioms BB6c.check_ok
#print axioms BB6c.offset_bound
#print axioms BB6c.recur_next
-- Stops.lean: pre never gets stuck, so it stops when the cells stay bounded (kernel only)
#print axioms BB6c.prog_ok
#print axioms BB6c.preR_inv
#print axioms BB6c.pre_stops
#print axioms BB6c.recur_next_bounded
-- Chain.lean: good starts do not stay good; a halt needs a last block 3 after a block >= 6, or 6 (kernel only)
#print axioms BB6c.three_six_halts
#print axioms BB6c.two_two_three_halts
#print axioms BB6c.next_safe
#print axioms BB6c.safe_pass
#print axioms BB6c.six_after_two
#print axioms BB6c.six_pass
#print axioms BB6c.blank_safe
-- Count.lean: the pass map with step counts (kernel only), and the run to 10¹² steps (native_decide)
#print axioms BB6c.passesC_sound
#print axioms BB6c.blank_passesC
#print axioms BB6c.blank_reaches_1e12
#print axioms BB6c.blank_runs_1e12
#print axioms BB6c.blank_runs_1e10
-- Tokens.lean: pre at its A states, the carry and the three ways it stops (kernel only)
#print axioms BB6c.carry
#print axioms BB6c.row_zero
#print axioms BB6c.row_two
#print axioms BB6c.row_end
#print axioms BB6c.two_one
#print axioms BB6c.two_three
#print axioms BB6c.three_two
#print axioms BB6c.row_zero_tokens
#print axioms BB6c.row_two_tokens
#print axioms BB6c.row_end_tokens
