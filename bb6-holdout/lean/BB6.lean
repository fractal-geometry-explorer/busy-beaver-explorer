import BB6.Basic
import BB6.Cycles
import BB6.Rules
import BB6.Iter
import BB6.Rows
import BB6.Rows2
import BB6.Marks
import BB6.Model
import BB6.Mid
import BB6.Pkt
import BB6.Pkt2
import BB6.Gap2
import BB6.Blk
import BB6.Contact
import BB6.Events
import BB6.PktRun
import BB6.Round
import BB6.SymForm
import BB6.SymRound
import BB6.SymSplit
import BB6.Meets
import BB6.Loop
import BB6.HaltClose

/-! Axiom audit: every theorem of the development should depend on at most `propext`, `Quot.sound`,
`Classical.choice` (the standard three) — in practice the rules depend on none of them. -/
#print axioms BB6.packet_to_block
#print axioms BB6.gap_marker_swap
#print axioms BB6.row_merge
#print axioms BB6.ev_swap
#print axioms BB6.ev_merge
#print axioms BB6.ev_pkt_marker
#print axioms BB6.ev_pkt_gap
#print axioms BB6.ev_pkt_wall
#print axioms BB6.ev_pkt_leftend
#print axioms BB6.ev_pkt_leftend_marker
#print axioms BB6.ev_pkt_block
#print axioms BB6.ev_gap_end
#print axioms BB6.ev_gap_wall_marker
#print axioms BB6.ev_gap_wall_wall
#print axioms BB6.ev_gap_wall_block
#print axioms BB6.ev_gap_wall_blank
#print axioms BB6.ev_gap_wall_endmarker
#print axioms BB6.ev_gap_block_marker
#print axioms BB6.ev_gap_block_wall
#print axioms BB6.ev_gap_block_block
#print axioms BB6.ev_gap_block_blank
#print axioms BB6.pktBack_run
#print axioms BB6.gapEvent_ok
#print axioms BB6.roundZ_run
#print axioms BB6.round_run
#print axioms BB6.rounds_run
#print axioms BB6.first_round_start
#print axioms BB6.blank_rounds
#print axioms BB6.Sym.posCheck_sound
#print axioms BB6.Sym.symGapEvent_sound
#print axioms BB6.Sym.symRoundZ_sound
#print axioms BB6.Sym.symRoundsZ_sound
#print axioms BB6.Sym.leaf_run
#print axioms BB6.Sym.cover_split
#print axioms BB6.Sym.Tree.sound
#print axioms BB6.Sym.symMeetsZ_sound
#print axioms BB6.Sym.Tree.soundNC
#print axioms BB6.meetsRounds_append
#print axioms BB6.Sym.Tree.soundLoop
#print axioms BB6.halt_needs_contact
#print axioms BB6.blank_halt_needs_contact
#print axioms BB6.halt_needs_close
