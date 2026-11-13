"""Write ../lean/Macro.lean: the rules of the drain machine of 1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB, proved for
every value of the counts and every tape around them by bbtools.symtm (Lean checks the traces).

The macro configurations (see the README): the drain D(A,B) = `1^A (01)^B 0 C> 0 Z`, the parity tail
P(A,B) = `1^A (01)^B 1 1 1 0 C> 0 Z` and the left-end phase T(n) = `E> (01)^n Z`, where the environment Z is a row of
blocks `0^g (10)^c 1`.

usage: python3 holdouts/1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB/py/macro_rules.py   (then lean/check.sh)
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools import symtm  # noqa: E402

M = "1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB"

RULES = [
    ("m_sweep", "L 1 1 1 (01)^b 0 C> 0 0 R", "L 1 (01)^b+2 0 C> R",
     "Drain sweep D(A+3,B) -> D(A+1,B+2): the head goes left over the pairs to the block of 1s and back; two 1s become "
     "a pair `01` and the head moves two cells right.  It reads only one cell past the head, so the rest R is any tape."),
    ("m_odd", "L 1 1 1 (01)^b 0 C> 0 0 (10)^c+2 1 R", "L 1 (01)^b+3 0 C> 0 0 (10)^c 1 R",
     "Odd sweep, the drain next to a block `0 (10)^(c+2) 1` (a gap of one 0): D(A+3,B) -> D(A+1,B+3) and the block "
     "loses two pairs.  This is the round of the ternary step."),
    ("m_odd_end1", "L 1 1 1 (01)^b 0 C> 0 0 1 0 1 0 R", "L 1 (01)^b+3 0 C> 0 0 R",
     "The odd sweep at the last pair of its block: `0 (10) 1` is used up, D(A+3,B) -> D(A+1,B+3)."),
    ("m_odd_end0", "L 1 1 1 (01)^b 0 C> 0 0 1 0 0 0 0 0 R", "L 1 (01)^b+3 1 1 1 0 C> 0 R",
     "The odd sweep at a block `0 1` with no pair: D(A+3,B) -> P(A+1,B+3), the parity tail, four 0s further right."),
    ("m_absorb", "L 1 1 1 (01)^b 0 C> 0 0 0 (10)^c 1 0 R", "L 1 (01)^b+c+3 0 C> 0 R",
     "The drain at a block `0 0 (10)^c 1` (a gap of two 0s): the block is merged, D(A+3,B) -> D(A+1,B+c+3)."),
    ("m_end2", "0^inf 1 1 (01)^b 0 C> 0 0 R", "0^inf 1 0 C> 0 0 (10)^b+1 1 R",
     "End of an even drain: D(2,B) -> S = D(1,0) with a new block `0 (10)^(B+1) 1` in front of the rest."),
    ("m_end1", "0^inf 1 (01)^b 0 C> 0 0 R", "0^inf E> (01)^b+3 R",
     "End of an odd drain: D(1,B) -> T(B+3), the head at the left end."),
    ("m_end0", "0^inf (01)^b 0 C> 0 0 R", "0^inf E> (01)^b+2 R",
     "D(0,B) -> T(B+2)."),
    ("m_tseg", "0^inf E> (01)^n+1 (10)^y+1 1 R", "0^inf (11)^n 1 0 C> 0 0 (10)^y 1 R",
     "T(n+1) next to a block `(10)^(y+1) 1`: the pairs become 1s, D(2n+1,0), and the block becomes `0 (10)^y 1`, ready "
     "for the odd sweeps (the ternary rounds)."),
    ("m_tblank", "0^inf E> (01)^n+1 0 0 0 0 0 R", "0^inf (11)^n+1 1 1 0 C> 0 0 R",
     "T(n+1) next to at least five 0s: D(2n+4,0), four 0s used."),
    ("m_peven", "0^inf 1^a+2 (0101)^k 1 1 1 0 C> 0 0 0 0 0 0 R", "0^inf 1^a 1 0 (1010)^k 1 0 1 0 1 0 1 0 C> 0 0 R",
     "Parity tail with an even number of pairs: P(A+2,2k) -> D(A+1,2k+4), four 0s used."),
    ("m_podd", "0^inf 1^a (0101)^k 01 1 1 1 0 C> 0 0 0 0 R", "0^inf 1 0 C> 0^a+2 (1010)^k 1 0 1 0 1 0 1 R",
     "Parity tail with an odd number of pairs: P(A,2k+1) -> S = D(1,0) followed by a gap `0^(A+1)` and the block "
     "`(10)^(2k+3) 1`: the block of 1s is wiped out and a new run starts from scratch inside the gap."),
    ("m_tail_halt", "L 1 1 1 (01)^b 0 C> 0 0 1 0 0 0 1 R", "L 1 0 1 0 (10)^b 1 0 1 1 1 1 B> 1 R",
     "The odd sweep at a block `0 1` followed by exactly three 0s and a 1: the parity tail has no room, and B reads "
     "a 1 (the machine halts on the next step, `tail_halts`)."),
]


def main():
    th = []
    for name, start, end, doc in RULES:
        th.append(symtm.prove(M, name, start, end, doc=doc, rotate=True, count_first=True, max_seg=40)[0])
    lean = os.path.join(HERE, "..", "lean")
    doc = ("# 1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB: the rules of the drain machine\n\n"
           "Each rule holds for every count and every tape in the contexts L, R; written by `py/macro_rules.py` with "
           "`bbtools.symtm` (a symbolic run, its trace checked by the kernel).  `0^inf` is blank tape: those rules use "
           "the left end of the tape.")
    with open(os.path.join(lean, "Macro.lean"), "w") as f:
        f.write(symtm.rules_file("Machine", "H8002", th, doc))


if __name__ == "__main__":
    main()
