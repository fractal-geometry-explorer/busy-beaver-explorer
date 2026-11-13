"""Write ../lean/Fallback.lean: four more drain rules of 1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB, for the cases
where `py/drain.py` falls back to running cell by cell (a block right after a block with no gap, `0 1 (10)^c 1`
and so on).  Proved for every value of the counts and every tape around them by bbtools.symtm (Lean checks the
traces).  `lean/Chain.lean` uses them in the map F.

usage: python3 holdouts/1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB/py/chain_rules.py   (then lean/check.sh)
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools import symtm  # noqa: E402

M = "1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB"

RULES = [
    ("f_oe1z", "L 1 1 1 (01)^b 0 C> 0 0 1 0 1 (10)^c 1 0 R", "L 1 (01)^b+c+4 0 C> 0 R",
     "The odd sweep at a last pair `0 (10) 1` with a block `(10)^c 1` right after it (no gap): both are used up, "
     "D(A+3,B) -> D(A+1,B+c+4)."),
    ("f_ab_z", "L 1 1 1 (01)^b 0 C> 0 0 0 (10)^c 1 (10)^d+2 1 R", "L 1 (01)^b+c+4 0 C> 0 0 (10)^d 1 R",
     "The drain at a block `0 0 (10)^c 1` with a block `(10)^(d+2) 1` right after it (no gap): the first block is "
     "merged and the second becomes `0 (10)^d 1`, D(A+3,B) -> D(A+1,B+c+4)."),
    ("f_oe0z_odd", "0^inf 1^a 1 1 1 (0101)^k 01 0 C> 0 0 1 (10)^c+1 1 R",
     "0^inf 1 0 C> 0 0^a+2 (1010)^k 1 0 1 0 1 0 1 (10)^c 1 R",
     "The odd sweep at a block `0 1` with a block `(10)^(c+1) 1` right after it, an odd number of pairs: "
     "D(A+3,2k+1) -> S = D(1,0) with blocks `0^(A-1) (10)^(2k+3) 1` and `(10)^c 1` in front of the rest."),
    ("f_oe0z_even", "0^inf 1^a 1 1 1 (0101)^k 0 C> 0 0 1 (10)^c+1 1 R",
     "0^inf 1^a 1 1 0 C> 0 0 0 (1010)^k 1 0 1 (10)^c 1 R",
     "The same with an even number of pairs: D(A+3,2k) -> D(A+2,0) with blocks `0 0 (10)^(2k+1) 1` and `(10)^c 1` "
     "in front of the rest."),
]


def main():
    th = []
    for name, start, end, doc in RULES:
        th.append(symtm.prove(M, name, start, end, doc=doc, rotate=True, count_first=True, max_seg=40)[0])
    lean = os.path.join(HERE, "..", "lean")
    doc = ("# 1RB1RE_0RC---_1RD0RD_1LE0LF_1RA0LD_1LC1RB: the drain rules next to a block with no gap\n\n"
           "Each rule holds for every count and every tape in the contexts L, R; written by `py/chain_rules.py` with "
           "`bbtools.symtm` (a symbolic run, its trace checked by the kernel).  `0^inf` is blank tape.")
    with open(os.path.join(lean, "Fallback.lean"), "w") as f:
        f.write(symtm.rules_file("Machine", "H8002", th, doc))


if __name__ == "__main__":
    main()
