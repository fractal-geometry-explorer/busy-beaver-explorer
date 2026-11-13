"""Write lean/Family.lean: the local passes of the rebuild for the family of up-counters whose lowest 2k + 3 digits
are 1^(2k+1) 0 b (k = m + 1 >= 1), and the carry into a top word (a tick that reads only the cell receiving the
carry).  Between the passes the rebuild runs four phases of ticks, done in lean/FamilyRule.lean with Phase.lean.

The configurations (n = 2m + p + 5 the length of V, L the rest of the tape, U digits 00000/00001 in 5 cells):

  start  L 00000 (00001)^(2m+3) 00 D> 0110101 (11)^n 1 0^inf
  segA   --> the tick configuration U = 0 (2m+2 digits, top word 1 0000), V = 1^(n+1)
  P1, carry, P2 (ticks)
  segB   L 0000 1 0001 (00001)^(2m+2) 00 D> 0110111 (11)^(2m+3) (01)^(p+3) 1 0^inf  --> U = 0 (2m+3 digits, top 1 000)
  P3, carry, P4 (ticks)
  segC_b L 0000b 1 001 (00001)^(2m+3) 00 D> 0110111 (11)^(2m+3) 01 11 (01)^(p+1) 1 0^inf --> L 00 D> H' V' 1 0^inf

proved along the symbolic run of tools/py/bbtools/symtm.py.

usage: python3 gen_family.py > ../lean/Family.lean
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.symtm import prove

M = "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB"
RULES = [
    ("carry0_odd", "L 0 (00001)^j 00 D> 0 110101 01 R", "L 1 (00000)^j 00 D> 0 110101 11 R",
     "A tick whose carry ends in a cell 0 of any word (header 0110101, V odd): only that cell is read."),
    ("carry0_even", "L 0 (00001)^j 00 D> 0 110101 (11)^i+1 01 R", "L 1 (00000)^j 00 D> 0 110101 (01)^i+1 11 R",
     "The same, V with i + 1 trailing zeros."),
    ("carry1_odd", "L 0 (00001)^j 00 D> 0 110111 01 R", "L 1 (00000)^j 00 D> 0 110111 11 R",
     "The same for header 0110111, V odd."),
    ("carry1_even", "L 0 (00001)^j 00 D> 0 110111 (11)^i+1 01 R", "L 1 (00000)^j 00 D> 0 110111 (01)^i+1 11 R",
     "The same for header 0110111, V with i + 1 trailing zeros."),
    ("segA", "L 00000 (00001)^2*m+3 00 D> 0 110101 (11)^2*m+p+5 1 0^inf",
     "L 0000 1 (00000)^2*m+3 0 D> 0 110111 (01)^2*m+p+5 01 1 0^inf",
     "The first pass: V = 0 borrows out, the new V is all ones (one digit longer), the header becomes 0110111 and "
     "the lowest 2m + 3 digits 1 become 2m + 2 digits 0 under a top word `1 0000`."),
    ("segB", "L 0000 1 0001 (00001)^2*m+2 00 D> 0 110111 (11)^2*m+3 (01)^p+3 1 0^inf",
     "L 1 0000 0000 (00000)^2*m+2 00 D> 0 110111 (01)^2*m+2 01 11 (01)^p+2 1 0^inf",
     "The carry into the top word `1 0001`: U becomes 2m + 3 digits 0 under a top word `1 000`, V loses 1."),
    ("segC0", "L 00000 1 001 (0000100001)^m 00001 00001 00001 00 D> 0 110111 (1111)^m 11 11 11 01 11 (01)^p+1 1 0^inf",
     "L 00 D> 0 110101 0 1 0 1 (0101010101)^m 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 1 1 1 1 (1111)^m 1 1 1 1 1 1 0 1 1 1 (01)^p+1 1 0^inf",
     "The last pass, next digit 0: the counter digits and the digit above them are taken into V; header 0110101."),
    ("segC1", "L 00001 1 001 (0000100001)^m 00001 00001 00001 00 D> 0 110111 (1111)^m 11 11 11 01 11 (01)^p+1 1 0^inf",
     "L 00 D> 0 110111 1 1 1 1 (1111111111)^m 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0 1 1 1 (1111)^m 1 1 1 1 1 1 0 1 1 1 (01)^p+1 1 0^inf",
     "The last pass, next digit 1: header 0110111, V one more than for digit 0."),
]
out = []
for name, s, e, doc in RULES:
    t, f = prove(M, name, s, e, doc=doc + f" `{s}` --> `{e}`", rotate=True, max_seg=30)
    out.append(t)
    print(f"-- {name}: proved", file=sys.stderr)
print("import Machine\n\n/-! The local passes of the rebuild for the up-counters ending in 1^(2k+1) 0 b, written by "
      "py/gen_family.py (see FamilyRule.lean). -/\n\nset_option maxRecDepth 8192\n\nnamespace H49767\n\nopen TM\n")
for t in out: print(t)
print("end H49767")
