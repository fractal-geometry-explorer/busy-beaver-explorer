"""Write lean/StepPasses.lean: the local passes of single steps of the rebuild's walk, for every length of the run of
digits they read.  A step goes from one clean configuration (state D on a header, 00 on its left, the unread digits
of the counter above a short suffix, the down-counter V on the right) to the next; between its passes it runs
phases of ticks (Phase.lean), and lean/StepRule.lean puts the pieces together.

The passes were found by running the step on concrete counters for several lengths and fitting the visited windows
(the cells a pass reads) to one repeated block; symtm proves each for every value of the length.

Step 1: state 1001 with header 0110111, digits (top to bottom) 0 0 1^(2t+3):
  pass 0   reads the run of ones and the suffix: a tick configuration with U = 1 (2t + 2 digits), header 0110101
  phase    2^(2t+2) - 2 ticks
  pass 1   the carry into the cell above U (V must end in 11 11 01 here)
  phase    2^(2t+2) - 1 ticks
  pass 2   the full U and the digit 0 above it go into V; state 000, header 0110111

usage: python3 gen_steps.py > ../lean/StepPasses.lean
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools.symtm import prove

M = "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB"
RULES = [
    ("s1p0", "L 0 (0000100001)^t+1 00001100100 D> 0110 R", "L 1 (0000000000)^t+1 100 D> 011010111011 R",
     "Step 1, pass 0: the run 1^(2t+3) under the suffix 1001 becomes U = 1 with 2t + 2 digits, header 0110101."),
    ("s1p1", "L 0 (0000100001)^t+1 00 D> 011010111110 R", "L 1 (0000000000)^t+1 00 D> 011010101011 R",
     "Step 1, pass 1: the carry of the full U into the cell above it."),
    ("s1p2", "L 00001 (1000010000)^t+1 100 D> 0110 R", "L  D> 011011 (1010101010)^t+1 101011 R",
     "Step 1, pass 2: U and the digit above it are written into V; suffix 000, header 0110111."),
]
out = []
for name, s, e, doc in RULES:
    t, f = prove(M, name, s, e, doc=doc + f" `{s}` --> `{e}`", rotate=True, max_seg=30)
    out.append(t)
    print(f"-- {name}: proved", file=sys.stderr)
print("import Machine\n\n/-! The local passes of single steps of the walk, written by py/gen_steps.py (see StepRule.lean). -/\n\n"
      "set_option maxRecDepth 8192\n\nnamespace H49767\n\nopen TM\n")
for t in out: print(t)
print("end H49767")
