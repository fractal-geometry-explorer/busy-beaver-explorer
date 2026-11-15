"""Writes lean/VisitRules.lean: the moves of one visit of the left end, as shift rules for all counts.

usage: python3 visit_rules.py > ../lean/VisitRules.lean
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools.symtm import prove, rules_file
M="1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA"
RULES=[
 ("enter","The first five steps of a visit.","0^inf B> 0 R","0^inf 1 1 E> R"),
 ("scan_even","E crosses the rest of an even run and enters the next run, which is even.","L E> (11)^a 0 1 1 R","L (11)^a 0 1 1 E> R"),
 ("scan_odd","E reaches an odd run followed by another run: the two are joined and B returns to the 0 before them.","L E> (11)^a 0 1 (11)^b 0 1 R","L (11)^a B> 0 1 (11)^b 1 1 R"),
 ("scan_last","E reaches an odd run followed by two 0s.","L E> (11)^a 0 1 (11)^b 0 0 R","L (11)^a C> 0 (10)^b 1 0 1 R"),
 ("scan_halt","E reaches two 0s: F is on a 0.","L E> (11)^a 0 0 R","L (11)^a 0 F> 0 R"),
 ("fillzig","B fills the 0 and C, D turn the even run on the left into units.","L 0 (11)^t 1 1 B> 0 R","L C> 0 1 0 (10)^t 1 R"),
 ("stage","C fills the 0; the run on the left takes two units and B returns to the 0 before it.","L 0 (11)^c 1 1 C> 0 1 0 1 R","L B> 0 1 1 (11)^c 1 1 1 1 R"),
 ("left_end","At the left end five units become a 6 and a 4.","0^inf C> 0 1 0 1 0 1 0 1 0 1 0 R","0^inf B> 0 1 1 1 1 1 1 0 1 1 1 1 0 R"),
]
thms=[]
for name,doc,a,b in RULES:
    t,_=prove(M,name,a,b,doc=doc,max_seg=200)
    thms.append(t)
print(rules_file("Machine","H175628",thms,"The moves of one visit of the left end, each for every value of its counts and every tape in its contexts. Written by `py/visit_rules.py` with `bbtools.symtm.prove`; checked by the kernel."),end="")
