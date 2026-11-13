import os, sys
sys.path.insert(0, "/home/user/w/repo-r4c/tools/py")
from bbtools.symtm import prove, rules_file
M = "1RB1RA_1LC1LB_1RE0LD_1RA0LB_---0RF_1RC0RA"
RULES = [
    ("l_round", "L E> 1 1 (1)^b 1 1 0 0 R", "L 1 E> (1)^b 1 1 0 0 1 R", "One round."),
    ("l_three", "L E> 1 1 1 0 0 R", "L 1 E> 1 0 0 1 R", "One round."),
    ("l_two", "L E> 1 1 0 0 R", "L B> 0 1 1 1 R", "two"),
    ("l_one", "L E> 1 0 0 R", "L 0 1 1 E> R", "one"),
    ("l_sw", "L 0 (1)^f 1 1 1 B> 0 R", "L B> 0 1 (1)^f 0 0 1 R", "sweep"),
    ("l_sw2", "L 0 1 1 B> 0 R", "L B> 0 0 0 1 R", "sweep"),
    ("l_sw1", "L 0 1 B> 0 R", "L B> 1 1 1 R", "sweep1"),
    ("l_sw0", "L 0 B> 0 R", "L 1 E> 1 R", "sweep0"),
]
thms = [prove(M, name, a, b, doc=doc, rotate=True, count_first=True)[0] for name, a, b, doc in RULES]
sys.stdout.write(rules_file("Machine", "H139325", thms, "Leaf rules"))
