"""1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD---: from B> 000 (100)^a (010)^b 01 [rest] to the next moment with the
head in state B at the left end before 000.   python3 explore.py A B [REST]"""
import sys
from sim import next_event

a, b = int(sys.argv[1]), int(sys.argv[2]); rest = sys.argv[3] if len(sys.argv) > 3 else ''
ok = lambda m: m.tape[m.h + 1] == 0 and m.tape[m.h + 2] == 0 and m.steps > 0
cfg = 'B> 000 (100)^%d (010)^%d 01 %s' % (a, b, rest)
print(cfg, '->', *next_event(cfg, 'B', 'L', lambda m: m.tape[m.h + 1] == 0 and m.tape[m.h + 2] == 0))
