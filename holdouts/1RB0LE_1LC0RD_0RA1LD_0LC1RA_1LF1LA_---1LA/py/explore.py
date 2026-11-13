"""Partial map of 1RB0LE_1LC0RD_0RA1LD_0LC1RA_1LF1LA_---1LA: from (101)^n 0 D> 0 to the next moment with the head
in state D at the right end and a word of at most 12 cells after the (101) block.   python3 explore.py 40"""
import re, sys
from sim import next_event


def short(m):
    t = ''.join(map(str, m.tape[m.lo:m.h])).lstrip('0')
    w = re.fullmatch(r'((?:101)*)(.*)', t).group(2)
    return len(w) <= 12


for n in range(1, int(sys.argv[1]) if len(sys.argv) > 1 else 40):
    print(n, *next_event('(101)^%d 0 D> 0' % n, 'D', 'R', short))
