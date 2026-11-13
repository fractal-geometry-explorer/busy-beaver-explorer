"""1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA: the b-map.  X(a,b) = (10)^a 1^b C> 0, Y(a,b) = (10)^a 1^b 0 C> 0.
From X/Y(A, b) run to the next moment with the head in state C at the right end on a 0 where the tape is again
of the form X or Y, and print b: kind b' a'-a steps.   python3 explore.py 400 70"""
import re, sys
from sim import Sim

A = int(sys.argv[1]) if len(sys.argv) > 1 else 400
B = int(sys.argv[2]) if len(sys.argv) > 2 else 70


def canon(m):
    t = ''.join(map(str, m.tape[m.lo:m.h])).lstrip('0')
    g = re.fullmatch(r'((?:10)*)(1*)(0?)', t)
    return g and ('Y' if g.group(3) else 'X', len(g.group(1)) // 2, len(g.group(2)))


for kind in 'XY':
    for b in range(B):
        sim = Sim('(10)^%d 1^%d %sC> 0' % (A, b, '0 ' if kind == 'Y' else ''))
        sim.run(lambda m: True, 1)
        sim.run(lambda m: m.st == 2 and m.h == m.hi and m.tape[m.h] == 0 and canon(m), 10**7)
        if sim.halted: print(kind, b, 'HALT', sim.steps); continue
        k, a2, b2 = canon(sim)
        print(kind, b, '->', k, b2, '%+d' % (a2 - A), sim.steps)
