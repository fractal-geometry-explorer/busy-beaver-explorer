"""1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA---: from Y(n) = (101)^n 10 A> 0, print every moment with the head in
state A at the right end until the next Y.   python3 explore.py 23"""
import re, sys
from sim import Sim

n = int(sys.argv[1]) if len(sys.argv) > 1 else 23
sim = Sim('(101)^%d 10 A> 0' % n)
for i in range(200):
    sim.run(lambda m: m.st == 0 and m.h == m.hi and m.tape[m.h] == 0, 10**9)
    if sim.halted: print('HALT', sim.steps); break
    t = ''.join(map(str, sim.tape[sim.lo:sim.h])).lstrip('0')
    g = re.fullmatch(r'((?:101)*)(.*?)((?:110)*)', t)
    a, w, b = len(g.group(1)) // 3, g.group(2), len(g.group(3)) // 3
    print(sim.steps, '(101)^%d %s (110)^%d A> 0' % (a, w if len(w) < 30 else w[:12] + '..(%d cells)' % len(w), b))
    if w == '10' and b == 0: break
    sim.run(lambda m: True, 1)
