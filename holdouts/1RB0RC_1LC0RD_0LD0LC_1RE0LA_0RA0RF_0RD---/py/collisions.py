"""Mergers of two walls, by symbolic simulation: for every pair of wall shapes and a gap of g blocks between them,
run sweeps from  0^inf D> 1000 1000 1000 (1000)^x W1 (1000)^g W2 (1000)^(y+6) W3 (1000)^(z+4) R  (x, y, z any
numbers, R any tape) until the tape is in the ordinary form again, and report halts and the times E reads a 1.

usage: python3 collisions.py MACHINE GAP [W3]
"""
import os
import sys, re, itertools
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "tools", "py"))
from bbtools import symtm
from bbtools.machine import Machine, STATES
P = ['1001', '1001100', '100110', '10011', '10010', '0']
D = STATES.index('D'); E_ = STATES.index('E')
def tstr(toks):
    out = []
    for t in toks:
        if isinstance(t, symtm.Rep):
            out.append(''.join(map(str, t.word)) * 3)
        elif isinstance(t, symtm.Ctx): out.append('R')
        elif isinstance(t, symtm.Blank): out.append('Z')
        else: out.append(str(t))
    return ''.join(out)
WALL = '(?:10011|10010|1001100|100110|1001|0)'
STD = re.compile(r'^(?:1000)+(?:' + WALL + r'(?:1000)+)*' + WALL + r'?(?:1000)*R$')
def walls_of(s):
    s = s.replace('C', '#')
    return s
def sweeps(m, c, n):
    e1 = []; hist = []
    for i in range(n):
        tr = []
        try:
            c = symtm.run(m, c, lambda x: (not x.steps.is_zero()) and x.state == D and len(x.left) == 1 and isinstance(x.left[0], symtm.Blank) and x.right and x.right[0] == 1, max_moves=40000, rotate=True, trace=tr)
        except symtm.Halted:
            return 'HALT', i, e1, hist
        except symtm.TouchContext:
            return 'TOUCH', i, e1, hist
        except Exception as e:
            return type(e).__name__, i, e1, hist
        for t in tr:
            if t[0] == 'step' and t[1].state == E_ and t[1].right and t[1].right[0] == 1:
                nxt = t[1].right[1] if len(t[1].right) > 1 else None
                e1.append((i, str(nxt)))
        s = tstr(c.right); hist.append(s)
        c = symtm.Config(c.left, c.state, c.right, 0)
        if i > 0 and STD.match(s) and s.count('C') >= 2 and not any(w in s for w in ['1001C']) :
            pass
        if i > 0 and STD.match(s): return 'STD', i, e1, hist
    return 'LIMIT', n, e1, hist
if __name__ == '__main__':
    m = Machine.parse(sys.argv[1]); gap = int(sys.argv[2]); r = sys.argv[3] if len(sys.argv) > 3 else '1001100'
    for p, q in itertools.product(range(6), range(6)):
        s = f"0^inf D> 1000 1000 1000 (1000)^x {P[p]} {'1000 ' * gap}{P[q]} 1000 1000 1000 1000 1000 1000 (1000)^y {r} 1000 1000 1000 1000 (1000)^z R"
        res = sweeps(m, symtm.Config.parse(s), 120)
        print(P[p], '+', P[q], res[0], res[1], 'E1:', res[2], '->', res[3][-1] if res[3] else '')
