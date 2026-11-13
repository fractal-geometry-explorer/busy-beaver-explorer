"""Which abstract configurations of rlectl2.py do real runs visit (the run from blank tape and runs from random tapes
of odd blocks), and where does the abstract path to a halt leave them?
usage: python3 holdouts/1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---/py/realabs2.py K,C1,C0,J,m [STEPS_BLANK] [NRANDOM] [STEPS_RANDOM]"""
import os, sys, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rlectl
from rlectl import table, search
from rlectl2 import Dom2, fmtst

M = "1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---"


def run(T, dom, cells, steps, out):
    """cells: the tape right of (and under) the head at the start; state A.  Adds the abstract configurations to out."""
    sl = [dom.blank]
    sr = [dom.blank]
    for x in reversed(cells):
        sr.append(dom.push(x, sr[-1]))
    right = list(reversed(cells))      # right[-1] = head cell
    left = []
    s = 0
    for _ in range(steps):
        out.add((s, sl[-1], sr[-1]))
        x = right.pop() if right else 0
        if len(sr) > 1: sr.pop()
        tr = T[(s, x)]
        if tr is None:
            return 'halt'
        w, d, s = tr
        if d == 1:
            left.append(w); sl.append(dom.push(w, sl[-1]))
        else:
            y = left.pop() if left else 0
            if len(sl) > 1: sl.pop()
            right.append(w); sr.append(dom.push(w, sr[-1]))
            right.append(y); sr.append(dom.push(y, sr[-1]))
    return 'ok'


def legit(dom, nblank, nrand, srand, seed=1):
    T = table(M)
    out = set()
    run(T, dom, [], nblank, out)
    rnd = random.Random(seed)
    halts = 0
    for i in range(nrand):
        cells = []
        for _ in range(rnd.randint(3, 40)):
            cells += [1] * rnd.choice((1, 3, 3, 5, 7) if i % 2 else (1, 2, 3, 4, 5)) + [0]
        if run(T, dom, cells, srand, out) == 'halt': halts += 1
    return out, halts


if __name__ == '__main__':
    K, C1, C0, J, m = map(int, sys.argv[1].split(','))
    nb = int(float(sys.argv[2])) if len(sys.argv) > 2 else 2000000
    nr = int(sys.argv[3]) if len(sys.argv) > 3 else 100
    sr_ = int(float(sys.argv[4])) if len(sys.argv) > 4 else 200000
    dom = Dom2(K, C1, C0, J, m)
    real, halts = legit(dom, nb, nr, sr_)
    print('abstract configurations visited by real runs: %d (random tapes that halted: %d)' % (len(real), halts))
    ok, S, states, pops, halting = search(table(M), dom, dom, tmax=float(os.environ.get('TMAX', '300')))
    print('closure: %s, %d abstract configurations; real ones missing from it: %d' % (ok, len(S), len(real - S)))
    if halting:
        path = []
        c = halting[0][0]
        while c is not None: path.append(c); c = rlectl.PARENT[c]
        path = path[::-1]
        for i, c in enumerate(path):
            if c not in real:
                print('abstract path to the halt: %d steps; first one no real run made: step %d' % (len(path), i))
                for c2 in path[max(0, i - 8):i + 4]:
                    print('   %s %-66s [%s] %s' % ('  ' if c2 in real else '!!', fmtst(c2[1]), 'ABCDEF'[c2[0]], fmtst(c2[2])))
                break
