"""snapshots.py STEPS [SIDE] [EVERY] [MAXP]

Runs the machine from blank tape for STEPS steps and prints the tape, run-length
coded, each EVERY-th time the head reaches a new cell on SIDE (L, R or B for both).
`(01)^5` is five copies of 01; the head is shown as `S>` before the cell it reads.
Plain Python, about 10^7 steps a minute.
"""
import os, sys

M = os.path.basename(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def parse(m):
    T = {}
    for i, g in enumerate(m.split('_')):
        for b in range(2):
            x = g[3 * b:3 * b + 3]
            T[(i, b)] = None if x[2] == '-' else (int(x[0]), 1 if x[1] == 'R' else -1, ord(x[2]) - 65)
    return T


def comp(t, maxp=12, minrep=3):
    out, i, n = [], 0, len(t)
    while i < n:
        cov, per = 1, 1
        for p in range(1, maxp + 1):
            w = t[i:i + p]
            if len(w) < p:
                break
            k = 1
            while t[i + k * p:i + (k + 1) * p] == w:
                k += 1
            if k >= minrep and k * p > cov:
                cov, per = k * p, p
        if cov > 1:
            out.append('(%s)^%d' % (t[i:i + per], cov // per)); i += cov
        else:
            out.append(t[i]); i += 1
    res, buf = [], ''
    for x in out:
        if len(x) == 1 or x.endswith('>'):
            buf += x
        else:
            if buf: res.append(buf); buf = ''
            res.append(x)
    if buf: res.append(buf)
    return ' '.join(res)


def main():
    steps = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 6
    side = sys.argv[2] if len(sys.argv) > 2 else 'B'
    every = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    maxp = int(sys.argv[4]) if len(sys.argv) > 4 else 12
    T = parse(M)
    tape = {}; h = 0; s = 0; lo = hi = 0; seen = 0
    for k in range(1, steps + 1):
        b = tape.get(h, 0)
        tr = T[(s, b)]
        if tr is None:
            print('HALT at step', k); return
        w, d, s = tr
        tape[h] = w; h += d
        new = None
        if h < lo: lo = h; new = 'L'
        elif h > hi: hi = h; new = 'R'
        if new and (side == 'B' or side == new):
            seen += 1
            if seen % every == 0:
                cells = ''.join(str(tape.get(x, 0)) for x in range(lo, hi + 1))
                j = h - lo
                # run-length code the parts either side of the head separately
                print(k, new, comp(cells[:j], maxp), 'ABCDEF'[s] + '>' + cells[j], comp(cells[j + 1:], maxp))
    print('no halt in', steps, 'steps')


if __name__ == '__main__':
    main()
