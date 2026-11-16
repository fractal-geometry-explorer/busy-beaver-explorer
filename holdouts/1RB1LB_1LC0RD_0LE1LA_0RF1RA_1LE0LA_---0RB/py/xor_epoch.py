"""One sweep pair of 1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB on clean words is the XOR rule.

Write x = 111 and y = 110.  For every word string w = w[0] .. w[n-1] over {x, y} with w[n-1] = y and n <= N:

  1. the machine started in state B on the first cell of enc(w), with 0 0 after it, moves right without ever
     turning back past the start and first steps onto the cell after enc(w) in state B;
     (each run 1^m 0 becomes 0^(m-1) 1 1);
  2. started in state C on the last cell of what step 1 wrote, it moves left one cell per step, never turning;
  3. when it leaves the left end the cells read enc(v) with v[i] = w[i] xor w[i+1] for i < n-1 (x = 0, y = 1),
     and v[n-1] = x.

This is exhaustive for each n <= N (all 2^(n-1) strings), using the machine's own transition table; it is a
computation, not a proof for all n.

usage: python3 xor_epoch.py [N]     (default 16: 65,535 strings, a few seconds)
"""
import itertools
import sys

TM = "1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB"
TR = {}
for i, g in enumerate(TM.split('_')):
    for r in range(2):
        s = g[3 * r:3 * r + 3]
        if s[0] != '-':
            TR[(i, r)] = (int(s[0]), 1 if s[1] == 'R' else -1, ord(s[2]) - 65)
ENC = {'x': [1, 1, 1], 'y': [1, 1, 0]}
B, C = 1, 2


def check(w):
    n = len(w)
    u = sum((ENC[c] for c in w), [])
    t = u + [0, 0]
    p, st = 0, B
    while p < len(u):
        a, d, s2 = TR[(st, t[p])]
        t[p] = a
        p += d
        st = s2
        if p < 0:
            return False
    if (p, st) != (len(u), B):
        return False
    p, st = len(u) - 1, C
    while p >= 0:
        a, d, s2 = TR[(st, t[p])]
        t[p] = a
        if d != -1:
            return False
        p -= 1
        st = s2
    v = [t[3 * i:3 * i + 3] for i in range(n)]
    want = [ENC['y'] if (w[i] == 'y') != (w[i + 1] == 'y') else ENC['x'] for i in range(n - 1)] + [ENC['x']]
    return v == want


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    total = 0
    for n in range(1, N + 1):
        for ws in itertools.product('xy', repeat=n - 1):
            w = ''.join(ws) + 'y'
            total += 1
            if not check(w):
                print("FAILS for", w)
                sys.exit(1)
    print("ok: %d word strings, lengths 1..%d" % (total, N))


if __name__ == '__main__':
    main()
