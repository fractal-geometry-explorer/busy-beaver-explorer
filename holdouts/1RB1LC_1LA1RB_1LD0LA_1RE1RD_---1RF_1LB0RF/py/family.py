"""The macro family of 1RB1LC_1LA1RB_1LD0LA_1RE1RD_---1RF_1LB0RF and the checks of its rules.

X(k, N, b) is the configuration   C>0 1 0 1^(5k+3) 0 W_b(N)   with blank tape on both sides, where
W_b(N) = 1 x_0 1 x_1 ... 1 x_(b-1) is N in binary, least significant bit first, each bit after a 1
(so W is a word of odd blocks of 1s separated by single 0s; a trailing x = 0 is blank tape).

usage (from this folder, after  gcc -O2 -o ../c/tmfrom ../c/tmfrom.c):
  python3 family.py rule B          X(k,N,b) -> X(k+1, N + 2^(k+1), b) for all b <= B, N >= 2^(b-1) with no overflow
  python3 family.py small B         the small restructure (N odd, N + 2^(k+1) >= 2^b), all b <= B
  python3 family.py scan B STEPS    every X(k,N,b), b <= B, run STEPS steps: does any halt?
  python3 family.py events FILE     every X event in a `tmrun ... records` file, checked against the rules
  python3 family.py forecast        the rules applied to the configuration at step 3,145,810

The simulator is c/tmfrom.c (a plain direct simulator started from a given tape).
"""
import os, subprocess, sys

M = "1RB1LC_1LA1RB_1LD0LA_1RE1RD_---1RF_1LB0RF"
HERE = os.path.dirname(os.path.abspath(__file__))
TMF = os.path.join(HERE, "..", "c", "tmfrom")


def cells(s):
    out = []
    for tok in s.split():
        if '>' in tok:
            tok = tok.split('>')[1]
        if not tok:
            continue
        if '^' in tok:
            a, b = tok.split('^')
            out += [int(a)] * int(b)
        else:
            out.append(int(tok))
    return out


def rle(c):
    out, i = [], 0
    while i < len(c):
        j = i
        while j < len(c) and c[j] == c[i]:
            j += 1
        out.append(f"{c[i]}^{j - i}" if j - i > 1 else str(c[i]))
        i = j
    return ' '.join(out)


def word(N, b):
    c = []
    for i in range(b):
        c += [1, (N >> i) & 1]
    return c


def tape(k, N, b):
    return "C>0 1 0 " + rle([1] * (5 * k + 3) + [0] + word(N, b))


def decode(c):
    """The cells from the head on, at C>0 1 0 ...: ('X', k, N, b), ('n=..', N, b) or ('bad', n)."""
    if not (len(c) > 3 and c[0] == 0 and c[1] == 1 and c[2] == 0):
        return None
    j = 3
    while j < len(c) and c[j] == 1:
        j += 1
    n, w = j - 3, c[j + 1:]
    while w and w[-1] == 0:
        w.pop()
    if len(w) % 2:
        w = w + [0]
    if not all(w[i] == 1 for i in range(0, len(w), 2)):
        return ('bad', n)
    N = sum(w[2 * i + 1] << i for i in range(len(w) // 2))
    if n >= 3 and (n - 3) % 5 == 0:
        return ('X', (n - 3) // 5, N, len(w) // 2)
    return ('n=%d' % n, N, len(w) // 2)


def chain(tp, ev=1, maxs=10**8):
    """Run from the tape; the next `ev` events C>0 1 0 ... at the left end: [(steps since last, decoded)]."""
    out = subprocess.run([TMF, M, tp, str(maxs), "C", "L", str(ev * 6 + 6)], capture_output=True,
                         text=True).stdout.splitlines()
    res, last = [], 0
    for l in out:
        if l.startswith('halted'):
            res.append(('HALT', int(l.split()[1]) - last))
            break
        if l.startswith('running'):
            break
        st, rest = l.split(None, 1)
        if rest.startswith('C>0 1 0 '):
            res.append((int(st) - last, decode(cells(rest))))
            last = int(st)
            if len(res) >= ev:
                break
    return res


def regular(k, N, b):
    return ('X', k + 1, N + (1 << (k + 1)), b)


def small(k, N, b):
    m = N + (1 << (k + 1)) - (1 << b)
    return ('X', k, (1 << (b + 2)) + 24 + (m - 1) // 2, b + 3)


def main(a):
    if a[0] == 'rule':
        B, tot, bad, T = int(a[1]), 0, 0, {}
        for b in range(1, B + 1):
            for k in range(0, b):
                for N in range(1 << (b - 1), 1 << b):
                    if N + (1 << (k + 1)) >= (1 << b):
                        continue
                    tot += 1
                    r = chain(tape(k, N, b), 1, 200 * 2**k + 10**5)
                    if not r or r[0][1] != regular(k, N, b):
                        bad += 1
                        print("BAD", b, k, N, r)
                    else:
                        T.setdefault(k, []).append(r[0][0])
        print("regular rule: %d configurations, %d failures" % (tot, bad))
        for k in sorted(T):
            print("  k=%d steps %d..%d  (84*2^k = %d)" % (k, min(T[k]), max(T[k]), 84 * 2**k))
    elif a[0] == 'small':
        B, ok, bad = int(a[1]), 0, 0
        for b in range(3, B + 1):
            for k in range(0, b):
                for N in range(1 << (b - 1), 1 << b):
                    if N % 2 == 0 or N + (1 << (k + 1)) < (1 << b):
                        continue
                    r = chain(tape(k, N, b), 1, 10**8)
                    if r and r[0][1] == small(k, N, b):
                        ok += 1
                    else:
                        bad += 1
                        print("BAD", b, k, N, r)
        print("small restructure: %d configurations agree, %d do not" % (ok, bad))
    elif a[0] == 'scan':
        B, S, tot, nh = int(a[1]), a[2], 0, 0
        for b in range(1, B + 1):
            for k in range(0, b + 1):
                for N in range(1 << (b - 1), 1 << b):
                    tot += 1
                    out = subprocess.run([TMF, M, tape(k, N, b), S, "C", "L", "0"], capture_output=True,
                                         text=True).stdout
                    if 'halted' in out:
                        nh += 1
                        print("HALT", b, k, N, out.splitlines()[-1][:200])
        print("scan: %d configurations, %d halt within %s steps" % (tot, nh, S))
    elif a[0] == 'events':
        ev = []
        for l in open(a[1]):
            p = l.split(None, 3)
            if len(p) == 4 and p[3].startswith('C>0 1 0 '):
                ev.append((int(p[0]), decode(cells(p[3]))))
        reg = sm = 0
        for (t0, x), (t1, y) in zip(ev, ev[1:]):
            if x[0] == 'X' and y == regular(*x[1:]):
                reg += 1
            elif x[0] == 'X' and x[2] % 2 and y == small(*x[1:]):
                sm += 1
                print("small restructure at step %d: X%s -> X%s" % (t0, x[1:], y[1:]))
            else:
                print("other: step %d %s -> step %d %s" % (t0, x[:2] + x[3:] if x[0] == 'X' else x[0], t1,
                                                           y[:2] + y[3:] if y[0] == 'X' else y[0]))
        print("%d events: %d regular, %d small restructures; last: step %d %s" % (len(ev), reg, sm, ev[-1][0],
                                                                                ev[-1][1][:2] + ev[-1][1][3:]))
    elif a[0] == 'forecast':
        import math
        k, N, b, t = 0, 9223585492820455065, 64, 3145810.0
        while True:
            if N + (1 << (k + 1)) < (1 << b):
                t += 84 * 2**k
                N, k = N + (1 << (k + 1)), k + 1
                continue
            if N % 2 == 0:
                print("big restructure (N even) at k=%d, b=%d, after about 10^%.1f steps" % (k, b, math.log10(t)))
                break
            t += 84 * 2**k
            N, b = small(k, N, b)[2], b + 3
            print("small restructure at k=%d -> b=%d, about 10^%.1f steps" % (k, b, math.log10(t)))


if __name__ == "__main__":
    main(sys.argv[1:])
