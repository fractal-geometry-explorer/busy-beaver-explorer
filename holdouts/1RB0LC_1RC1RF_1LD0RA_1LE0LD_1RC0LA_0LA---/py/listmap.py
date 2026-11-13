"""The list form of 1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA--- (and of its relabelling 1RB0LD_1LC0RD_1LA0LC_1RE0LB_1RB1RF_0LD---,
whose state B is this machine's C).  Third pass.

An event is the head at the left end of the tape in state C, reading 000.  Every event seen (from blank tape and
from thousands of synthetic starts) is a list of runs of the word 100 with short separators:

    [n1 s1, n2 s2, ..., nk 1]   =   C> 000 (100)^n1 s1 (100)^n2 s2 ... (100)^nk 1        s_i in {0, 1, 00, ...}

(P(c, b) = 000 (100)^c (010)^b 01 of the first analysis is [c 0, b 1], R(c, d) = 000 (100)^c 1 (100)^d 1 is [c 1, d 1].)

Halting: [c 0, 2c+1 1, d ...] (a quadrupling round that leaves 0 copies of the second run, with a separator 1 and
more runs after it) becomes [4c 01, d ...], and that halts before the next event (checked for c = 3..39).

`rule(L)` gives the next event for the lists it knows (one or two runs, any c >= 3; restarts with c = 1, 2; three runs
[c 0, b 0, e 1] with b odd < 2c - 1 and e even) and None otherwise.

usage: python3 listmap.py check [N]      every known rule against direct simulation, parameters < N (default 40)
       python3 listmap.py blank [EVENTS] [CAP]   the events of the run from blank tape (direct simulation, C), as
                                         lists, with the rule that predicts each one
       python3 listmap.py iterate START  the two-run map from a list such as "40960:0,109904:1" until it leaves
                                         the known rules
"""
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
M = '1RB0LC_1RC1RF_1LD0RA_1LE0LD_1RC0LA_0LA---'


def parse(w):
    """'000' then runs of 100 with separators -> [(n, sep)], or None."""
    if not w.startswith('000'):
        return None
    i, n, out = 3, len(w), []
    while i < n:
        k = 0
        while w.startswith('100', i):
            k += 1
            i += 3
        j = i
        while j < n and not w.startswith('100', j):
            j += 1
        out.append((k, w[i:j]))
        i = j
    return out


def build(L):
    return '000' + ''.join('100' * k + s for k, s in L)


def fmt(L):
    return '[' + ', '.join(f'{k} {s}' for k, s in L) + ']'


def norm(L):
    """A run of length 0 merges its two separators (as on the tape)."""
    out = []
    for k, s in L:
        if k == 0 and out:
            out[-1] = (out[-1][0], out[-1][1] + s)
        else:
            out.append((k, s))
    return out


def rule(L):
    """(name, next list) for the known cases, else None."""
    if len(L) == 1 and L[0][1] == '1' and L[0][0] >= 2:
        n = L[0][0]
        return 'single', [(2, '0'), (2 * n, '1')]
    c, s1 = L[0]
    if s1 == '0' and c in (1, 2) and len(L) >= 2:          # restart: the head run is rebuilt as 8 or 10
        b, s2 = L[1]
        need = 5 if c == 1 else 6
        if b > need:
            return 'restart', [(8 if c == 1 else 10, '0'), (b - need, s2)] + L[2:]
        return None
    if c < 3 or len(L) < 2:
        return None
    b, s2 = L[1]
    rest = L[2:]
    if s1 == '0':
        if b == 2 * c + 1 and s2 == '1' and len(L) >= 3:   # a round leaves 0 copies before a 1: the machine halts
            return 'halt', 'HALT'
        if b >= 2 * c + 1:                                  # the quadrupling round (60c^2 + 13c + 39 steps)
            return 'quad', norm([(4 * c, '0'), (b - 2 * c - 1, s2)] + rest)
        if len(L) == 2 and s2 == '1':
            if b == 2 * c:
                return 'P b=2c', [(4 * c - 1, '1')]
            if b == 2 * c - 1:
                return 'P b=2c-1', [(2, '0'), (4 * c, '1')]
            if b % 2 == 0:
                return 'P even', [(2 * c - b - 1, '1'), (2 * b + 2, '1')]
            return 'P odd', norm([(2, '0'), (2 * c - b - 3, '0'), (2 * b + 2, '1')])
        if len(L) == 3 and s2 == '0' and L[2][1] == '1' and b % 2 == 1 and b < 2 * c - 1 and L[2][0] % 2 == 0:
            e = L[2][0]
            m = 2 * b - e - 1
            if m >= 1:
                return 'P3 odd', [(2, '0'), (2 * c - b - 1, '1'), (m, '1'), (2 * e + 2, '1')]
            f = 2 * c + b - e - 3
            if f >= 1:
                return 'P3 odd, m<1', [(2, '0'), (f, '00'), (2 * e + 2, '1')]
        if s2 == '1' and len(L) >= 3 and b % 2 == 1 and b < 2 * c - 1:
            d, s3 = L[2]
            if d >= 2 * b + 2:                              # the flip stops at the third run
                return 'P odd, carry 1', norm([(2, '0'), (2 * c - b - 3, '00'), (4 * b + 2, '1'),
                                               (d - 2 * b - 2, s3)] + L[3:])
            if len(L) >= 4 and s3 == '1' and d % 2 == 0 and d <= 2 * b - 2 and L[3][0] >= 2 * d + 2:
                e, s4 = L[3]                                # ... at the fourth run
                return 'P odd, carry 2', norm([(2, '0'), (2 * c - b - 1, '1'), (2 * b - d - 1, '00'),
                                               (4 * d + 2, '1'), (e - 2 * d - 2, s4)] + L[4:])
        if s2 == '00' and len(L) >= 3 and b % 2 == 1 and b < 2 * c - 3 and L[2][1] == '1' and L[2][0] % 2 == 0:
            d = L[2][0]
            if len(L) == 3:
                return 'P00 odd', [(2, '0'), (2 * c - b - 3, '0'), (2 * b + d + 4, '1')]
            e, s4 = L[3]
            return 'P00 odd, more', norm([(2 * c - b, '1'), (2 * b + d + 1, '0'), (e - 1, s4)] + L[4:])
        return None
    if s1 == '1' and len(L) == 2 and s2 == '1':
        d = b
        if d >= 2 * c:
            return 'R d>=2c', [(2, '0'), (2 * d, '1')]
        if d % 2 == 0:
            return 'R even', [(2 * c - d - 1, '0'), (2 * d + 2, '1')]
        return 'R odd', [(2 * c - d + 1, '0'), (2 * d + 1, '1')]
    return None


def evrun(cap):
    d = tempfile.mkdtemp()
    exe = os.path.join(d, 'evrun2')
    subprocess.check_call(['gcc', '-O2', '-o', exe, os.path.join(HERE, '..', '..', '1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---',
                                                                  'c', 'evrun2.c')])
    p = subprocess.Popen([exe, M, 'C', '000', str(cap)], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True,
                         bufsize=1)

    def nxt(w):
        p.stdin.write(w + '\n')
        f = p.stdout.readline().split()
        if f[0] in ('HALT', 'CAP'):
            return f[0], int(f[1])
        return int(f[0]), f[1]
    return nxt


def check(N):
    nxt = evrun(10 ** 9)
    cases = []
    for c in range(1, N):
        for b in range(1, N):
            cases.append([(c, '0'), (b, '1')])
            cases.append([(c, '1'), (b, '1')])
            for e in (3, 10, N, 3 * N):
                cases.append([(c, '0'), (b, '0'), (e, '1')])
                cases.append([(c, '0'), (b, '00'), (e, '1')])
                for d in (e // 3, e, 2 * b + 2 + e // 5):
                    cases.append([(c, '0'), (b, '1'), (d, '1'), (e, '1')])
                    cases.append([(c, '0'), (b, '1'), (d, '1'), (e, '0'), (7, '1')])
                    cases.append([(c, '0'), (b, '1'), (d, '1'), (4 * d + 3, '1')])
                    cases.append([(c, '0'), (b, '00'), (d, '1')])
                    cases.append([(c, '0'), (b, '00'), (d, '1'), (e, '1')])
                    cases.append([(c, '0'), (b, '00'), (d, '1'), (e, '1'), (5, '1')])
            cases.append([(c, '0'), (2 * c + 1, '1'), (b, '1')])
            cases.append([(c, '0'), (2 * c + 1, '1'), (b, '1'), (5, '1')])
    for n in range(1, N):
        cases.append([(n, '1')])
    from collections import Counter
    ok, bad = Counter(), Counter()
    for L in cases:
        r = rule(L)
        if r is None:
            continue
        name, want = r
        st, w = nxt(build(L))
        if want == 'HALT' and st not in ('HALT', 'CAP'):
            st, w = nxt(w)                                  # [4c 01, d ...] halts at the next event
        got = parse(w) if st not in ('HALT', 'CAP') else ('HALT' if st == 'HALT' else None)
        if got == want:
            ok[name] += 1
        else:
            bad[name] += 1
            if bad[name] <= 3:
                print('differs', name, fmt(L), '->', fmt(got) if isinstance(got, list) else (st, w), 'predicted', want)
    for name in sorted(set(ok) | set(bad)):
        print(f'{name:14s} {ok[name]:6d} cases agree, {bad[name]} differ')
    return not bad


def blank(events, cap):
    nxt = evrun(cap)
    w, tot, prev = '0', 0, None
    for i in range(events):
        st, w2 = nxt(w)
        if st in ('HALT', 'CAP'):
            print(st, tot + w2)
            return
        tot += st
        L = parse(w2)
        tag = ''
        if prev is not None:
            r = rule(prev)
            tag = '' if r is None else (r[0] if r[1] == L else 'MISMATCH ' + r[0])
        print(i, tot, fmt(L) if L else w2, tag, flush=True)
        prev, w = L, w2


def iterate(start):
    L = [(int(a), b) for a, b in (x.split(':') for x in start.split(','))]
    i = 0
    while True:
        r = rule(L)
        if r is None:
            print('stops: no known rule for', fmt(L) if sum(k for k, _ in L) < 10 ** 6 else
                  '[' + ', '.join(f'~10^{len(str(k)) - 1} {s}' for k, s in L) + ']')
            return
        i += 1
        if r[1] == 'HALT':
            print(i, 'HALT (a quadrupling round leaves 0 copies before a separator 1)')
            return
        if r[0] == 'quad' and len(L) >= 3 and L[1][1] == '1':
            print('   quad margin b - (2c+1) =', L[1][0] - 2 * L[0][0] - 1)
        L = r[1]
        print(i, r[0], fmt(L) if sum(k for k, _ in L) < 10 ** 30 else len(L))


if __name__ == '__main__':
    a = sys.argv[1:]
    if not a or a[0] == 'check':
        sys.exit(0 if check(int(a[1]) if len(a) > 1 else 40) else 1)
    elif a[0] == 'blank':
        blank(int(a[1]) if len(a) > 1 else 40, int(float(a[2])) if len(a) > 2 else 10 ** 12)
    elif a[0] == 'iterate':
        iterate(a[1])
