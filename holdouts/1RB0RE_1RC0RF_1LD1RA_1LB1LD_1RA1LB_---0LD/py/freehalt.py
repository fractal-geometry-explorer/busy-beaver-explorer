"""Halting tails when the gap's residues are free (trust level: computation).

The run is a sequence of phases `0^inf S> 0 1 0^X T` (gap X, tail T); a phase end rewrites the front of T
according to r = X mod 4 (r = 0 or 2) and the next gap is about 3X/2.  This script lets r be chosen freely at
every phase and searches for a sequence of choices that halts.  It serves both machines of the family:

    1RB0RE_1RC0RF_1LD1RA_1LB1LD_1RA1LB_---0LD   (phase state B, first tail 1^8)
    1RB1RF_1LC1RD_1LA1LC_1RA0RE_1RD1LA_---0LE   (phase state A, first tail 1^4)

usage: python3 freehalt.py check            replay the recorded halting words of both machines, then run the last
                                            phases of each directly with real gaps (a few seconds)
       python3 freehalt.py hunt M S TAIL N  best-first search from TAIL, N expansions; prefers tails with a short
                                            odd run of ones near the front
       python3 freehalt.py bfs M S TAIL D   every choice of residues to depth D (exhaustive)
       python3 freehalt.py show M S TAIL WORD   the tails along a word of residues

Phases are simulated cell by cell by ../c/phaseend.c with gap 100 + r; the Lean lemma `phase` covers the rounds
for every gap >= 24, and the phase end was measured to depend on the gap only through r.
"""
import heapq
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
M1 = '1RB0RE_1RC0RF_1LD1RA_1LB1LD_1RA1LB_---0LD'
M2 = '1RB1RF_1LC1RD_1LA1LC_1RA0RE_1RD1LA_---0LE'
# words of residues found by `hunt`: after the word, residue 2 halts
W1 = ('000' + '2' + '0' + '2' * 4 + '0' + '2' * 5 + '0' + '2' * 11 + '0' + '2' * 23 + '0' + '2' * 47 + '0' * 70 + '2')
W2 = '0' + W1
KNOWN = ((M1, 'B', '1' * 8, W1), (M2, 'A', '1' * 4, W2))
_EXE = None


class Phase:
    def __init__(self, machine, state):
        global _EXE
        if _EXE is None:
            _EXE = os.path.join(tempfile.mkdtemp(), 'phaseend')
            subprocess.check_call(['gcc', '-O2', '-o', _EXE, os.path.join(HERE, '..', 'c', 'phaseend.c')])
        self.p = subprocess.Popen([_EXE, machine, state], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True,
                                  bufsize=1)

    def __call__(self, X, T):
        """-> ('HALT',) | ('LONG',) | ('ok', X', T')"""
        self.p.stdin.write('%d %s\n' % (X, T or '-')); self.p.stdin.flush()
        w = self.p.stdout.readline().split()
        if w[0] in ('HALT', 'LONG'):
            return (w[0],)
        return ('ok', int(w[1]), w[3] if len(w) > 3 else '')


def runs(T):
    return [len(x) for x in re.findall('1+|0+', T)]


def fmt(T, n=16):
    return ' '.join(str(x) if i % 2 == 0 else '.%d' % x for i, x in enumerate(runs(T)[:n]))


def replay(ph, T, word):
    tails = [T]
    for ch in word:
        o = ph(100 + int(ch), T)
        if o[0] != 'ok':
            return tails, o[0]
        T = o[2]; tails.append(T)
    return tails, None


def direct(ph, tails, word, m, last=2, xmax=200000):
    """The last m phases of the word and the halting phase, run with real gaps: the smallest even start gap whose
    residues follow the word.  -> (gap, tail) or None"""
    T0 = tails[len(word) - m]; want = [int(c) for c in word[len(word) - m:]] + [last]
    for X0 in range(24, xmax, 2):
        X, T = X0, T0
        for i, r in enumerate(want):
            if X % 4 != r:
                break
            o = ph(X, T)
            if o[0] == 'HALT':
                if i == len(want) - 1:
                    return X0, T0
                break
            if o[0] != 'ok':
                break
            X, T = o[1], o[2]
    return None


def check():
    ok = True
    for M, S, T0, W in KNOWN:
        ph = Phase(M, S)
        tails, ev = replay(ph, T0, W)
        halts = ev is None and ph(102, tails[-1])[0] == 'HALT' and ph(100, tails[-1])[0] == 'ok'
        first1 = next((i for i, T in enumerate(tails) if 1 in runs(T)[0::2]), None)
        print(M)
        print('  %d free phases from tail %s reach tail %s; residue 2 then halts: %s' % (len(W), fmt(T0), fmt(tails[-1]), halts))
        print('  first tail with a lone 1: after phase %s' % first1)
        d = direct(ph, tails, W, 5) if halts else None
        if d:
            print('  direct run: 0^inf %s> 0 1 0^%d T with T = %s halts in the 6th phase' % (S, d[0], fmt(d[1])))
        ok = ok and halts and d is not None
    return ok


BAD = {1: 0, 3: 1, 5: 2, 7: 3, 9: 4, 13: 5}


def score(T, d):
    rr = runs(T); best = (9, 99)
    for i in range(0, min(len(rr), 16), 2):
        b = BAD.get(rr[i], 9)
        if (b, i) < best:
            best = (b, i)
    return best + (d,)


def hunt(M, S, T0, N):
    ph = Phase(M, S)
    seen = {T0: None}; h = [(score(T0, 0), 0, T0)]; n = 0; best = None

    def word(T):
        out = []
        while seen[T] is not None:
            T, r = seen[T]; out.append(str(r))
        return ''.join(out[::-1])
    while h and n < N:
        _, d, T = heapq.heappop(h); n += 1
        for r in (0, 2):
            o = ph(100 + r, T)
            if o[0] == 'HALT':
                if best is None or d + 1 < best[0]:
                    best = (d + 1, word(T), r, T)
                continue
            if o[0] != 'ok' or o[2] in seen or len(o[2]) > 3000:
                continue
            seen[o[2]] = (T, r); heapq.heappush(h, (score(o[2], d + 1), d + 1, o[2]))
    print('expanded %d tails, %d seen' % (n, len(seen)))
    if best:
        print('halts after %d phases: word %s then residue %d, on tail %s' % (best[0], best[1], best[2], fmt(best[3])))
    else:
        print('no halt found')


def bfs(M, S, T0, D):
    ph = Phase(M, S)
    seen = {T0}; layer = [T0]; halts = lone = 0
    for d in range(D):
        nxt = []
        for T in layer:
            for r in (0, 2):
                o = ph(100 + r, T)
                if o[0] == 'HALT':
                    halts += 1
                elif o[0] == 'ok' and o[2] not in seen:
                    seen.add(o[2]); nxt.append(o[2]); lone += 1 in runs(o[2])[0::2]
        layer = nxt
        print('depth %d: %d new tails, %d in all, %d halts, %d tails with a lone 1' % (d + 1, len(nxt), len(seen), halts, lone), flush=True)


if __name__ == '__main__':
    a = sys.argv[1:]
    if a[:1] == ['check']:
        sys.exit(0 if check() else 1)
    elif a[:1] == ['hunt']:
        hunt(a[1], a[2], a[3], int(float(a[4])))
    elif a[:1] == ['bfs']:
        bfs(a[1], a[2], a[3], int(a[4]))
    elif a[:1] == ['show']:
        ph = Phase(a[1], a[2])
        tails, ev = replay(ph, a[3], a[4])
        for i, T in enumerate(tails[1:]):
            print(i + 1, a[4][i], fmt(T))
        if ev: print(ev)
    else:
        print(__doc__); sys.exit(1)
