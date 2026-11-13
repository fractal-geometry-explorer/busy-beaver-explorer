"""The register map of 1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD (lean/Model.lean, `nxt`), with step counts.

States (real counts, as in the README):  X(a,b,c) = 0^inf 1^a 0 (10)^b 1 D> 0 1^c 0^inf,  Y(a,b,c) the same with 00,
Z(a,c) = 0^inf 1^a 0 D> 0 1^c 0^inf.  `single` is one rule (Lean: `nxt`, in shifted counts), `jump` does a whole
run of one bulk rule at once.  The step counts of each rule are those of lean/Rules.lean.

usage:
  python3 orbit.py run R          iterate R rounds (a round ends at X(0,0,N)); prints N, steps, closest approach
  python3 orbit.py validate       read `c/canon STEPS` output on stdin and check every transition and its step count
"""
import sys, math

HALT = ('HALT',)

def single(s):
    """(next state, steps); next is HALT at Z(a,2)."""
    md = s[0]
    if md == 'X':
        _, a, b, c = s
        if c >= 2:
            if a >= 4: return ('X', a - 3, b + 2, c - 1), 4 * b + 13
            if a == 3: return ('X', 1, b + 1, c - 1), 4 * b + 13
            if a == 2: return ('X', 2, b + 2, c - 1), 4 * b + 25
            if a == 1: return ('Y', 3, b, c - 1), 4 * b + 13
            if b == 0: return ('Z', 3, c - 1), 9
            return ('Y', 3, b - 1, c - 1), 4 * b + 9          # X(0,b,c) is X(1,b-1,c)
        if c == 1:
            if a >= 5: return ('X', a - 5, 0, 2 * b + 9), 8 * b + 37
            if a == 4: return ('X', 4, 0, 2 * b + 7), 8 * b + 47
            if a == 3: return ('X', 4, 0, 2 * b + 5), 8 * b + 43
            if a == 2: return ('X', 0, 0, 2 * b + 9), 8 * b + 49
            if a == 1: return ('X', 1, 0, 2 * b + 5), 8 * b + 33
            if b == 0: return ('X', 1, 0, 3), 25
            return ('X', 1, 0, 2 * b + 3), 8 * b + 25
    if md == 'Y':
        _, a, b, c = s
        if b >= 1 and c >= 2: return ('Y', a + 3, b - 1, c - 1), 4 * b + 9
        if b == 0 and c >= 2: return ('Z', a + 3, c - 1), 9
        if c == 1: return ('X', a, 1, 2 * b + 3), 8 * b + 25
    if md == 'Z':
        _, a, c = s
        if c >= 6: return ('X', a + 4, 0, c - 5), 11
        return {1: (('X', a, 1, 1), 17), 2: (HALT, 5), 3: (('X', a, 0, 5), 29), 4: (('X', a + 2, 0, 3), 21),
                5: (('X', a + 2, 0, 5), 27)}[c]
    raise ValueError(s)

def jump(s):
    """All repetitions of a bulk rule at once: (state, steps)."""
    md = s[0]
    if md == 'X':
        _, a, b, c = s
        if c >= 2 and a >= 4:
            k = min((a - 1) // 3, c - 1); return ('X', a - 3 * k, b + 2 * k, c - k), 13 * k + 4 * b * k + 4 * k * (k - 1)
        if c >= 2 and a == 2:
            k = c - 1; return ('X', 2, b + 2 * k, 1), 25 * k + 4 * b * k + 4 * k * (k - 1)
    if md == 'Y':
        _, a, b, c = s
        if b >= 1 and c >= 2:
            k = min(b, c - 1); return ('Y', a + 3 * k, b - k, c - k), 13 * k + 4 * (b - 1) * k - 2 * k * (k - 1)
    return single(s)

START, START_STEPS = ('X', 2, 0, 3), 29

def lg(x):
    return math.log10(x) if x < 10 ** 300 else len(str(x)) - 1 + math.log10(int(str(x)[:15]) / 1e14)

def run(R):
    s, steps, r, N, ny, best = START, START_STEPS, 0, None, 0, None
    every = max(1, R // 25)
    while r < R:
        if s[0] == 'Y' and s[2] >= 1 and s[3] >= 2 and s[3] - 1 >= s[2] and N:
            ny += 1                                   # a Y run that ends with b = 0, at c - b; halting needs c - b = 3
            d = abs(s[3] - s[2] - 3)
            if r >= 3:
                q = lg(max(d, 1)) - lg(N)
                if best is None or q < best[0]: best = (q, r)
        s2, n = jump(s)
        if s2 == HALT:
            print('HALT at step', steps + n, 'from', s); return
        steps += n
        if s2[0] == 'X' and s2[1] == 0 and s2[2] == 0:
            r += 1; N = s2[3]
            if r <= 12 or r % every == 0:
                print('round %d  N %s  steps %s' % (r, N if N < 10 ** 15 else '~10^%.2f' % lg(N),
                                                    steps if steps < 10 ** 15 else '~10^%.2f' % lg(steps)), flush=True)
        s = s2
    print('rounds', r, '; Y runs that end with b = 0:', ny, '; closest |c-b-3| relative to N after round 3: 10^%.2f (round %d)' % best)

def validate():
    prev = pn = None; ok = bad = 0
    for line in sys.stdin:
        p = line.split()
        if p[0] == 'HALT': print(line.strip()); bad += 1; break
        n = int(p[0])
        if p[1] == 'OTHER':
            print('unparsed tape at step', n); bad += 1; prev = None; continue
        a, b, c = map(int, p[2:])
        cur = ('Z', a, c) if p[1] == 'Z' else (p[1], a, b, c)
        if prev is not None:
            nx, k = single(prev)
            if nx == cur and n - pn == k: ok += 1
            else:
                bad += 1
                if bad < 20: print('MISMATCH at', n, prev, '->', cur, n - pn, 'predicted', nx, k)
        prev, pn = cur, n
    print('transitions checked', ok, 'mismatches', bad, 'last step', pn, 'last state', prev)

if __name__ == '__main__':
    if sys.argv[1] == 'run': run(int(float(sys.argv[2])))
    elif sys.argv[1] == 'validate': validate()
