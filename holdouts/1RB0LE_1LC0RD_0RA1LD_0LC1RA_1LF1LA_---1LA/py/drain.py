"""The halting condition of 1RB0LE_1LC0RD_0RA1LD_0LC1RA_1LF1LA_---1LA: the first run of the list drains the main run.

    EL(m, T) = 0^inf E> 1 00 1^m T 0^inf,   T = 0 1^a 0 1^(a2) ...   (see roundmap.py)

By direct simulation (C helper evrun2.c of ../../1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---/c):

* `halt M A`: for every m < M, a < A and suffix [], [2], [7, 2]: does EL(m, [a] + suffix) halt before the next
  EL event?  Result: never for m = 1 (mod 3); for m = 0 (mod 3) from a = 4m + 14 on and for m = 2 (mod 3) from
  a = 4m on (up to 12 less with a suffix), for all a beyond except a few just above the threshold.
* `law A`: for m = 1500 + r and a < A: m' and the new list.  Result: r = 1 swallows a (m' = (4m + 3a + 8)/3, the
  list loses its first run); for r = 0, 2 either a is swallowed as well (a in three residues of twelve) or
  a' = 4a/3 + O(1) and m' = (4m - a)/3 + O(1).  So with x = a/m:  1/x' = 1/x - 1/4 while a survives.

usage: python3 drain.py halt [M A] | law [A]
"""
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
M = '1RB0LE_1LC0RD_0RA1LD_0LC1RA_1LF1LA_---1LA'


def helper(cap):
    exe = os.path.join(tempfile.mkdtemp(), 'evrun2')
    subprocess.check_call(['gcc', '-O2', '-o', exe, os.path.join(HERE, '..', '..', '1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---',
                                                                  'c', 'evrun2.c')])
    p = subprocess.Popen([exe, M, 'E', '100', str(cap)], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True,
                         bufsize=1)

    def nxt(w):
        p.stdin.write(w + '\n')
        return p.stdout.readline().split()
    return nxt


def EL(m, T):
    return '100' + '1' * m + ''.join('0' + '1' * a for a in T)


def runs(w):
    parts = w[3:].split('0')
    return len(parts[0]), [len(x) for x in parts[1:]]


def halt(Mmax, A):
    nxt = helper(10 ** 9)
    ok = True
    for suf in ([], [2], [7, 2]):
        worst = 0
        for m in range(Mmax):
            hs = [a for a in range(1, A) if nxt(EL(m, [a] + suf))[0] == 'HALT']
            if m % 3 == 1:
                ok &= not hs
                continue
            first = hs[0] if hs else None
            want = 4 * m + 14 if m % 3 == 0 else 4 * m
            if m >= 6 and want < A:
                ok &= first is not None and (first == want if not suf else want - 12 <= first <= want)
                gaps = [a for a in range(want, A) if a not in set(hs)]
                worst = max(worst, len(gaps) / (A - want))
                ok &= len(gaps) <= 0.1 * (A - want) + 4
        print(f'suffix {suf}: m = 1 (mod 3) never halts; else first halting a = 4m+14 (m = 0) or 4m (m = 2)'
              f'{" (up to 12 less)" if suf else ""}; at most {worst:.0%} of the a beyond do not halt: {"ok" if ok else "DIFFERS"}')
    return ok


def law(A):
    nxt = helper(2 * 10 ** 10)
    ok = True
    n = surv = 0
    for a in range(14, A):
        for r in (0, 1, 2):
            m = 1500 + r
            f = nxt(EL(m, [a]))
            m2, T2 = runs(f[1])
            c = 3 * m2 - 4 * m
            if r == 1:
                ok &= (c == 3 * a + 8 and T2 == [])
                continue
            n += 1
            if T2 and T2[0] > a:                                # a survives
                surv += 1
                ok &= abs(3 * T2[0] - 4 * a) <= 30 and abs(c + a) <= 30
            else:                                               # swallowed
                ok &= abs(c - 3 * a) <= 30
    print(f'a = 14..{A - 1}: r = 1 swallows a (m\' = (4m + 3a + 8)/3); r = 0, 2: a survives in {surv} of {n} cases '
          f'with a\' = 4a/3 + O(1), m\' = (4m - a)/3 + O(1), else it is swallowed (m\' = (4m + 3a)/3 + O(1)): '
          f'{"ok" if ok else "DIFFERS"}')
    return ok


if __name__ == '__main__':
    a = sys.argv[1:] or ['halt']
    if a[0] == 'halt':
        sys.exit(0 if halt(int(a[1]) if len(a) > 1 else 40, int(a[2]) if len(a) > 2 else 240) else 1)
    sys.exit(0 if law(int(a[1]) if len(a) > 1 else 120) else 1)
