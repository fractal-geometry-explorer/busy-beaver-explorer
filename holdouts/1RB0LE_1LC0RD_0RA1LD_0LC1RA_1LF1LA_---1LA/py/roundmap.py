"""The round map of 1RB0LE_1LC0RD_0RA1LD_0LC1RA_1LF1LA_---1LA (same family as 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---,
whose py/rounds.py is the engine).

Sample the run when the head is in state E at the LEFT end reading 1.  The tape is then

    EL(m, T) = 0^inf E> 1 00 1^m T 0^inf        T = 0 1^(a1) 0 1^(a2) ... 0 1^(ak)  (a list of runs), or empty

First at step 213: EL(11, 0 1^2).  One round: m -> (4m + c(r, T))/3, T -> tau(r, T), r = m mod 3 (m >= 30), steps
a quadratic polynomial in (m - r)/3.

usage:  python3 roundmap.py check 5e9 | iterate 100000 | bfs 3000 80 | show 40
"""
import os
import sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..',
                                '1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---', 'py'))
import rounds

M = '1RB0LE_1LC0RD_0RA1LD_0LC1RA_1LF1LA_---1LA'
RM = rounds.RoundMap(M, 'E', 1, '100', '1', 3, 4)
START = (11, '011', 213)


def runs(T):
    """The tail as its list of run lengths."""
    return [len(x) for x in T.split('0')[1:]] if T else []


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'iterate'
    if cmd == 'check':
        sys.exit(0 if rounds.check(RM, START, sys.argv[2] if len(sys.argv) > 2 else '5e9') else 1)
    elif cmd == 'iterate':
        rounds.iterate(RM, START, int(sys.argv[2]) if len(sys.argv) > 2 else 10000)
    elif cmd == 'bfs':
        rounds.bfs(RM, START[1], int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == 'show':
        for i, t, m, T in RM.orbit(*START, int(sys.argv[2])):
            print(i, t, m if isinstance(m, int) and m < 10 ** 15 else m, runs(T) if isinstance(T, str) else T)
