"""End of an epoch of 1RB0LF_1LC0LA_1RA0RD_---1RE_1LA1RC_0LB0RC: every phase of every regime with the first count at
its last value (a = 4) and a large second count b (with the residue mod 3 that phase has in the run), run until a
regime phase is reached again with first count >= b/2.

usage: python3 endcases.py [BB]        (default BB 3000; prints one line per regime phase, 62 in all)
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from regimes import REG, phases, phase_index, reach  # noqa: E402


def main():
    BB = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    idx = phase_index()
    n = ok = 0
    for r in REG:
        for i, l in enumerate(phases(r)[:-1]):
            b = BB - BB % 3 + l[3] % 3
            res = reach(['00', 4, l[2], b] + l[4:], idx, BB // 2)
            n += 1
            ok += res[0] == 'OK'
            print(r, i, 'a=4 b=%d ->' % b, res, flush=True)
    print('%d of %d end cases reach a regime again' % (ok, n))


if __name__ == '__main__':
    main()
