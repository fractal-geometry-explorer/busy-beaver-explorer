"""recaccel.py against direct runs: every halting time it reports must be the exact halting time.

Known champions (BB(4) 107, BB(5) 47,176,870) at several block sizes, then random 4- and 5-state machines that halt
within a direct run of 2·10^6 steps: recaccel (at block sizes 1..4) must report the same halting step, and must not
report a halt or a non-halt for machines that do not halt in the direct run before it.

    python3 tools/tests/test_recaccel.py [N_RANDOM]
"""
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'py', 'bbtools'))
import recaccel as R  # noqa: E402


def direct(m, limit):
    T = R.parse(m)
    tape = {}
    pos = 0
    q = 0
    for n in range(1, limit + 1):
        t = T[(q, tape.get(pos, 0))]
        if t is None:
            return n
        tape[pos] = t[0]
        pos += t[1]
        q = t[2]
    return None


def rand_machine(ns, rng):
    rows = []
    halt = (rng.randrange(ns), rng.randrange(2))
    for q in range(ns):
        row = ''
        for b in range(2):
            if (q, b) == halt or (q == 0 and b == 0 and False):
                row += '---'
            else:
                row += '%d%s%s' % (rng.randrange(2), 'LR'[rng.randrange(2)], 'ABCDEFGH'[rng.randrange(ns)])
        rows.append(row)
    if rows[0][:3] == '---':
        rows[0] = '1RB' + rows[0][3:]
    return '_'.join(rows)


def check(m, expect, ks=(1, 2, 3, 4), acts=10 ** 6, **kw):
    bad = []
    for k in ks:
        s = R.Sim(m, k, **kw)
        s.run(acts, 30)
        if s.halted:
            if expect is None or s.steps != expect:
                bad.append((m, k, 'halt at', s.steps, 'expected', expect))
        elif s.nonhalt and expect is not None:
            bad.append((m, k, 'nonhalt', s.nonhalt, 'but halts at', expect))
    return bad


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    bad = []
    bad += check('1RB1LB_1LA0LC_---1LD_1RD0RA', 107)
    bad += check('1RB1LC_1RC1RB_1RD0LE_1LA1LD_---0LA', 47176870, acts=10 ** 7)
    rng = random.Random(1)
    halting = 0
    tried = 0
    while halting < n:
        m = rand_machine(rng.choice((4, 5)), rng)
        tried += 1
        h = direct(m, 2 * 10 ** 6)
        if h is None:
            if tried % 10 == 0:
                for sp in (True, False):
                    for k in (1, 2, 3):
                        s = R.Sim(m, k, same_period=sp)
                        s.run(20000, 5)
                        if s.halted and s.steps <= 2 * 10 ** 6:
                            bad.append((m, k, 'halt at', s.steps, 'but direct run does not halt there'))
            continue
        if h < 50:
            continue
        halting += 1
        for sp in (True, False):
            bad += check(m, h, acts=10 ** 5, same_period=sp)
    for b in bad:
        print('MISMATCH', *b)
    print('%d halting machines checked, %d mismatches' % (halting, len(bad)))
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
