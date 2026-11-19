"""regaccel.py against direct runs: every halting time it reports must be the exact halting time.

The BB(4) and BB(5) champions, then cut holdouts: a BB(6) holdout with one transition replaced by a halt, which
halts the first time the run uses that transition (random machines almost never run long). For those that halt
within a direct run of 2·10^6 steps, regaccel (block sizes 2 and 3, mirrored or not) must report the same halting
step or not finish; for those that do not, it must not report a halt at or before 2·10^6 steps.

    python3 tools/tests/test_regaccel.py [N_RANDOM]
"""
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'py', 'bbtools'))
import regaccel as G  # noqa: E402
from test_recaccel import direct  # noqa: E402

HOLD = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'holdouts')


def cut_machines(rng):
    ms = sorted(d for d in os.listdir(HOLD) if d.startswith('1RB'))
    while True:
        m = rng.choice(ms)
        rows = m.split('_')
        cells = [(q, b) for q in range(len(rows)) for b in range(2) if rows[q][3 * b] != '-']
        q, b = rng.choice(cells)
        rows[q] = rows[q][:3 * b] + '---' + rows[q][3 * b + 3:]
        yield '_'.join(rows)

sys.setrecursionlimit(100000)


FOUND = [0, 0]


def check(m, expect, ks=(1, 2, 3, 4), sec=10):
    bad = []
    for k in ks:
        s = G.Sim(m, k)
        s.run(sec)
        FOUND[1] += 1
        if s.halted:
            FOUND[0] += 1
            if expect is None or s.steps != expect:
                bad.append((m, k, 'halt at', s.steps, 'expected', expect))
        elif s.nonhalt and expect is not None:
            bad.append((m, k, 'nonhalt', s.nonhalt, 'but halts at', expect))
    return bad


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    bad = check('1RB1LB_1LA0LC_---1LD_1RD0RA', 107)
    bad += check('1RB1LC_1RC1RB_1RD0LE_1LA1LD_---0LA', 47176870, ks=(1, 3), sec=20)
    rng = random.Random(2)
    gen = cut_machines(rng)
    halting = 0
    other = 0
    while halting < n:
        m = next(gen)
        if rng.random() < 0.5:
            m = G.mirror(m)
        h = direct(m, 2 * 10 ** 6)
        if h is None:
            if other < n // 2:
                other += 1
                for k in (1, 2, 3):
                    s = G.Sim(m, k)
                    s.run(2)
                    if s.halted and s.steps <= 2 * 10 ** 6:
                        bad.append((m, k, 'halt at', s.steps, 'but the direct run does not halt there'))
            continue
        if h < 30:
            continue
        halting += 1
        bb = check(m, h, ks=(2, 3), sec=1)
        for b in bb:
            print('MISMATCH', *b, flush=True)
        bad += bb
    for b in bad:
        print('MISMATCH', *b)
    print('%d halting and %d other machines checked; %d of %d accelerated runs reached the halt; %d mismatches' % (
        halting, other, FOUND[0], FOUND[1], len(bad)))
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
