"""Overflow events of 1RB1LD_1LC0RE_1LA1RC_0LC0LA_0RF0RC_---0RB and how the word W changes between them.

usage:
  python3 overflows.py check EVENTS          EVENTS: the output of `tmrun MACHINE N at A L K` (A at the left end)
  python3 overflows.py slots EVENTS T M0 M1  run the event at step T again with m = M0..M1-1 and print which digits
                                             of W change

An event is a moment where the head, in state A, is on the leftmost visited cell reading `0 1 0`; the tape is then
`A>0 1 0 (1^2 0)^m 1^4 0 W` with W a word of odd blocks of 1s (the first such moment after each overflow; the
moment 3 steps earlier, `A>1 1 0 ...`, is skipped). W is printed in digits: pairs of cells, `1 0` = 0, `1 1` = 1.
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tmsim import run_to_event, Machine  # noqa: E402

MACHINE = "1RB1LD_1LC0RE_1LA1RC_0LC0LA_0RF0RC_---0RB"


def parse(line):
    toks = line.split()
    out, h = [], None
    for t in toks[1:]:
        m = re.match(r'([A-F])?(>)?([01])(\^(\d+))?$', t)
        if m.group(2):
            h = len(out)
        out += [int(m.group(3))] * (int(m.group(5)) if m.group(5) else 1)
    return int(toks[0]), out, h


def digits(cells):
    r = list(cells) + ([0] if len(cells) % 2 else [])
    return ''.join({(1, 0): '0', (1, 1): '1', (0, 0): '_', (0, 1): 'x'}[(r[i], r[i + 1])] for i in range(0, len(r), 2))


def split(cells, h):
    """(m, W cells) for `A>0 1 0 (1^2 0)^m 1^4 0 W`, or None."""
    if cells[h:h + 3] != [0, 1, 0]:
        return None
    i, m = h + 3, 0
    while cells[i:i + 3] == [1, 1, 0]:
        i, m = i + 3, m + 1
    if cells[i:i + 5] != [1, 1, 1, 1, 0]:
        return None
    return m, cells[i + 5:]


def read_events(path):
    evs = []
    for line in open(path):
        if line.startswith(('running', 'halted')):
            continue
        t, c, h = parse(line)
        s = split(c, h)
        if s:
            evs.append((t, s[0], digits(s[1]), s[1]))
    return evs


def check(path):
    evs = read_events(path)
    for k in range(len(evs) - 1):
        (t0, m0, W0, _), (t1, m1, W1, _) = evs[k], evs[k + 1]
        ratio = '%.4f' % ((t1 - t0) / (t0 - evs[k - 1][0])) if k else ''
        if m1 == m0 + 1 and len(W1) == len(W0):
            diff = [i for i in range(len(W0)) if W0[i] != W1[i]]
            span = f"digits {diff[0]}..{diff[-1]} changed ({len(diff)})" if diff else 'no change'
            print(f"{t0} m={m0} len={len(W0)} {span} gap ratio {ratio}")
        else:
            print(f"{t0} m={m0} len={len(W0)} -> m={m1} len={len(W1)} (restructure) gap ratio {ratio}")


def slots(path, T, m0, m1):
    t, m, W, Wc = [e for e in read_events(path) if e[0] == T][0]
    mach = Machine.parse(MACHINE)
    print(f"event at step {t}: m = {m}")
    print('    ' + W)
    for mm in range(m0, m1):
        cells = [0, 1, 0] + [1, 1, 0] * mm + [1, 1, 1, 1, 0] + Wc
        n, cc, hh = run_to_event(mach, cells, 0, 'A', 'A', 0, 10 ** 8)
        s = split(cc, hh)
        if not s:
            print(f"{mm:3d} (not of the event shape after {n} steps)")
            continue
        o = digits(s[1])
        print('%3d ' % mm + ''.join(a if a != b else '.' for a, b in zip(o, W))
              + ('' if len(o) == len(W) else f' (length {len(W)} -> {len(o)})') + f"  ({n} steps, m -> {s[0]})")


if __name__ == '__main__':
    if sys.argv[1] == 'check':
        check(sys.argv[2])
    elif sys.argv[1] == 'slots':
        slots(sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]))
