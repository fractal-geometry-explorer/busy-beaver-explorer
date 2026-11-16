"""Overflow events of 1RB1LC_1LA1RD_1LA0LA_1LD0RE_0RF1RB_---0RC, read as (z, W) with W in binary digits, and the
carry law between them.

usage:
  python3 overflows.py check EVENTS          EVENTS: the output of `tmrun MACHINE N at C L K` (C at the left end)
  python3 overflows.py slots EVENTS T Z0 Z1  run the event at step T again with z = Z0..Z1-1 and print which digits
                                             of W change (the bit slots of the right counter)

An event is a moment where the head, in state C, is on the leftmost visited cell. The cells right of the head are
read in pairs, `1 0` = digit 0, `1 1` = digit 1; the tape is then `C>0 0^z W` with W starting with a 1.
"""
import re
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tmsim import run_to_event, Machine  # noqa: E402

MACHINE = "1RB1LC_1LA1RD_1LA0LA_1LD0RE_0RF1RB_---0RC"


def parse(line):
    """`STEPS tape` (tmrun format) -> (steps, cells, head index, state letter)."""
    toks = line.split()
    out, h, q = [], None, None
    for t in toks[1:]:
        m = re.match(r'([A-F])?(>)?([01])(\^(\d+))?$', t)
        if m.group(2):
            h, q = len(out), m.group(1)
        out += [int(m.group(3))] * (int(m.group(5)) if m.group(5) else 1)
    return int(toks[0]), out, h, q


def digits(cells):
    r = list(cells) + ([0] if len(cells) % 2 else [])
    return ''.join({(1, 0): '0', (1, 1): '1', (0, 0): '_', (0, 1): 'x'}[(r[i], r[i + 1])] for i in range(0, len(r), 2))


def read_events(path):
    """[(steps, symbol read, z, W digits, W cells)] for the events in a tmrun `at C L` file."""
    evs = []
    for line in open(path):
        if line.startswith(('running', 'halted')):
            continue
        t, c, h, q = parse(line)
        d = digits(c[h + 1:])
        z = len(d) - len(d.lstrip('0'))
        evs.append((t, c[h], z, d[z:], c[h + 1 + 2 * z:]))
    return evs


def classify(e0, e1):
    """'carry' if e1 = e0 with z + 1 and W changed by one binary carry: digits p1 < ... < pk with 1 -> 0 at
    p1..p(k-1) and 0 -> 1 at pk; 'other' if z grew by one and W kept its length but changed otherwise;
    'restructure' for everything else."""
    (t0, r0, z0, W0, _), (t1, r1, z1, W1, _) = e0, e1
    if not (r0 == 0 and r1 == 0 and z1 == z0 + 1 and len(W1) == len(W0)):
        return 'restructure', None
    diff = [i for i in range(len(W0)) if W0[i] != W1[i]]
    if diff and all(W0[i] == '1' and W1[i] == '0' for i in diff[:-1]) and W0[diff[-1]] == '0' and W1[diff[-1]] == '1':
        return 'carry', diff
    return 'other', diff


def check(path):
    """For each pair of consecutive events: the kind, the digits of W that changed, and the ratio of the gaps."""
    evs = read_events(path)
    n = {'carry': 0, 'other': 0, 'restructure': 0}
    for k in range(len(evs) - 1):
        kind, diff = classify(evs[k], evs[k + 1])
        n[kind] += 1
        t0, r0, z0, W0, _ = evs[k]
        ratio = ''
        if k >= 1 and evs[k][0] > evs[k - 1][0]:
            ratio = '%.4f' % ((evs[k + 1][0] - t0) / (t0 - evs[k - 1][0]))
        span = f"changed digits {diff[0]}..{diff[-1]} ({len(diff)})" if diff else ''
        print(f"{t0} read={r0} z={z0} len={len(W0)} {kind} {span} gap ratio {ratio}")
    print(f"{len(evs)} events, {len(evs) - 1} pairs: {n}")


def slots(path, T, z0, z1):
    evs = [e for e in read_events(path) if e[0] == T]
    t, r, z, W, Wc = evs[0]
    m = Machine.parse(MACHINE)
    print(f"event at step {t}: z = {z}")
    print('    ' + W)
    for zz in range(z0, z1):
        cells = [0] + [1, 0] * zz + Wc
        n, cc, hh = run_to_event(m, cells, 0, 'C', 'C', 0, 10 ** 8)
        d = digits(cc[hh + 1:])
        z2 = len(d) - len(d.lstrip('0'))
        o = d[z2:]
        print('%3d ' % zz + ''.join(a if a != b else '.' for a, b in zip(o, W)) + f"  ({n} steps, z -> {z2})")


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'check':
        check(sys.argv[2])
    elif cmd == 'slots':
        slots(sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]))
