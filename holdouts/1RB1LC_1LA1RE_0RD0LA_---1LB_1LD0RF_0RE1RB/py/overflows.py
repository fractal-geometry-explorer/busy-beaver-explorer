"""Overflow events of 1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB, read as (z, W) with W in binary digits, and the
carry law between them.

usage:
  python3 overflows.py check EVENTS          EVENTS: the output of `tmrun MACHINE N at C L K` (C at the left end)
  python3 overflows.py slots EVENTS T Z0 Z1  run the event at step T again with z = Z0..Z1-1 and print which digits
                                             of W change (the bit slots of the right counter)
  python3 overflows.py predict EVENTS        extrapolate the last epoch of EVENTS to its end with the steady law

An event is a moment where the head, in state C, is on the leftmost visited cell. The cells right of the head are
read in pairs, `1 0` = digit 0, `1 1` = digit 1; the tape is then `C>0 0^z W` with W starting with a 1.
"""
import re
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tmsim import run_to_event, Machine  # noqa: E402

MACHINE = "1RB1LC_1LA1RE_0RD0LA_---1LB_1LD0RF_0RE1RB"


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


def steady_at(W, p):
    """The marker form at digit p: W = P 111110 (110)^b 111 with the marker's first 1 at p - 2 -> (P, b), or None."""
    m = re.match(r'^111110((?:110)*)111$', W[p - 2:]) if p >= 2 else None
    return (W[:p - 2], len(m.group(1)) // 3) if m else None


def steady_step(e0, e1):
    """True if e0 -> e1 is a steady overflow: e0 = P 111110 (110)^b 111 (b >= 1) with the carry at the marker,
    e1 = P 110 111110 (110)^(b-1) 111."""
    kind, diff = classify(e0, e1)
    if kind != 'carry' or len(diff) != 2 or diff[1] != diff[0] + 3:
        return False
    s0 = steady_at(e0[3], diff[0])
    return bool(s0 and s0[1] >= 1 and e1[3] == s0[0] + '110' + '111110' + '110' * (s0[1] - 1) + '111')


def check(path):
    evs = read_events(path)
    n = {'carry': 0, 'other': 0, 'restructure': 0}
    for k in range(len(evs) - 1):
        kind, diff = classify(evs[k], evs[k + 1])
        n[kind] += 1
        t0, r0, z0, W0, _ = evs[k]
        print(f"{t0} read={r0} z={z0} len={len(W0)} {kind} {diff if diff and len(diff) < 14 else ''}"
              + (" steady" if steady_step(evs[k], evs[k + 1]) else ''))
    st = [k for k in range(len(evs) - 1) if steady_step(evs[k], evs[k + 1])]
    dbl_ok = dbl_bad = 0
    for k in st:
        if k + 1 in st:
            a, b, c = evs[k][0], evs[k + 1][0], evs[k + 2][0]
            if c - b == 2 * (b - a) + 2:
                dbl_ok += 1
            else:
                dbl_bad += 1
    print(f"{len(evs)} events, {len(evs) - 1} pairs: {n}; steady overflows (marker moves one block): {len(st)}; "
          f"gap law D' = 2D + 2 between consecutive steady overflows: {dbl_ok} hold, {dbl_bad} fail")


def predict(path):
    evs = read_events(path)
    t1, _, z1, W1, _ = evs[-1]
    t0 = evs[-2][0]
    m = re.match(r'^(.*)111110((?:110)*)111$', W1)
    if not (m and classify(evs[-2], evs[-1])[0] == 'carry'):
        print("the last event is not in the marker form")
        return
    b = len(m.group(2)) // 3
    print(f"last event: step {t1}, z = {z1}, {len(W1)} digits, marker {b} blocks from the end")
    D = t1 - t0
    t = t1
    for j in range(b):
        D = 2 * D + 2
        t += D
        print(f"  overflow at step {t} (z = {z1 + j + 1}, {b - j - 1} blocks to go)")
    print(f"the marker reaches the end at step {t} ~ {t:.3e}; the restructure follows within the next gap")


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
    elif cmd == 'predict':
        predict(sys.argv[2])
    elif cmd == 'slots':
        slots(sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]))
