"""The three-counter map of 1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA (the same map as `next` in lean/Map.lean).

At every moment the head, in state D, stands at the left end of the tape, the tape is  D> 0 0 1^a 0 1^b (01)^c.

usage: python3 map.py check [STEPS]     compare the map with the C simulator (tools/c/tmrun) at every such moment
       python3 map.py orbit [CYCLES]    iterate the map from (1, 1, 4), whole stretches of a >= 3 at once, and print
                                        every refill of c (the moments a budget of pairs ran out and survived)
"""
import os, re, subprocess, sys

M = '1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA'
HERE = os.path.dirname(os.path.abspath(__file__))
TOOLS = os.path.join(HERE, '../../../tools/c')


def nxt(a, b, c):
    """One round; None means the machine halts."""
    if a >= 3:
        return a - 2, b + 3, c
    if a == 1:
        return (b + 1, 4, c - 1) if c >= 1 else (b + 1, 3, 0)
    if c >= 3:
        return b + 6, 4, c - 3
    if c == 2:
        return b + 6, 3, 0
    if c == 1:
        return b + 5, 3, 0
    return (1, 1, b // 2 + 1) if b % 2 == 0 else None


def parse(tape):
    cells = []
    for tok in tape.split():
        m = re.fullmatch(r'(?:[A-F]>)?([01])(?:\^(\d+))?', tok)
        cells += [int(m.group(1))] * int(m.group(2) or 1)
    if cells[:2] != [0, 0]:
        return None
    i, a = 2, 0
    while i < len(cells) and cells[i]: a += 1; i += 1
    i += 1; b = 0
    while i < len(cells) and cells[i]: b += 1; i += 1
    c = 0
    while i + 1 < len(cells) and cells[i] == 0 and cells[i + 1] == 1: c += 1; i += 2
    if any(cells[i:]):
        return None
    return a, b, c


def check(steps):
    exe = os.path.join(HERE, 'tmrun')
    subprocess.run(['gcc', '-O2', '-o', exe, os.path.join(TOOLS, 'tmrun.c')], check=True)
    out = subprocess.run([exe, M, str(steps), 'at', 'D', 'L', '100000000'], capture_output=True, text=True).stdout
    evs = []
    for line in out.splitlines():
        p = line.split(' ', 1)
        if p[0] in ('running', 'halted'):
            continue
        evs.append((int(p[0]), parse(p[1])))
    first = next(i for i, (k, x) in enumerate(evs) if x == (1, 1, 4))
    x = evs[first][1]
    for k, y in evs[first + 1:]:
        x = nxt(*x)
        if x != y:
            print(f'MISMATCH at step {k}: map {x}, machine {y}'); return 1
    print(f'{len(evs) - first} moments from step {evs[first][0]} to {evs[-1][0]}: the map agrees at every one; '
          f'last {evs[-1][1]}')
    return 0


def orbit(cycles):
    sys.set_int_max_str_digits(0)
    a, b, c, n = 1, 1, 4, 0
    while n < cycles:
        if a >= 3:
            k = (a - 1) // 2; a -= 2 * k; b += 3 * k
        n += 1
        if a == 2 and c == 0:
            if b % 2:
                print(f'cycle {n}: HALT'); return
            print(f'cycle {n}: refill, c = {b // 2 + 1} ({(b // 2 + 1).bit_length()} bits)')
        a, b, c = nxt(a, b, c)
    print(f'after {n} cycles: a has {a.bit_length()} bits, c = {c} ({c.bit_length()} bits) pairs left')


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'check'
    if cmd == 'check':
        sys.exit(check(int(float(sys.argv[2])) if len(sys.argv) > 2 else 400000000))
    orbit(int(float(sys.argv[2])) if len(sys.argv) > 2 else 3000)
