"""The counter map of 1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE (the same map as `next` in lean/Map.lean).

At every moment the head, in state E, stands at the left end of the tape on a 0, the tape is

    X a b c k  =  E> 0 1^a 0 1 0 1^b (01)^c (11101)^k 1

usage: python3 map.py check [STEPS]     compare the map with the C simulator (tools/c/tmrun) at every such moment
       python3 map.py orbit [PHASES]    iterate the map from (15, 7, 7, 1), whole phases at once (a phase: the
                                        rounds from b = 7 until the first block is spent), and print every time
                                        the budget c runs out
"""
import os
import re
import subprocess
import sys

M = '1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE'
HERE = os.path.dirname(os.path.abspath(__file__))
TOOLS = os.path.join(HERE, '../../../tools/c')


def land(B, c, k):
    if c >= 1:
        return B, 7, c, k
    return (B, 10, 1, k - 1) if k >= 1 else 'stuck'


def nxt(a, b, c, k):
    """One round, exactly as `next` in lean/Map.lean: a tuple, 'halt' or 'stuck'."""
    if c == 0:
        return 'stuck'
    if a >= 4:
        return a - 2, b + 3, c, k
    if a == 3:
        return 1, b + 3, c, k
    if a == 2:
        return 0, b + 3, c, k
    if c >= 2:
        if a == 1 and b == 1:
            return 2, 4, c - 1, k
        if a == 1 and b >= 3:
            return land(b, c - 2, k)
        if a == 0 and b >= 3:
            return land(b - 1, c - 2, k)
        return 'stuck'
    if a == 1:
        if b % 2 == 1:
            return (2, 1, b // 2, k + 1) if b >= 3 else 'stuck'
        return 'halt' if b >= 2 else 'stuck'
    if b % 2 == 0:
        return (5, 4, b // 2 - 3, k + 1) if b >= 10 else 'stuck'
    return (1, 1, b // 2, k + 1) if b >= 5 else 'stuck'


def parse(tape):
    """(a, b, c, k) from the tape printed by tmrun (head at the left end), or None."""
    cells = []
    for tok in tape.split():
        m = re.fullmatch(r'(?:[A-F]>)?([01])(?:\^(\d+))?', tok)
        cells += [m.group(1)] * int(m.group(2) or 1)
    s = ''.join(cells)
    m = re.fullmatch(r'0(1*)010(1*)((?:01)*)((?:11101)*)1', s)
    if not m:
        return None
    return len(m.group(1)), len(m.group(2)), len(m.group(3)) // 2, len(m.group(4)) // 5


def check(steps):
    exe = os.path.join(HERE, 'tmrun')
    subprocess.run(['gcc', '-O2', '-o', exe, os.path.join(TOOLS, 'tmrun.c')], check=True)
    out = subprocess.run([exe, M, str(steps), 'at', 'E', 'L', '1000000000'], capture_output=True, text=True).stdout
    evs = []
    for line in out.splitlines():
        p = line.split(' ', 1)
        if p[0] in ('running', 'halted') or 'E>0' not in p[1]:
            continue
        evs.append((int(p[0]), parse(p[1])))
    first = next(i for i, (t, x) in enumerate(evs) if t == 1188)
    x = evs[first][1]
    assert x == (15, 7, 7, 1), x
    n = 0
    for t, y in evs[first + 1:]:
        x = nxt(*x)
        if x != y:
            print(f'MISMATCH at step {t}: map {x}, machine {y}')
            return 1
        n += 1
    print(f'{n} moments from step 1188 to {evs[-1][0]}: the map agrees at every one; last {x}')
    return 0


def orbit(phases):
    """Iterate the map, the rounds a -> a - 2 of a phase in one jump; report each time the budget runs out."""
    sys.set_int_max_str_digits(0)
    x, n, rounds = (15, 7, 7, 1), 0, 0
    big = lambda v: str(v) if v < 10 ** 15 else f'a {v.bit_length()}-bit number'
    while n < phases:
        a, b, c, k = x
        if a >= 4:
            r = (a - 2) // 2
            x = (a - 2 * r, b + 3 * r, c, k)
            rounds += r
            continue
        y = nxt(*x)
        rounds += 1
        if not isinstance(y, tuple):
            print(f'phase {n + 1}: {y.upper()} at a = 1, b = {big(b)}')
            return
        if a <= 1:
            n += 1
            if c == 1:
                print(f'phase {n}: the budget ran out with a = {a}, b = {big(b)} ({"odd" if b % 2 else "even"}): '
                      f'refilled to c = {big(y[2])}, k = {y[3]}')
            elif c == 2 and y[2] == 1:
                print(f'phase {n}: the budget ran out (c = 0): one more pair taken from the suffix, k = {y[3]}')
        x = y
    print(f'after {n} phases ({big(rounds)} rounds): a = {big(x[0])}, budget c = {big(x[2])}, k = {x[3]}')


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'check'
    if cmd == 'check':
        sys.exit(check(int(float(sys.argv[2])) if len(sys.argv) > 2 else 200000000))
    orbit(int(float(sys.argv[2])) if len(sys.argv) > 2 else 20)
