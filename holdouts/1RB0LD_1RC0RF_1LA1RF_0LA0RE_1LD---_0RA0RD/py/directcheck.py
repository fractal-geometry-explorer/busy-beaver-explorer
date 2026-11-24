"""Check one state of py/oacc.py against a direct run of the machine (24 November 2026).

Builds the tape of a state line `sweeps steps digits...` (from oacc.py's OEVENTS log or its state file) and compares
it, cell for cell, with the direct run of c/at.c to exactly that step: the head must be in the sample state, on a 0
with only 0s to its right, and the cells to its left must be the digits.

    gcc -O2 -o /tmp/at c/at.c
    python3 py/directcheck.py /tmp/at c2|c1 "LINE"
"""
import re
import subprocess
import sys

MACH = {'c2': '1LB0RD_1LC0LF_1RA1LF_0RA0LE_1RD---_0LA0LD',      # c2 mirrored: the counter at the right end
        'c1': '1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB'}
STATE = {'c2': 'D', 'c1': 'B'}
SH = {'Z': '101010', 'O': '10', 'T': '100000'}


def wall(n):
    if n in SH:
        return SH[n]
    a, b = map(int, n[1:].split('_'))
    return '1' * a + '0' * b


def main():
    at, which, line = sys.argv[1], sys.argv[2], sys.argv[3]
    w = line.split()
    T = int(w[1])
    s = ''
    for t in w[2:-2]:
        m = re.match(r'^\[(\d+)\](\w+)$', t)
        s += '1000' * int(m.group(1)) + wall(m.group(2))
    s += '1000' * int(w[-2][1:-1]) + '100'
    out = subprocess.run([at, MACH[which], str(T)], capture_output=True, text=True).stdout.split()
    st, left = out[0], out[1]
    right = out[3] if len(out) > 3 else ''
    ok = st == STATE[which] and right.strip('0') == '' and left.lstrip('0') == s.lstrip('0')
    print('%s at step %d: %d cells %s' % (which, T, len(s.lstrip('0')), 'EQUAL' if ok else 'DIFFERENT'))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
