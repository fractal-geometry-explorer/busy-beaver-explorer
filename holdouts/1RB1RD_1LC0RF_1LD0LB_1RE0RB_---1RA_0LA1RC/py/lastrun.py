"""lastrun.py [RMAX]: the head enters the last run of ones of the tape, 1^r followed by blank, moving right (it stands
on the first 1; the cells to its left are not looked at).  For each state and each r <= RMAX (default 300), does it
halt (H) or leave the run to the left (L)?  Result: it halts exactly for E with r = 2 (mod 6) and A with r = 1 (mod 6).
"""
import sys
M = "1RB1RD_1LC0RF_1LD0LB_1RE0RB_---1RA_0LA1RC"
RMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 300
T = {}
for i, row in enumerate(M.split('_')):
    for b in (0, 1):
        t = row[3 * b:3 * b + 3]
        T[(i, b)] = None if t[0] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
for st in range(6):
    res = []
    for r in range(1, RMAX + 1):
        tape = [1] * r; pos = 0; q = st; out = '?'
        for n in range(100 * RMAX + 1000):
            if pos < 0: out = 'L'; break
            if pos >= len(tape): tape.append(0)
            tr = T[(q, tape[pos])]
            if tr is None: out = 'H'; break
            tape[pos] = tr[0]; pos += tr[1]; q = tr[2]
        assert out != '?'
        res.append(out)
    halts = sorted({r % 6 for r, c in zip(range(1, RMAX + 1), res) if c == 'H'})
    print('ABCDEF'[st], 'halts for r mod 6 in', halts, '|', ''.join(res[:36]), '...')
