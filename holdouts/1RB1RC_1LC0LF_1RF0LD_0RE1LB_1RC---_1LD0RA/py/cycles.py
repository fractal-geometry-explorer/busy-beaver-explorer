"""The cycles of 1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RC---_1LD0RA, read off a run.

usage: gcc -O2 -o tmrun tools/c/tmrun.c
       ./tmrun 1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RC---_1LD0RA 1000000000 at D L 100000000 | python3 py/cycles.py

Reads the tapes printed each time the head is at the left end in state D, writes them with a = 11010, b = 110,
finds the cycle starts `0 0 b a^n b (b a a) (b a)^q b X 1^r T` and prints the counters and the corrections in
3q' = 4q + c, n' + q' = n + 2q + d, r' = 2q' + e.
"""
import re
import sys

T1 = re.compile(r'D>00b a\^(\d+) b \(baa\)\^1 \(ba\)\^(\d+) b (1b|0) 1\^(\d+) (.*)')


def words(line):
    p = line.split()
    cells, head = [], None
    for t in p[1:]:
        if '>' in t:
            head = (len(cells), t[0])
            t = t[2:]
        if not t:
            continue
        if '^' in t:
            c, n = t.split('^')
            cells += [c] * int(n)
        else:
            cells += list(t)
    s = ''.join(cells)
    s = s[:head[0]] + head[1] + '>' + s[head[0]:]
    s = s.replace('11010', 'a ').replace('110', 'b ')
    s = re.sub(r'(?:a )+', lambda m: 'a^%d ' % (len(m.group(0)) // 2), s)
    s = re.sub(r'(?:b a\^2 )+', lambda m: '(baa)^%d ' % m.group(0).count('b'), s)
    s = re.sub(r'(?:b a\^1 )+', lambda m: '(ba)^%d ' % m.group(0).count('b'), s)
    s = re.sub(r'1{5,}', lambda m: ' 1^%d ' % len(m.group(0)), s)
    return p[0], ' '.join(s.split())


starts, prev = [], False
for line in sys.stdin:
    if line.startswith('running') or line.startswith('halted'):
        continue
    step, cfg = words(line)
    m = T1.match(cfg)
    if m and not prev:
        starts.append((int(step), int(m.group(1)), int(m.group(2)), int(m.group(4)), m.group(5)))
    prev = bool(m)
for (s, n, q, r, tail), (s2, n2, q2, r2, _) in zip(starts, starts[1:]):
    print(f"step {s:>11}  n={n:5} q={q:5} r={r:5}   c={3*q2-4*q:3} d={n2+q2-n-2*q:3} e={r2-2*q2:3}   tail {tail[:50]}")
if starts:
    print(f"step {starts[-1][0]:>11}  n={starts[-1][1]:5} q={starts[-1][2]:5} r={starts[-1][3]:5}")
