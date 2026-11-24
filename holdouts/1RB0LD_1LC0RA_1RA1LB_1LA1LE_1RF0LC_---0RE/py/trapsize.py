"""Traps that combine the size of v = n - h_k inside its level (B cells of x = v/(5*2^k)) with residues
(v mod 2^j, k mod 2^j).  At large levels every (cell, residue) pair is taken by some n, so a trap must be closed under
every transition the cells allow.  Backward search from the halting transitions; a trap exists iff some state cannot
reach a halt."""
import sys
from fractions import Fraction as Fr
from collections import deque

def check(B, j):
    Mo = 1 << j
    third = Fr(1, 3)
    def succ(c, v, ka):
        out = []
        lo, hi = Fr(c, B), Fr(c + 1, B)
        if lo < third:                       # d = 0: x' = 3x
            a, b = 3 * lo, min(3 * hi, Fr(1))
            for c2 in range(int(a * B), min(B, -(-int(b * B * 1) // 1) + 1)):
                if Fr(c2, B) < b and Fr(c2 + 1, B) > a:
                    out.append((c2, (3 * v + 2 + ka) % Mo, ka))
        if hi > third:                       # d = 1: x' = (3x - 1)/2
            a, b = max((3 * lo - 1) / 2, Fr(0)), (3 * hi - 1) / 2
            for c2 in range(int(a * B), B):
                if Fr(c2, B) < b and Fr(c2 + 1, B) > a:
                    out.append((c2, (3 * v + 3 + ka) % Mo, (ka + 1) % Mo))
        return out
    states = [(c, v, ka) for c in range(B) for v in range(Mo) for ka in range(Mo)]
    pred = {s: [] for s in states}
    halting = set()
    for s in states:
        for t in succ(*s):
            pred[t].append(s)
            if t[0] == 0 and t[1] == 0 and Fr(s[0], B) <= third < Fr(s[0] + 1, B):
                halting.add(s)               # d = 1 from the cell holding 1/3 onto v' = 0
    seen = set(halting); dq = deque(halting)
    while dq:
        t = dq.popleft()
        for s in pred[t]:
            if s not in seen:
                seen.add(s); dq.append(s)
    return len(states), len(states) - len(seen)

for B in [3, 9, 16, 27, 64, 81]:
    for j in [1, 2, 3, 4, 5]:
        n, bad = check(B, j)
        print(f"cells {B:3d}  mod 2^{j}: {n:6d} states, {bad} cannot reach a halt", flush=True)
