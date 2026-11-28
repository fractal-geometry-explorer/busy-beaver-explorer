"""One sweep of the real machine on a list (as in py/mac14.py): build the tape `A>1 (list)`, run the machine until
the head is next in state A on the leftmost visited cell reading a 1, and read the list back."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mac14 import canon, trim
M = '1RB0LE_1LC0RA_1LD0RC_1LE1LF_1LA0LC_0LA---'
T = {}
for i, g in enumerate(M.split('_')):
    for r in (0, 1):
        t = g[3 * r:3 * r + 3]
        T[(chr(65 + i), r)] = None if t[0] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, t[2])


def enc(L):
    return ''.join('10' * t if type(t) is int else ('0' if t == '.' else '1') for t in L)


def sweep(L, maxsteps=10**7):
    """Returns (steps, list) or (steps, 'HALT ...') or (None, 'no return')."""
    s = '1' + enc(L)
    tape = bytearray(len(s) + 4000); off = 2000
    for k, ch in enumerate(s): tape[off + k] = int(ch)
    p = off; st = 'A'; lo = p; hi = off + len(s) - 1
    for n in range(maxsteps):
        r = tape[p]
        if n > 0 and p == lo and st == 'A' and r == 1:
            x = bytes(tape[p + 1:hi + 1]).decode('latin1').translate({0: '0', 1: '1'})
            return n, trim(canon(x))
        t = T[(st, r)]
        if t is None:
            return n, 'HALT in state %s' % st
        tape[p] = t[0]; p += t[1]; st = t[2]; lo = min(lo, p); hi = max(hi, p)
    return None, 'no return'
