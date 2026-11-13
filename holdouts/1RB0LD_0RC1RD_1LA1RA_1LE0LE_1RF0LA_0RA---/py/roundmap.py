"""The round map of 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA--- (the complete macro map, in algorithmic form).

Sample the run when the head is in state D at the LEFT end of the tape.  The tape is then

    DL(m, T) = 0^inf D> 1 0 0 (10)^m T 0^inf          (T a word ending in 1, the "tail")

From blank tape: DL(0, 1) at step 8, then DL(3, 1), DL(7, 1), ...  P(n) = (101)^n 01 A> of the first analysis is the
moment just before DL(2n+1, 1).  One round DL(m, T) -> DL(m', T'):

  * a right sweep turns (10)^m into (101)^(about 2m/3) (three 10 -> two 101), passes through the tail and changes it,
  * the head comes back and a D-loop (proved in Lean, `dloop`) moves the (101) block back to the left end as (10)s.

Found empirically and checked below: once m is large compared with the tail, the round depends on m only through m mod 3:
    m' = (4m + c(r, T)) / 3,   T' = tau(r, T),   r = m mod 3,
and its step count is a quadratic polynomial in k = (m - r) / 3.  So a round with a huge m is computed exactly from
five representatives m0 = 3j + r (j = j0..j0+3 and 2 j0 + 7, j0 = max(10, 4|T|/3 + 1)); the polynomial fitted on
three is checked on the other two.  The engine is py/rounds.py (shared with 1RB0LE_1LC0RD_0RA1LD_0LC1RA_1LF1LA_---1LA).
The machine halts iff some round halts (D reads 0 with a 0 on its left, then F reads 1).

usage:
    python3 roundmap.py check 2e9        direct C run (tools/c/tmrun.c), every DL event compared with the map
    python3 roundmap.py iterate 100000   iterate the round map from blank tape (big integers)
    python3 roundmap.py bfs 3000 60      explore the tail graph (all residues), report halting (r, T)
"""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rounds

M = '1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---'
RM = rounds.RoundMap(M, 'D', 1, '100', '10', 3, 4)
START = (0, '1', 8)

if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'iterate'
    if cmd == 'check':
        sys.exit(0 if rounds.check(RM, START, sys.argv[2] if len(sys.argv) > 2 else '5e9') else 1)
    elif cmd == 'iterate':
        rounds.iterate(RM, START, int(sys.argv[2]) if len(sys.argv) > 2 else 10000)
    elif cmd == 'bfs':
        rounds.bfs(RM, START[1], int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == 'show':
        for i, t, m, T in RM.orbit(*START, int(sys.argv[2])):
            print(i, t, m if isinstance(m, int) and m < 10 ** 15 else m, rounds.compress(T) if isinstance(T, str) else T)
