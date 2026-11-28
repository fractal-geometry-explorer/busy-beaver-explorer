"""The left end of 1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB, closed against any content of the first segment.

Every round trip starts with the head on a new blank cell lo in state A. Write the tape from lo as a window of L cells,
then the rest. By the cell automaton (lean/Trip.lean, lean/Token.lean) a trip writes each cell p up to the turn as
1 xor f[p] xor f[p+3], f the tape with lone-1 holes filled, so the window's new cells depend only on cells lo .. lo+L+2.
Beyond the window the tape is the first (oldest, longest) segment: all its 0s lie in one residue class mod 3.

The abstract state is (window, cell lo+L, the segment's class relative to lo). One trip: the cell lo+L is known (it
left the window on the trip before), and cells lo+L+1, lo+L+2 are free, except that only the one in the segment's
class may be 0. The machine is run on window + those three cells + a tail 111111 00 (which ends any 110 chain and
gives the turn; by locality it cannot change the window). Then a new blank cell is put in front, and the last window
cell becomes the next known cell. If that cell is a 0 outside the segment's class, the abstraction does not apply
(the window would have reached the segment's wall); the script reports it.

Result for L = 20, 24, 30: the set closes (448, 1,152, 4,608 states; L = 36 from a longer start: 18,432), never halts and never hits the wall.
So the left end never halts, whatever the first segment holds, as long as (a) the cells from lo+L on stay inside the
first segment, and (b) no 110 chain from a lone 1 at the left end runs through the whole segment to its wall. The tail
stands in for (b): a chain that leaves the window is cut there.

usage: python3 lend_closure.py [L] [TAPE_FILE]
  TAPE_FILE: lines `TAPE trip lo hi cells` (cells from the new blank cell lo), e.g. from c/trips.c with a dump added;
  each tape's left window is checked to lie in the closed set.
"""
import sys
from collections import deque

TM = "1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB".split('_')
TR = {}
for i, g in enumerate(TM):
    for r in (0, 1):
        x = g[3 * r:3 * r + 3]
        TR[(i, r)] = None if x[0] == '-' else (int(x[0]), 1 if x[1] == 'R' else -1, ord(x[2]) - 65)
TAIL = [1, 1, 1, 1, 1, 1, 0, 0]
# the left end at round trip 1,000,000 (the first 31 cells; the first segment's 0s are in class 0 relative to lo)
START_CELLS = "0010110110110110110111110111111"
START_CLASS = 0


def trip(t):
    t = t[:] + [0] * 4
    p = s = 0
    while True:
        if p >= len(t):
            t += [0] * 8
        a = TR[(s, t[p])]
        if a is None:
            return None, p
        t[p] = a[0]
        p += a[1]
        s = a[2]
        if p < 0:
            assert s == 0
            return t, None


def succ(state, L):
    w, e0, rr = state
    if e0 == 0 and L % 3 != rr:
        return 'the window reaches the wall of the first segment'
    out = []
    for b1 in (0, 1):
        for b2 in (0, 1):
            if (b1 == 0 and (L + 1) % 3 != rr) or (b2 == 0 and (L + 2) % 3 != rr):
                continue
            t, where = trip(list(w) + [e0, b1, b2] + TAIL)
            if t is None:
                return f'halt at window cell {where}: {w} {e0} {b1} {b2}'
            out.append(((0,) + tuple(t[:L - 1]), t[L - 1], (rr + 1) % 3))
    return out


def closure(s0, L):
    seen = {s0}
    q = deque([s0])
    while q:
        o = succ(q.popleft(), L)
        if isinstance(o, str):
            return None, o
        for x in o:
            if x not in seen:
                seen.add(x)
                q.append(x)
    return seen, None


def main():
    L = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    assert L <= 30
    s0 = (tuple(int(c) for c in START_CELLS[:L]), int(START_CELLS[L]), START_CLASS)
    S, bad = closure(s0, L)
    if S is None:
        print('L', L, 'not closed:', bad)
        return 1
    print(f'L = {L}: closed set of {len(S)} left-end states, no halt, the window never reaches the segment wall')
    if len(sys.argv) > 2:
        n = ok = 0
        for line in open(sys.argv[2]):
            if not line.startswith('TAPE'):
                continue
            cells = line.split()[4]
            z = [j for j, c in enumerate(cells[L:5000]) if c == '0']
            rr = (L + z[0]) % 3
            if not all((L + j) % 3 == rr for j in z):
                print('trip', line.split()[1], ': beyond the window is not one segment')
                continue
            n += 1
            ok += (tuple(int(c) for c in cells[:L]), int(cells[L]), rr) in S
        print(f'real tapes: {ok} of {n} left windows in the set')
    return 0


if __name__ == '__main__':
    sys.exit(main())
