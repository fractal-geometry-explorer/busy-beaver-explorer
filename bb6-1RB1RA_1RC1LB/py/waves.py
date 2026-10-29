"""The run of 1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB as a map on block lists, and the left-going wave inside it.

usage:
  python3 waves.py left K        every arrival of the wave at the left end in the first K macro steps
  python3 waves.py super K       the super steps (four macro steps each) with the wave's depth and N

**Macro step.**  At each event the head is in state A on the blank just right of the last block, and the tape is
blocks of ones separated by single 0s:  0^inf 1^b1 0 1^b2 0 ... 0 1^bn A>0 0^inf.  The list (b1, ..., bn) is the
macro state; the last block may be 0 (the tape then ends in 1^b 0 A>0).  `step` maps one event to the next and counts
the machine steps between them.  It is made of these local rules (y is the block left of the head, R the blocks on
the right, which during the wave are separated by 00):

  trigger     ... 1^x A>0                     -> B on the 0 left of 1^(x-1), then 000 1       6 + (x-1) steps
  cycle       1^y 0 [B] 1^m 000 1^k            -> 1^(y+1) 0 [B] 1^(m-2) 000 1^(k+1)           2m + 5 steps
  even end    1^y 0 [B] 000 1^k, y >= 2        -> [B] on the 0 left of 1^(y-2), then 000 1 00 1^k   y + 3 steps
  odd end     1^y 0 [B] 1 000 1^k              -> 1^(y+2) 0, A at the start of 1^(k+2)        17 steps
  y = 1 end   1 0 [B] 000 1^k                  -> 1 0 1^4 0, A at the start of 1^(k-1)        19 steps
  pass        A crossing 1^u 00 1^v            -> 1^(u+2) 0 1^(v-1), A on                     u + 3 steps
  trailing 0  1^v 0 A>0                        -> 1^(v+1) 0 1^2 A>0                           17 steps
  halt        [B] 000 at the left end (y = 0) -> B0 C0 D1 E0 C0 D0: the halting transition

So one macro step sends a *wave* left from the right end: the block it stands at, of length c, is halved by c // 2
cycles; if c is even the wave moves on to the next block left with c' = y + c/2 - 2 (y that block's length), if c is
odd it turns and A sweeps back to the right end.  At the left end y is 0: the wave keeps halving there, c -> c/2 - 2,
and halts if it reaches c = 0, that is if it arrives with c + 4 a power of two.

**Super step.**  From the fourth event on (step 136, tape [1, 6, 5, 0]), every fourth event has the tape
[p1, ..., pm, 5, 0], and the next such event follows from P = (p1, ..., pm) alone (`superstep`): put d_{m+1} = 20
and d_l = p_l + d_{l+1}/2 going left.
The wave turns at the largest i with d_i odd, and then

  P' = (p1, ..., p_{i-2},  p_{i-1} + (d_i - 1)/2,  (d_i + 5)/2,  d_{i+1}/2, ..., d_m/2)          (i >= 2).

If d_2, ..., d_m are all even the wave reaches the left end; write d_1 = 2^s u with u odd: u = 1 is the halt,
u = 3 a visit to the left end in state F with P' = (1, 4, 3, 6, ..., 3 2^(s-1), d_2/2, ..., d_m/2), and u >= 5 gives
P' = ((u-1)/2, (u+5)/2, u, 2u, ..., 2^(s-1) u, d_2/2, ..., d_m/2).  In one number: with N = 10 + sum p_l 2^(m-l),
the wave goes down to depth v2(N) + 1, reaches the left end when 2^(m-1) divides N, and the machine halts exactly
when some N is a power of two.

Trust: the rules above were found by hand and are checked here against direct simulation (tests/test_waves.py: every
event of the first 10^9 steps, with exact step counts, and the predicted left-end records against
runs/left_records_1e10.txt and a direct run to 2.7 10^10 steps, and against the first 2,000 configurations of
py/macro.py, the cut of the same run that lean/Macro.lean proves).  The super step and the halting criterion are
proved in Lean (lean/Wave.lean: `super_run`, `superL_none_iff`, `halts_iff_pow2'`); the finer events of `step` and
the step counts are not.
"""
import sys

M = "1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB"
START = (1, 2)          # the first event, at step 17
START_STEP = 17


class Halt(Exception):
    """The wave reached the left end with c = 0: the next transitions are B0 C0 D1 E0 C0 D0.  args[0] is the number
    of steps from the event to the halt, the halting transition counted."""


def step(b, log=None):
    """The next event after block list `b`, and the number of machine steps to it.  log(i, c, t) is called each time
    the wave stands at the 0 left of a block of length c with i blocks further left (i = 0: that 0 is new tape), t
    machine steps after the event.  Raises Halt (with the steps to the halting transition) if the machine halts."""
    b = list(b)
    if b[-1] == 0:
        b.pop()
        b[-1] += 1
        b.append(2)
        return b, 17
    c = b.pop() - 1
    R = [1]                                     # the blocks right of the wave, nearest first
    t = 6 + c
    while True:
        y0 = b[-1] if b else 0
        if log:
            log(len(b), c, t)
        j = c // 2
        t += j * (2 * c + 7) - 2 * j * j          # j cycles, of 2m + 5 steps for m = c, c - 2, ...
        R[0] += j
        if c % 2 == 0:
            y = y0 + j
            if y >= 2:
                if b:
                    b.pop()
                t += y + 3
                c = y - 2
                R.insert(0, 1)
                continue
            if y == 0:
                raise Halt(t + 6)                   # B0 C0 D1 E0 C0, then the halting D0 (counted)
            if b:
                b.pop()
            b += [1, 4]
            x = R[0] - 1
            t += 19
        else:
            if b:
                b[-1] = y0 + j + 2
            else:
                b.append(j + 2)
            x = R[0] + 2
            t += 17
        rest = R[1:]
        t += x + sum(2 + r for r in rest)
        if not rest:
            b.append(x)
        else:
            b += [x + 2] + [r + 1 for r in rest[:-1]] + [rest[-1] - 1]
        return b, t


def superstep(P):
    """(P', kind, value) for the super step from [*P, 5, 0]; kind is 'turn' (value: the depth reached), 'left'
    (value: d_1), 'F' (value: d_1) or 'halt' (P' None, value: d_1)."""
    m = len(P)
    d = [0] * (m + 2)
    d[m + 1] = 20
    for l in range(m, 0, -1):
        d[l] = P[l - 1] + d[l + 1] // 2
        if d[l] % 2 and l >= 2:
            i = l
            return (list(P[:i - 2]) + [P[i - 2] + (d[i] - 1) // 2, (d[i] + 5) // 2] +
                    [d[k] // 2 for k in range(i + 1, m + 1)], "turn", m - i + 1)
    s, u = 0, d[1]
    while u % 2 == 0:
        s, u = s + 1, u // 2
    up = [d[k] // 2 for k in range(2, m + 1)]
    if u == 1:
        return None, "halt", d[1]
    if u == 3:
        return [1, 4] + [3 << t for t in range(s)] + up, "F", d[1]
    return [(u - 1) // 2, (u + 5) // 2] + [u << t for t in range(s)] + up, "left", d[1]


def big_n(P):
    """N = 10 + sum p_l 2^(m-l): the wave of the super step from P goes v2(N) + 1 blocks deep."""
    m = len(P)
    return 10 + sum(p << (m - 1 - l) for l, p in enumerate(P))


def events(k):
    """(index, step, block list) for the first k events."""
    b, t = list(START), START_STEP
    for n in range(k):
        yield n, t, b
        b, dt = step(b)
        t += dt


def left_arrivals(k):
    """(macro index, machine step, c) each time the wave reaches new tape at the left end in the first k macro
    steps.  The machine step is the one that moves the head onto the new cell (a 'L' record of tools/c/tmrun)."""
    out = []
    b, t = list(START), START_STEP
    for n in range(k):
        b, dt = step(b, lambda i, c, s: i == 0 and out.append((n, t + s, c)))
        t += dt
    return out


def main(argv):
    if len(argv) >= 2 and argv[0] == "left":
        for n, t, c in left_arrivals(int(argv[1])):
            print(n, t, c)
    elif len(argv) >= 2 and argv[0] == "super":
        P = [1, 6]
        for n in range(int(argv[1])):
            N = big_n(P)
            P2, kind, v = superstep(P)
            print(n, len(P), kind, v, N, P)
            if P2 is None:
                break
            P = P2
    else:
        print(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
