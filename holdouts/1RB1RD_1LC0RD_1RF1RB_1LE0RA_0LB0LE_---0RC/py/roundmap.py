"""The complete round map of 1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC on lists of blocks (computed, see README).

usage: python3 roundmap.py check N MAX BLOCKS [SEED]   compare the map with direct simulation (c/evc.c) on N random
                                                       lists of at most BLOCKS blocks of at most MAX ones
       python3 roundmap.py orbit K                     K rounds from blank tape with the map (big integers)

A round start is `B> 0 0 1^a 0 1^b 0 1^c ...`, the list of blocks (a, b, c, ...).  One step later the tape is the
*phase state*  P(i, x, R) = w^i C> 0 1 0 1^x 0 R  with i = 0, x = a, R = (b, c, ...) and w = 10101.  The round is a
recursion on phase states in one of two contexts: `t` (top level: blank tape left of w^i) or `d` (nested: the round
runs to the right of an even block that was rewritten as `w 0 (01)^k 0`, and its result is merged into that block).

  T1  x odd, x >= 7:   P(i, x, y:R)  ->  P(i + 1, x - 6, (y+1):R)       (a new block 1 if R is empty)
  T3  x even, x >= 2:  P(i, x, R)    ->  P(i + 1, x - 2 + B0, B')       where B0:B' = the nested round on R
                                                                        (0 and nothing if R is empty)
      except at top level with x = 2 and R = y:R':  P(i, 2, y:R') -> P(i, y + 3, R')
  ends, nested:  x = 0: 5i if R is empty, else 5i + (nested round on (y+1):R')
                 x = 1: 5i if R is empty, else (5i + y) : R'
                 x = 3: 5i : (y+1) : R'                                 (5i : 1 if R is empty)
                 x = 5: HALT if R is empty, else 5i + 7 + (nested round on (y-1):R')
  ends, top:     x = 0: 5i + 1  (R is empty here; HALT if i = 0, the tape `B> 0 0 0`)
                 x = 1: HALT if R is empty, else 5i + 2 + (top-level round on R)
                 x = 3: (5i + 6 + y) : R'                               (5i + 6 if R is empty)
                 x = 5: (5i + 6) : (y+1) : R'                           ((5i + 6) : 1 if R is empty)
"c + (round)" adds c to the first block of the round's result.  T1 and the top ends 2, 3, 5 and the halt at x = 1
are theorems in lean/Rules.lean; the nested part and the map as a whole are checked against simulation only.
"""
import os
import random
import sys
import time

sys.setrecursionlimit(1000000)
HERE = os.path.dirname(os.path.abspath(__file__))


class Halt(Exception):
    pass


def add(c, blocks):
    return [c + blocks[0]] + blocks[1:]


def phase(top, i, x, R):
    while True:
        if x % 2 == 1 and x >= 7:                      # T1, q sweeps at once
            q = x // 6
            R = [R[0] + q] + R[1:] if R else [q]
            i, x = i + q, x - 6 * q
        elif x % 2 == 0 and x >= 2:
            if top and x == 2 and R:
                x, R = R[0] + 3, R[1:]
            elif not R:                                # T3 with nothing on the right, x/2 sweeps at once
                i, x = i + x // 2, 0
            else:
                B = round_(False, R)
                i, x, R = i + 1, x - 2 + B[0], B[1:]
        else:
            break
    if not top:
        if x == 0:
            return [5 * i] if not R else add(5 * i, round_(False, [R[0] + 1] + R[1:]))
        if x == 1:
            return [5 * i] if not R else [5 * i + R[0]] + R[1:]
        if x == 3:
            return [5 * i, 1] if not R else [5 * i, R[0] + 1] + R[1:]
        if not R:
            raise Halt
        return add(5 * i + 7, round_(False, [R[0] - 1] + R[1:]))
    if x == 0:
        if i == 0:
            raise Halt
        assert not R
        return [5 * i + 1]
    if x == 1:
        if not R:
            raise Halt
        return add(5 * i + 2, round_(True, R))
    if x == 3:
        return [5 * i + 6] if not R else [5 * i + 6 + R[0]] + R[1:]
    return [5 * i + 6, 1] if not R else [5 * i + 6, R[0] + 1] + R[1:]


def round_(top, R):
    if not R:
        if top:
            raise Halt
        return [0]
    return phase(top, 0, R[0], list(R[1:]))


def next_round(blocks):
    """The next round start, a tuple of blocks, or "halt"."""
    try:
        return tuple(round_(True, list(blocks)))
    except Halt:
        return "halt"


def main(argv):
    if argv[0] == "check":
        from rounds import evc, nxt
        n, mx, nb = int(argv[1]), int(argv[2]), int(argv[3])
        random.seed(int(argv[4]) if len(argv) > 4 else 1)
        p, bad, halts = evc(), 0, 0
        for _ in range(n):
            R = [random.randint(1, mx) for _ in range(random.randint(1, nb))]
            got, want = nxt(p, R)[0], next_round(R)
            halts += want == "halt"
            if got != want:
                bad += 1
                print("mismatch", R, got, want)
        print(f"{n} random lists (at most {nb} blocks of at most {mx}): {bad} mismatches, {halts} halting")
    else:
        s, t0, multi, k = (2,), time.time(), 0, int(argv[1])
        for i in range(1, k + 1):
            s = next_round(s)
            if s == "halt":
                print(f"HALT in round {i}")
                return
            assert len(s) <= 2
            multi += len(s) == 2
            if i <= 22:
                print(i, s)
            elif i % max(1, k // 10) == 0:
                print(f"round {i}: {len(s)} block(s), first block has {s[0].bit_length()} bits; "
                      f"{multi} two-block rounds so far; {time.time() - t0:.0f} s", flush=True)
        print(f"no halt in {k} rounds")


if __name__ == "__main__":
    sys.path.insert(0, HERE)
    main(sys.argv[1:])
