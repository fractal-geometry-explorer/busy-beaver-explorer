#!/usr/bin/env python3
"""Clean-tape recurrence for the Turing machine 1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE.

A clean tape is 1 0 (10)^n 1 1: nothing but stripes and the end marker. next_clean(n) gives the n of the
next clean tape, computed round by round from the marks on the tape instead of step by step.

Coordinates: cell 0 is the leftmost 1 and the content runs to cell w-1. Each mark is named by its first cell:
  G g  gap    000 at g..g+2        M p  marker 11 at p, p+1
  W q  wall    00 at q, q+1        B r  block 111 at r..r+2
A round starts when a packet reaches the left end and opens a new gap at cell 1.

Quick cases that follow from the rules (checked for every n up to 2,000,000):
  n odd             -> n + 3
  n = 0 (mod 4)     -> n + 6
  n = 26, 38 (mod 48) -> n + 9
  n = 2 (mod 96)    -> n + 12
Every other n needs the full round-by-round calculation below.
"""

class Halt(Exception):
    """A carried packet ran into a block: the machine would halt (never seen so far)."""


def next_clean(n, max_rounds=10**6):
    w = 2 * n + 6                         # the round right after a clean tape: 1 000 (10)^n 1 1
    marks = [["G", 1], ["M", w - 2]]
    for rounds in range(1, max_rounds + 1):
        w, marks = _round(w, marks)
        if len(marks) == 2 and marks[1] == ["M", w - 2]:
            return (w - 6) // 2, rounds
    raise RuntimeError("no clean tape within max_rounds")


def _round(w, marks):
    marks = sorted(([t, p] for t, p in marks), key=lambda m: m[1])
    gap = marks[0]                        # the active gap, G 1

    def first_right(x):
        right = [m for m in marks if m[1] > x]
        return min(right, key=lambda m: m[1]) if right else None

    def shift_from(x):
        """A shift runs right from cell x to the next mark. Returns the active gap after it."""
        nonlocal w
        k = first_right(x)
        if k is None:                     # blank end: the end gains a marker, a packet comes back
            w += 2; marks.append(["M", w - 2]); return packet_back(w - 2)
        if k[0] == "M":                   # the marker is used up and a gap opens there
            k[0] = "G"; return k
        if k[0] == "W":                   # the wall becomes a block, a packet comes back
            k[0] = "B"; return packet_back(k[1])
        if k[0] == "B":                   # the block becomes a wall two cells right, a packet comes back
            k[0] = "W"; k[1] += 2; return packet_back(k[1])
        raise RuntimeError("shift into " + k[0])

    def packet_back(x):
        """A packet travels left from cell x past markers. Returns the woken gap, or None at the left end."""
        left = [m for m in marks if m[1] < x and m[0] != "M"]
        if not left:
            return None
        m = max(left, key=lambda m: m[1])
        if m[0] == "B":
            raise Halt("packet reaches block")
        if m[0] == "G":                   # a sleeping gap takes a gap step
            m[1] += 2; return m
        q = m[1]; m[0], m[1] = "M", q - 1  # a wall becomes a marker with a gap just right of it
        g = ["G", q + 1]; marks.append(g); return g

    while gap is not None:
        g = gap[1]
        m = first_right(g)
        if m is None:                     # the gap reaches the blank end
            marks.remove(gap); w += 3; marks.append(["M", w - 2])
            gap = packet_back(w - 2)
        elif m[0] == "M":                 # closing in on a marker
            d = m[1] - g - 3
            assert d >= 0 and d % 2 == 0, (d, marks)
            if d % 4 == 0:                # swap
                m[1] = g + d // 2 - 1; gap[1] = g + d // 2 + 1
            else:                         # merge into a wall
                marks.remove(gap); m[0], m[1] = "W", g + d // 2 + 3
                gap = packet_back(m[1])
        elif m[0] == "W":                 # the gap meets a wall: both go, and a shift starts
            x = m[1]; marks.remove(gap); marks.remove(m)
            gap = shift_from(x)
        elif m[0] == "B":                 # a pass reaches a block: it becomes a wall and a shift starts
            m[0], m[1] = "W", m[1] - 1    # the old gap stays, asleep
            gap = shift_from(m[1])
        else:
            raise RuntimeError("gap meets " + m[0])
        marks.sort(key=lambda k: k[1])
    # the packet reached the left end: a new round starts two cells further left
    extra = 2
    if marks and marks[0] == ["M", 0]:    # a marker on the very first cell turns into a wall
        marks[0] = ["W", 1]; extra = 4
    return w + extra, [["G", 1]] + [[t, p + extra] for t, p in marks]


# ---------------------------------------------------------------- brute-force check against the machine
RULES = {}
for s, grp in zip("ABCDEF", "1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE".split("_")):
    for y in (0, 1):
        x = grp[3 * y:3 * y + 3]
        RULES[s, y] = None if x == "---" else (int(x[0]), 1 if x[1] == "R" else -1, x[2])

def machine_next_clean(n):
    """Run the machine from the clean tape 1 0 (10)^n 1 1 (head in state C on cell 1) to the next clean tape."""
    L = 2 * n + 4
    t = {i: (1 if i % 2 == 0 else 0) if i < 2 * n + 2 else 1 for i in range(L)}
    pos, st, lo, hi, steps, side = 1, "C", 0, L - 1, 0, -1
    while True:
        r = RULES[st, t.get(pos, 0)]
        if r is None:
            return None, steps                     # halted
        t[pos] = r[0]; pos += r[1]; st = r[2]; steps += 1
        lo, hi = min(lo, pos), max(hi, pos)
        if pos <= lo + 1 and side != -1:
            side = -1
            if st == "C" and pos == lo + 1 and steps > 10:
                cells = [t.get(i, 0) for i in range(lo, hi + 1)]
                k = (len(cells) - 4) // 2
                if cells == [1, 0] * (k + 1) + [1, 1]:
                    return k, steps
        if pos >= hi - 1 and side != 1:
            side = 1


if __name__ == "__main__":
    n, seq = 2, [2]
    for _ in range(40):
        n, _r = next_clean(n); seq.append(n)
    print("clean tapes from a blank start, n =", seq)
    bad = [m for m in range(2, 300, 3) if machine_next_clean(m)[0] != next_clean(m)[0]]
    print("checked against the machine for every n = 2 (mod 3) below 300; mismatches:", bad)
