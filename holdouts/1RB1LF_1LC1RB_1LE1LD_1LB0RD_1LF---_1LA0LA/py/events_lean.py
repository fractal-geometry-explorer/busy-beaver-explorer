"""Writes lean/Events.lean: hits that halt whatever the tape to their left is.

A *hit* of a word T is the head in B on the first cell of a pair X = 10 with a pair Y = 11 to its left, the word
X T ahead and blank tape after it (`Y B> X T`): that is how every visit hands its work on to the rest of the
tape. Two such hits halt for every left tape L (the head never reads L):

* hit13_halts:  L 1 1 B> 1 0 (11)^13 0^inf          (the hit of a final run of 13 Y's: an event with b = 13)
* hit800_halts: L 1 1 B> 1 0 (11)^8 1 0 1 0 0^inf   (the hit 8 0 0: the first of eight sub-visits has an event)

So any wall visit, at any depth of the recursion, that hands one of these hits on halts the machine.

And the events with a last digit b >= 11 other than 13 are ordinary hits: for b = 11, 12 and 14 to 20,

* event<b>_<x>: L x 1 1 B> 1 0 (11)^b 0^inf  reaches  L F> x <cells> 0^inf  (x = 0 or 1)

for every left tape L: the head comes back over the Y pair in F, as after every regular hit (compare turn0 /
turn1 in Rules.lean), and the word it leaves is fixed by b (events.py: the next wall visit of Y^a X Y^b is
0^a g(b)). So in the recursion these events are one more rule, h(b) = g(b).

The events with b <= 10 shift the pairs: for b = 0..10, every a = n + 1 >= 1 and every tape L,

* shift<b>: L 0^8 F> 0 (11)^(n+1) 1 0 (11)^b 0^inf  reaches  L 0 F> 0 111111 (10)^n <word of b> 0^inf

the wall visit of the word (a, b) with four blank pairs to the left of the wall ends 7 cells to the left instead of
2 (3.5 pairs: the pairs to the right are now shifted by one cell against those to the left), whatever L is.

usage: python3 events_lean.py > ../lean/Events.lean
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
from bbtools.symtm import prove, rules_file, cfg_term, Config
from bbtools.machine import Machine

M = "1RB1LF_1LC1RB_1LE1LD_1LB0RD_1LF---_1LA0LA"
NS = "H34090"
HITS = [("hit13", "1 0" + " 1 1" * 13, "the hit of a last run of 13 Y's (an event with b = 13)"),
        ("hit800", "1 0" + " 1 1" * 8 + " 1 0 1 0", "the hit 8 0 0 (the first of its eight sub-visits has an event)")]


def halting_end(cells):
    """simulate L 1 1 B> cells 0^inf until the halting read; returns (steps, end config string)"""
    m = Machine.parse(M)
    cs = [int(x) for x in cells.split()]
    tape = {-2: 1, -1: 1}
    for i, c in enumerate(cs):
        tape[i] = c
    pos, st, n = 0, 1, 0
    while True:
        assert pos >= -2, "the head reads L"
        tr = m.table[st][tape.get(pos, 0)]
        if tr is None:
            break
        tape[pos] = tr[0]; pos += tr[1]; st = tr[2]; n += 1
    hi = max(max(k for k, v in tape.items() if v), pos)
    left = " ".join(str(tape.get(p, 0)) for p in range(-2, pos))
    right = " ".join(str(tape.get(p, 0)) for p in range(pos, hi + 1))
    return n, "L %s %s> %s 0^inf" % (left, "ABCDEF"[st], right)


EVB = [11, 12, 14, 15, 16, 17, 18, 19, 20]


def return_end(b, x):
    """simulate L x 1 1 B> 1 0 (11)^b 0^inf until the head is back on the x cell; returns (steps, state, cells)"""
    m = Machine.parse(M)
    c = "10" + "11" * b
    tape = {-3: x, -2: 1, -1: 1}
    for i, ch in enumerate(c):
        tape[i] = int(ch)
    pos, st, n = 0, 1, 0
    while pos != -3:
        tr = m.table[st][tape.get(pos, 0)]
        assert tr is not None
        tape[pos] = tr[0]; pos += tr[1]; st = tr[2]; n += 1
    hi = max(k for k, v in tape.items() if v)
    return n, "ABCDEF"[st], " ".join(str(tape.get(p, 0)) for p in range(-2, hi + 1))


def shift_end(a, b):
    """the wall visit of (a, b) with 8 blank cells to the left: (steps, offset, cells right of the new wall)"""
    m = Machine.parse(M)
    c = "11" * a + "10" + "11" * b
    tape = {i + 1: int(ch) for i, ch in enumerate(c)}
    pos, st, n = 0, 5, 0
    while True:
        tr = m.table[st][tape.get(pos, 0)]
        tape[pos] = tr[0]; pos += tr[1]; st = tr[2]; n += 1
        assert pos >= -8
        if st == 5 and pos < 0 and tape.get(pos, 0) == 0 and tape.get(pos - 1, 0) == 0:
            break
    hi = max(k for k, v in tape.items() if v)
    return n, pos, "".join(str(tape.get(k, 0)) for k in range(pos + 1, hi + 1))


def main():
    thms = []
    for b in range(11):
        n1, off, s1 = shift_end(1, b)
        assert off == -7 and s1.startswith("111111")
        for a in range(2, 6):     # the shape for every a: one unit 10 more per Y of the prefix
            assert shift_end(a, b) == (n1 + 4 * (a - 1), -7, s1[:6] + "10" * (a - 1) + s1[6:])
        start = "L 0 0 0 0 0 0 0 0 F> 0 (11)^n+1 1 0%s 0^inf" % (" 1 1" * b)
        end = "L 0 F> 0 1 1 1 1 1 1 (10)^n %s 0^inf" % " ".join(s1[6:])
        t, fin = prove(M, "shift%d" % b, start, end,
                       doc="An event with last digit %d and four blank pairs left of the wall: the next wall visit is 7 "
                           "cells to the left (the pairs shifted by one cell), for every n and every tape L." % b,
                       rotate=True, count_first=True, max_seg=60)
        thms.append(t)
    for b in EVB:
        for x in (0, 1):
            n, st, rest = return_end(b, x)
            assert st == "F"
            start = "L %d 1 1 B> 1 0%s 0^inf" % (x, " 1 1" * b)
            end = "L F> %d %s 0^inf" % (x, rest)
            t, fin = prove(M, "event%d_%d" % (b, x), start, end,
                           doc="An event with last digit %d (%s to the left of the Y): an ordinary hit, back in F "
                               "over the Y after %d steps, for every tape L." % (b, "a %d" % x, n),
                           cross=False, count_first=True, max_seg=60)
            thms.append(t)
    for name, cells, what in HITS:
        n, end = halting_end(cells)
        start = "L 1 1 B> %s 0^inf" % cells
        t, fin = prove(M, name + "_run", start, end, doc="From %s, for every tape L to the left: %d steps to E on a 1."
                       % (what, n), cross=False, count_first=True, max_seg=60)
        thms.append(t)
        thms.append("/-- %s halts for every tape L to its left. -/\n"
                    "theorem %s_halts (L : Tape) : ∃ c, steps (%d) %s = some c ∧ step c = none :=\n"
                    "  ⟨_, %s_run L, rfl⟩" % (what[0].upper() + what[1:], name, n, cfg_term(Config.parse(start)), name))
    out = rules_file("Machine", NS, thms, "Hits that halt whatever the tape to their left is (the right-end events "
                     "that stop the machine). Generated by `py/events_lean.py`.")
    print(out.replace("open TM\n", "open TM\n\nset_option maxRecDepth 100000\n", 1), end="")


if __name__ == "__main__":
    main()
